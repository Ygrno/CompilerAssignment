#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;
exception X_no_matching_param_was_found;;
exception X_param_not_bound_to_level;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

(*================= Annotate Lexical Address ========== *)
let rec get_bounding_level env variable level index = match env with
  | [] -> raise X_param_not_bound_to_level
  | first_var::rest -> if(first_var = variable) then VarBound(variable, level, index) else (get_bounding_level rest variable level (index+1));;

let rec var_is_bound curr_env variable level = match curr_env with
  | [] -> VarFree(variable)
  | head_env::rest -> try (get_bounding_level head_env variable level 0) with X_param_not_bound_to_level -> (var_is_bound rest variable (level+1))
  | _ -> VarFree(variable);;

let rec var_is_param curr_env variable index = match curr_env with
  | [] -> raise X_no_matching_param_was_found
  | first_param::rest -> if(first_param = variable) then VarParam(variable, index) else (var_is_param rest variable (index+1));;

let determine_var_type env variable = match env with
  | [] -> VarFree(variable)
  | head_env::rest -> try(var_is_param head_env variable 0) with X_no_matching_param_was_found -> (var_is_bound rest variable 0)
  | _ -> VarFree(variable);;

let extend_params_list params extension = List.rev (extension::(List.rev params));;

let rec create_lexical_env curr_env e = match e with
  | Const(value) -> Const'(value)
  | Var(variable) -> Var'(determine_var_type curr_env variable)
  | If(test, dit, dif) -> If'((create_lexical_env curr_env test), (create_lexical_env curr_env dit), (create_lexical_env curr_env dif))
  | Seq(exp_list) -> Seq'(List.map (fun item -> create_lexical_env curr_env item) exp_list)
  | Set(variable_name, value) -> Set'((create_lexical_env curr_env variable_name), (create_lexical_env curr_env value))
  | Def(variable_name, value) -> Def'((create_lexical_env curr_env variable_name), (create_lexical_env curr_env value))
  | Or(exp_list) -> Or'(List.map (fun item -> create_lexical_env curr_env item) exp_list)
  | LambdaSimple(params, body) -> LambdaSimple'(params, (create_lexical_env (params::curr_env) body))
  | LambdaOpt(params, opt_param, body) -> LambdaOpt'(params, opt_param, (create_lexical_env ((extend_params_list params opt_param)::curr_env)) body)
  | Applic(expression, args) -> Applic'(create_lexical_env curr_env expression, (List.map (fun item -> create_lexical_env curr_env item) args));;


let annotate_lexical_addresses e = match e with
  (* At this point there is an empty env, thus, if e match with var it is clearly a free var. *)
  | Var(free_var) -> Var'(VarFree(free_var))
  | _ -> create_lexical_env [] e;;

(*================= Annotate Lexical Address End ========== *)

(*================= Annotate Tail Calls ========== *)

let rec determine_tail_pos e is_lambda_body = match e with 
  | Set'(variable_name, value) -> Set'(variable_name, (no_tail_pos value))
  | LambdaSimple'(param, body) -> LambdaSimple'(param, determine_tail_pos body true)
  | LambdaOpt'(param, opt_param, body) -> LambdaOpt'(param, opt_param, determine_tail_pos body true)
  | Applic'(expression, args) -> make_tail_applic_if_lambda_body expression args is_lambda_body
  | If'(test, dit, dif) -> If'((determine_tail_pos test false), (determine_tail_pos dit is_lambda_body), (determine_tail_pos dif is_lambda_body))
  | Def'(variable_name, value)-> Def'(variable_name, (determine_tail_pos value is_lambda_body))
  | Seq'(exp_list) -> Seq'(last_exp_tail exp_list is_lambda_body)
  | Or'(exp_list) -> Or'(last_exp_tail exp_list is_lambda_body)
  | _ -> e

(* Make sure there is no tail position *)
and no_tail_pos expression = match expression with
  | Applic'(expression, args) -> Applic'((determine_tail_pos expression false), (List.map (fun item -> determine_tail_pos item false) args))
  | If'(test, dit, dif) -> If'((determine_tail_pos test false), (determine_tail_pos dit false), (determine_tail_pos dif false))
  | _ -> determine_tail_pos expression false

and last_exp_tail exp_list is_lambda_body = match exp_list with
  (* We have reahed the last exp *)
  | fisrt_exp::[] -> (determine_tail_pos fisrt_exp is_lambda_body) ::[]
  (* Keep iterating, make sure that only the last one can be in tail position *)
  | first_exp::rest -> (no_tail_pos first_exp)::(last_exp_tail rest is_lambda_body)
  | _ -> []

and make_tail_applic_if_lambda_body expression args is_lambda_body = match expression with
  | LambdaSimple'(param, body) -> if(is_lambda_body) then (ApplicTP'((determine_tail_pos expression true), args)) else Applic'((determine_tail_pos expression false), args)
  | LambdaOpt'(param, opt_param, body) -> if(is_lambda_body) then (ApplicTP'((determine_tail_pos expression true), args)) else Applic'((determine_tail_pos expression false), args)
  | _ -> if(is_lambda_body) then (ApplicTP'(expression, (List.map no_tail_pos args))) else (Applic'(expression, (List.map no_tail_pos args)));;

let annotate_tail_calls e = determine_tail_pos e false;;

(*================= Annotate Tail Calls End ========== *)

(*================= Box Set ========== *)
let param_name param = List.nth param 0;;

let var_in_list var var_list = ((List.mem ((param_name var)::["1"]) var_list) || (List.mem ((param_name var)::["0"]) var_list));;

let rec remove_duplicates_rec var_list unique_var_list = match var_list with
  | [] -> unique_var_list
  | var::rest -> if (var_in_list var unique_var_list) 
                  then (remove_duplicates_rec rest unique_var_list) 
                  else (remove_duplicates_rec rest (var::unique_var_list));;

let remove_duplicates var_list = remove_duplicates_rec var_list [];;

let extract_variable_name variable = match variable with 
  | VarBound(name, level, index) -> name
  | VarParam(name, index) -> name
  (* TODO: raise exception? *)
  | _ -> "Variable Name Not Found"

let make_param_setter param_name index = Set'(Var'(VarParam(param_name, index)), Box'(VarParam(param_name, index)));;

let should_box param = List.nth param 1 = "1";;

let rec convert_params_to_sets params index = match params with 
  | [] -> []
  | param::rest -> if(should_box param) 
                    then ((make_param_setter (param_name param) index)::(convert_params_to_sets rest (index+1))) 
                    else (convert_params_to_sets rest (index+1));;

let create_seq params body = Seq'(List.append (convert_params_to_sets params 0) [body]);; 

let rec any_param_for_boxing marked_params = match marked_params with 
  | [] -> false
  | first_param::rest -> if (should_box first_param) then true else any_param_for_boxing rest;;

let rec count_param_writing_occurrences param body count = match body with
  | Const'(value) -> []
  | Var'(variable) -> []
  | Set'(Var'(variable), value) -> List.append (if ((extract_variable_name variable) = param) then [-1] else []) 
                                               (count_param_writing_occurrences param value (count+1))
  | Applic'(expression, args) -> List.append (count_param_writing_occurrences param expression count) (map_count_writing_occurences args param count)
  | ApplicTP'(expression, args) -> List.append (count_param_writing_occurrences param expression count) (map_count_writing_occurences args param count)
  | Seq'(exp_list) -> map_count_writing_occurences exp_list param count
  | Or'(exp_list) -> map_count_writing_occurences exp_list param count
  | Def'(variable, value) -> List.append (count_param_writing_occurrences param variable count) (count_param_writing_occurrences param value count)
  | If'(test, dit, dif) -> List.append 
                            (List.append 
                                (count_param_writing_occurrences param test (count+1)) 
                                (count_param_writing_occurrences param dit (count+1))
                            ) 
                            (count_param_writing_occurrences param dif (count+1))
  (* if param is in the lambda param_list it is in a new lexical scope, so no occurrence *)
  | LambdaSimple'(p_list, b) -> if (List.mem param p_list) 
                                  then [] 
                                  else (if ((count_param_writing_occurrences param b (count+1)) = []) then [] else [count])
  (* if param is in the lambda param_list it is in a new lexical scope, so no occurrence *)
  | LambdaOpt'(p_list, opt_p, b) -> if (List.mem param (List.append p_list [opt_p]))
                                      then [] 
                                      else (if ((count_param_writing_occurrences param b (count+1)) = []) then [] else [count])
  | _ -> []
  
  and map_count_writing_occurences exp_list param count = match exp_list with
    | [] -> []
    | first_exp::rest -> List.append (count_param_writing_occurrences param first_exp count) (map_count_writing_occurences rest param (count+1));;


let rec count_param_reading_occurrences param body count = match body with
  | Const'(value) -> []
  | Var'(variable) -> if ((extract_variable_name variable) = param) then [-1] else []
  | Set'(variable, value) -> (count_param_reading_occurrences param value (count+1))
  | Applic'(expression, args) -> List.append (count_param_reading_occurrences param expression count) (map_count_reading_occurences args param count)
  | ApplicTP'(expression, args) -> List.append (count_param_reading_occurrences param expression count) (map_count_reading_occurences args param count)
  | Seq'(exp_list) -> map_count_reading_occurences exp_list param count
  | Or'(exp_list) -> map_count_reading_occurences exp_list param count
  | Def'(variable, value) -> List.append (count_param_reading_occurrences param variable count) (count_param_reading_occurrences param value count)
  | If'(test, dit, dif) -> List.append 
                            (List.append 
                                (count_param_reading_occurrences param test (count+1)) 
                                (count_param_reading_occurrences param dit (count+1))
                            ) 
                            (count_param_reading_occurrences param dif (count+1))
  (* if param is in the lambda param_list it is in a new lexical scope, so no occurrence *)
  | LambdaSimple'(p_list, b) -> if (List.mem param p_list) 
                                  then [] 
                                  else (if ((count_param_reading_occurrences param b (count+1)) = []) then [] else [count])
  (* if param is in the lambda param_list it is in a new lexical scope, so no occurrence *)
  | LambdaOpt'(p_list, opt_p, b) -> if (List.mem param (List.append p_list [opt_p]))
                                      then [] 
                                      else (if ((count_param_reading_occurrences param b (count+1)) = []) then [] else [count])
  | _ -> []

  and map_count_reading_occurences exp_list param count = match exp_list with
    | [] -> []
    | first_exp::rest -> List.append (count_param_reading_occurrences param first_exp count) (map_count_reading_occurences rest param (count+1));;

let match_write_occurance_with_read_occurances write_occur read_occurances = 
  List.fold_left (fun matched read_occur -> (matched || (write_occur != read_occur))) false read_occurances;;

let rec boxing_criterias_are_met read_occurances write_occurances = match write_occurances with 
  | [] -> "0"
  | write_occur::rest -> if(match_write_occurance_with_read_occurances write_occur read_occurances) 
                          then "1" 
                          else (boxing_criterias_are_met read_occurances rest);;

let mark_param_for_boxing param body = 
  let reading_occurences = count_param_reading_occurrences param body 0 in
  let writing_occurences = count_param_writing_occurrences param body 0 in
  let marked_param = param::[boxing_criterias_are_met reading_occurences writing_occurences] in
  marked_param;;

let check_each_param_for_boxing params body = List.map (fun param -> mark_param_for_boxing param body) params;;

(* Return true if the givene variable is in the var list *)
let var_found_in_list variable var_list = List.mem ((extract_variable_name variable)::["1"]) var_list;;

let rec determine_boxing exp_for_check var_list = match exp_for_check with
  | Set'(Var'(variable), value) -> if (var_found_in_list variable var_list) 
                                      then BoxSet'(variable, (determine_boxing value var_list)) 
                                      else Set'(Var'(variable), (determine_boxing value var_list))
  | Var'(variable) -> if (var_found_in_list variable var_list) then BoxGet'(variable) else exp_for_check
  | LambdaSimple'(params, body) -> LambdaSimple'(params, (check_body_for_boxing body params var_list))
  | LambdaOpt'(params, opt_param, body) -> LambdaOpt'(params, opt_param, (check_body_for_boxing body (List.append params [opt_param]) var_list))
  | Applic'(expression, args) -> Applic'((determine_boxing expression var_list), (determine_boxing_list args var_list))
  | ApplicTP'(expression, args) -> ApplicTP'((determine_boxing expression var_list), (determine_boxing_list args var_list))
  | If'(test, dit, dif) -> If'((determine_boxing test var_list), (determine_boxing dit var_list), (determine_boxing dif var_list))
  | Def'(variable, value) -> Def'(variable, (determine_boxing value var_list))
  | Seq'(exp_list) -> Seq'(determine_boxing_list exp_list var_list)
  | Or'(exp_list) -> Or'(determine_boxing_list exp_list var_list)
  | _ -> exp_for_check

(* Map determine_boxing on every list element *)
and determine_boxing_list exp_list var_list = List.map (fun item -> determine_boxing item var_list) exp_list

and check_body_for_boxing body params var_list = 
  let marked_params_for_boxing = check_each_param_for_boxing params body in
  let merged_var_list = remove_duplicates (List.append marked_params_for_boxing var_list) in
  let boxed_body = determine_boxing body merged_var_list in
  if (any_param_for_boxing marked_params_for_boxing) then (create_seq marked_params_for_boxing boxed_body) else boxed_body;;

let box_set e = determine_boxing e [];;

(*================= Box Set End========== *)

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)

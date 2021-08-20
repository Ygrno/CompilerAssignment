#use "semantic-analyser.ml";;
(* open Assistance;; *)

exception X_not_a_compound_sexpr;;
exception X_tag_definition_not_found;;

let lambda_depth = (ref 0);; 
let label_count = (ref 0);;
let tag_defs = (ref []);;

(* TODO: maybe there's a need to add sort kind of tag-expression support in the table ?  *)
let init_fvars_table = 
  [
   "null?"; "char?"; "string?";
   "procedure?"; "symbol?"; "string-length";
   "string-ref"; "string-set!"; "make-string";
   "boolean?"; "float?"; "integer?"; "pair?"; "symbol->string"; 
   "apply"; "car"; "cdr"; "cons"; "set-car!"; "set-cdr!";
   "char->integer"; "integer->char"; "eq?";
   "+"; "*"; "-"; "/"; "<"; "=";   
  ];;

(* ========== Constants Table =========== *)
let builtins_consts = [Void;Sexpr(Nil);Sexpr(Bool(false));Sexpr(Bool(true))];;

let rec sexpr_in_lst expression lst = match lst with
  | [] -> false
  | Sexpr(curr_sexpr)::rest -> (sexpr_eq curr_sexpr expression) || (sexpr_in_lst expression rest)
  | curr_sexpr::rest -> (compare curr_sexpr (Sexpr expression)) == 0  || (sexpr_in_lst expression rest) ;;

let rec remove_dup_sexprs_rec lst uniqe_lst = match lst with 
  | [] -> uniqe_lst
  | Sexpr(curr_sexpr)::rest -> if (sexpr_in_lst curr_sexpr uniqe_lst) 
                                  then (remove_dup_sexprs_rec rest uniqe_lst) 
                                  else (remove_dup_sexprs_rec rest (uniqe_lst @ [Sexpr(curr_sexpr)]))
  | curr_sexpr::rest -> if (List.mem curr_sexpr uniqe_lst) 
                  then (remove_dup_sexprs_rec rest uniqe_lst) 
                  else (remove_dup_sexprs_rec rest (uniqe_lst @ [curr_sexpr]));;

let remove_dup_sexprs sexp_lst = remove_dup_sexprs_rec sexp_lst [];;

let rec find_const_offset expression const_lst = match const_lst with
| (Void,(offset,_))::rest -> find_const_offset expression rest
| (Sexpr(some_expr), (offset,_))::rest -> if (sexpr_eq some_expr expression) then offset else (find_const_offset expression rest)
(* TODO: magic number? *)
| [] -> 123456789;;

(* TODO: change .... *)
let rec convert_str_to_ch_lst_rec str indx ch_lst = 
  if(indx = 0) then (str.[0]::ch_lst)
            else convert_str_to_ch_lst_rec str (indx-1) (str.[indx]::ch_lst);;
let convert_str_to_ch_lst str = convert_str_to_ch_lst_rec str ((String.length str)-1) [];;

let change_str_format str = String.concat "," (List.map string_of_int (List.map Char.code (convert_str_to_ch_lst str)));; 

let get_const_asm_code expression const_lst = match expression with
  | Sexpr(Nil) -> "N_M"
  | Sexpr(Bool(boolean)) -> if boolean then "B_M(1)" else "B_M(0)"
  | Sexpr(String(str)) -> String.concat "" ["STRING_L_M ";(change_str_format str)]
  | Sexpr(Number(Int(number))) -> String.concat "" ["L_I_M(" ; string_of_int number ; ")"]
  | Sexpr(Number(Float(number))) -> String.concat "" ["L_F_M(" ; string_of_float number; ")"]
  | Sexpr(Char(c)) -> String.concat "" ["L_C_M(" ; string_of_int (int_of_char c) ; ")"]
  | Sexpr(Pair(car, cdr)) -> String.concat "" ["MAKE_LITERAL_PAIR(const_tbl+" ; string_of_int (find_const_offset car const_lst) ; 
                                                            ", " ; "const_tbl+" ; string_of_int (find_const_offset cdr const_lst) ; ")"]
  | Sexpr(Symbol(sym)) -> String.concat "" ["L_S_M(const_tbl+" ; string_of_int (find_const_offset (String sym) const_lst) ; ")"]
  | _ -> "V_M";;

(* Sizes are calculated as follows: Length Bytes + Tag Size==1 Byte *)
let sizeof expression = match expression with
  | Sexpr(Nil) -> 1
  | Sexpr(Bool(boolean)) -> 2
  | Sexpr(Char(c)) -> 2
  | Sexpr(Number(number)) -> 9
  | Sexpr(Symbol(sym)) -> 9
  | Sexpr(String(str)) -> 9 + (String.length str)  
  | Sexpr(Pair(car,cdr)) -> 17
  | _ -> 1

let rec calc_constant_offset calc_list = match calc_list with 
(* Empty table *)
| [] -> 0 
(* Single element *)
| [(expression, (offset, _))] -> offset + (sizeof expression)
| const::rest -> calc_constant_offset rest;;

let get_const_from_sexpr e = match e with
  | TaggedSexpr(name, value) -> (tag_defs := (name, value)::!tag_defs); [Sexpr(value)]
  | TagRef(name) -> []
  | _ -> [Sexpr(e)];;

let rec get_const_lst_from_ast ast = match ast with  
  (* Ignore TagRef at first *)
  | Const'(Sexpr(TagRef(name))) -> [] 
  | Const'(Sexpr(TaggedSexpr(name, value))) -> (tag_defs := (name, value)::!tag_defs); Sexpr(value)::[]
  (* | Const'(Sexpr(Pair(a,b)))-> (get_const_from_sexpr a) @ (get_const_from_sexpr b) *)
  | Const'(const) -> const::[]
  | BoxSet'(var, boxing) -> get_const_lst_from_ast boxing
  | If'(test, dit, dif) -> (get_const_lst_from_ast test) @ (get_const_lst_from_ast dit) @ (get_const_lst_from_ast dif)
  | Seq'(expr_lst) -> get_const_lst_from_expr_lst expr_lst
  | Set'(var_name, value) -> (get_const_lst_from_ast var_name) @ (get_const_lst_from_ast value)
  | Def'(var_name, value) -> (get_const_lst_from_ast var_name) @ (get_const_lst_from_ast value)
  | Or'(expr_lst) ->   get_const_lst_from_expr_lst expr_lst
  | LambdaSimple'(params, body) -> get_const_lst_from_ast body
  | LambdaOpt'(params, opt_param, body) -> get_const_lst_from_ast body
  | Applic'(expression, args) -> (get_const_lst_from_ast expression) @ (get_const_lst_from_expr_lst args)
  | ApplicTP'(expression, args) -> (get_const_lst_from_ast expression) @ (get_const_lst_from_expr_lst args)
  | _ -> []

  and  get_const_lst_from_expr_lst lst = 
   List.fold_left (fun first_lst sec_lst -> first_lst @ sec_lst) [] (List.map get_const_lst_from_ast lst);;

let is_comppound_expr expression = match expression with
  | Sexpr(Pair(car, cdr)) -> true
  | Sexpr(Symbol(sym)) -> true
  | _ -> false;;

let rec get_const_lst_from_expr e = remove_dup_sexprs (builtins_consts@(remove_dup_sexprs (expand_comppound_consts (remove_dup_sexprs (get_const_lst_from_ast e)))))

  and expand_pair pair =  match pair with 
    | Pair(car, cdr) -> (get_const_lst_from_expr ((Const'(Sexpr(car))))) @ (get_const_lst_from_expr ((Const'(Sexpr(cdr)))))
    | _ ->  get_const_lst_from_expr (Const'(Sexpr(pair)))  

  and expand_comppound_expr expression = match expression with
    | Sexpr(Pair(car, cdr)) -> expand_pair (Pair(car,cdr))
    | Sexpr(Symbol(sym)) -> (get_const_lst_from_expr (Const'(Sexpr(((String(sym))))))) @ [expression]
    (* TODO: should raise different expception? *)    
    | _ -> raise X_not_a_compound_sexpr

  and expand_comppound_consts lst = match lst with 
    | [] -> lst
    | const::rest -> if (is_comppound_expr const) 
                        then (expand_comppound_expr const) @ [const] @ (expand_comppound_consts rest)  
                        else (const::(expand_comppound_consts rest));;

let rec get_init_const_list asts = remove_dup_sexprs (List.flatten (List.map get_const_lst_from_ast asts));;

let get_const_list asts = remove_dup_sexprs (expand_comppound_consts (get_init_const_list asts));;

let get_concat_const_lst asts = remove_dup_sexprs (builtins_consts@(get_const_list asts));;                       

let make_const_element expression const_lst = (
                                                expression, 
                                                ((calc_constant_offset const_lst), (get_const_asm_code expression const_lst))
                                              );;

let rec accumolate_consts_code const_lst acc = match const_lst with
  | [] -> acc
  | const::rest -> (accumolate_consts_code rest (acc @ [make_const_element const acc]));;

let get_new_tag_name name count = Printf.sprintf "%s%d" name count;; 

let rec add_enumeration_to_tags e count = match e with
  | TaggedSexpr(name, value) -> TaggedSexpr((get_new_tag_name name count), add_enumeration_to_tags value count)
  | TagRef(name) -> TagRef(get_new_tag_name name count)
  | Pair(a,b) -> Pair(add_enumeration_to_tags a count, add_enumeration_to_tags b count)  
  | _ -> e;;

let rec enumerate_tags ast count = match ast with
  | Const'(Sexpr(const)) -> Const'(Sexpr(add_enumeration_to_tags const count))
  | BoxSet'(var, boxing) -> BoxSet'(var, (enumerate_tags boxing count))
  | If'(test, dit, dif) -> If'((enumerate_tags test count), (enumerate_tags dit count), (enumerate_tags dif count))
  | Seq'(expr_lst) -> Seq'(List.map (fun e -> enumerate_tags e count) expr_lst)
  | Set'(var_name, value) -> Set'(var_name, enumerate_tags value count)
  | Def'(var_name, value) -> Def'(var_name, enumerate_tags value count)
  | Or'(expr_lst) -> Or'(List.map (fun e -> enumerate_tags e count) expr_lst)
  | LambdaSimple'(params, body) -> LambdaSimple'(params, enumerate_tags body count)
  | LambdaOpt'(params, opt_param, body) -> LambdaOpt'(params, opt_param, enumerate_tags body count)
  | Applic'(expression, args) -> Applic'(enumerate_tags expression count, List.map (fun e -> enumerate_tags e count)  args)
  | ApplicTP'(expression, args) -> ApplicTP'(enumerate_tags expression count, List.map (fun e -> enumerate_tags e count)  args)
  | _ -> ast;;

 
let rec get_const_from_tag_defs const_name tags = match tags with 
| (name,const)::rest -> if (compare const_name name) == 0 then const else (get_const_from_tag_defs const_name rest)
| _ -> raise X_tag_definition_not_found;;

(* let return_tag_address name const_tbl= 
  let const = get_const_from_tag_defs name (!tag_defs) in  
  get_const_address const const_tbl;; *)

let rec get_constant_sexpr e = match e with 
  | TaggedSexpr(name, value) -> value
  | TagRef(name) -> get_const_from_tag_defs name (!tag_defs)
  | Pair(TagRef(name), b) -> Pair(get_const_from_tag_defs name (!tag_defs), get_constant_sexpr b)
  | Pair(a, TagRef(name)) -> Pair(get_constant_sexpr a, get_const_from_tag_defs name (!tag_defs))
  | Pair(a, b) -> Pair(handle_pair a, handle_pair b)
  | _ -> e
  and handle_pair e = match e with 
  | TaggedSexpr(name, value) -> value
  | _ -> e;;

let rec search e = match e with 
  | Sexpr(c) -> Sexpr(get_constant_sexpr c)
  | _ -> e;;

let create_new_row expression offset const_tbl =
  let new_expr = search expression in
  (expression, (offset, get_const_asm_code new_expr const_tbl));;

let create_consts_table asts =   
  let tmp_const_tbl = accumolate_consts_code (get_concat_const_lst asts) [] in
  List.map (fun (expression, (offset, str)) -> create_new_row expression offset tmp_const_tbl) tmp_const_tbl;;

(* ============ End of consts table =============== *)

  (*FVAR TABLE*)

  (* This function recives an expr', extracting free varibale and returns it's name as a string *)
  let rec find_fvar_in_expr'_return_string ex' = match ex' with
| Var'(VarFree(str)) -> [str]
| Applic'(expr',ls) -> (find_fvar_in_expr'_return_string expr') @ (List.fold_left (fun a b -> a @ b) [] (List.map find_fvar_in_expr'_return_string ls))
| ApplicTP'(expr',ls) -> (find_fvar_in_expr'_return_string expr') @ (List.fold_left (fun a b -> a @ b) [] (List.map find_fvar_in_expr'_return_string ls))
| Def'(expr'1,expr'2) -> (find_fvar_in_expr'_return_string expr'1) @ (find_fvar_in_expr'_return_string expr'2)
| Or'(ls) -> (List.fold_left (fun a b -> a @ b) [] (List.map find_fvar_in_expr'_return_string ls))
| LambdaSimple'(param,body) -> (find_fvar_in_expr'_return_string body)
| BoxSet'(var, expr') -> (find_fvar_in_expr'_return_string expr')
| If'(test, dit, dif) -> (find_fvar_in_expr'_return_string test) @ (find_fvar_in_expr'_return_string dit) @ (find_fvar_in_expr'_return_string dif)
| Seq'(ls) -> (List.fold_left (fun a b -> a @ b) [] (List.map find_fvar_in_expr'_return_string ls))
| Set'(expr'1,expr'2) -> (find_fvar_in_expr'_return_string expr'1) @ (find_fvar_in_expr'_return_string expr'2)
| LambdaOpt'(param,lastp,body) -> (find_fvar_in_expr'_return_string body)
| _ -> [];;

(* There's no need of duplicates in the free variables table, the following lines deals with removing the duplicates from the table*)
let rec duplicate_remover_assist l new_l = match l with
| [] -> new_l
| head :: tail -> if(List.mem head new_l) then (duplicate_remover_assist tail new_l) else (duplicate_remover_assist tail (new_l @ [head]));;
let duplicates_remover_from_list l = duplicate_remover_assist l [];;


(* recieves a table of free variables that contains only strings, then adds numeration ["a","b"] => [("a",0) , ("b",1)]  *)
let rec numerate_assit l counter = match l with
| [] -> []
| head :: tl -> [(head, counter)] @ (numerate_assit tl (counter+1));;
let numerate_fvars_table l = (numerate_assit l 0);;

(* let fvar_list e = str_to_fvar_list (remove_dup (collect_fvar e));; *)
let create_fvars_table asts = numerate_fvars_table (duplicates_remover_from_list (init_fvars_table @ List.flatten (List.map find_fvar_in_expr'_return_string asts)));;

(* ============ End of fvar table =============== *)

(* ========== Code Generator ========== *)

let unwrap_sexpr expression = match expression with
  | Sexpr(x) -> x
  | Void -> Number(Int(1));;

let const_comparer const curr_const =   
  (const == curr_const) || ((curr_const != Void) && (sexpr_eq (unwrap_sexpr const) (unwrap_sexpr curr_const)));;

let extract_offset_from_const tbl_row = match tbl_row with | (_, (offset, _)) -> offset;;
let exrtract_index_from_fvar tbl_row = match tbl_row with | (_,index) -> index;;

let get_const_address const const_tbl = 
  let row = List.find (fun (curr_const, (_, _)) -> (const_comparer const curr_const)) const_tbl in
  let offset = extract_offset_from_const row in
  "const_tbl+"^(string_of_int offset);;

let get_fvar_index var fvars =
  let row = List.find (fun (name, _) -> (compare var name == 0)) fvars in
  let index = exrtract_index_from_fvar row in
  index;;

let to_string format param = Printf.sprintf format param;;

let rec generate_code consts fvars e = match e with 
  | Const'(Sexpr(TaggedSexpr(name, value))) -> to_string ("mov rax, %s ; Const") (get_const_address (Sexpr(value)) consts)
  | Const'(Sexpr(TagRef(name))) -> to_string ("mov rax, %s ; Const") (get_const_address (Sexpr(get_const_from_tag_defs name (!tag_defs))) consts)
  
  | Const'(const) -> to_string ("mov rax, %s ; Const") (get_const_address const consts)
  | Var'(VarParam(_, minor)) -> to_string ("mov rax, qword [rbp + 8 * (4 + %d)] ; VarParam") minor
  | Set'(Var'(VarParam(_, minor)), value) ->  String.concat "\n" ["; Set VarParam Start" ;
                                                                  (generate_code consts fvars value) ; 
                                                                   to_string ("mov qword [rbp + 8 * (4 + %d)], rax") minor ; 
                                                                   "mov rax, SOB_VOID_ADDRESS" ;
                                                                   "; Set VarParam End\n"] 
  | Var'(VarBound(_, major, minor)) -> String.concat "\n" ["; VarBound Start" ;
                                                          "mov rax, qword [rbp + 8 * 2]" ;
                                                           to_string ("mov rax, qword [rax + 8 * %d]") major ;
                                                           to_string ("mov rax, qword [rax + 8 * %d]") minor ;
                                                           "; VarBound End\n"]
  | Set'(Var'(VarBound(_, major, minor)), value) -> String.concat "\n" ["; Set VarBound Start";
                                                                        (generate_code consts fvars value) ;
                                                                        "mov rbx, qword [rbp + 8 * 2]" ; 
                                                                        to_string ("mov rbx, qword [rbx + 8 * %d]") major ;
                                                                        to_string ("mov qword [rbx + 8 * %d], rax") minor ;
                                                                        "mov rax, SOB_VOID_ADDRESS" ;
                                                                        "; Set VarBound End\n"]  
  | Var'(VarFree(variable)) -> to_string ("mov rax, qword [fvar_tbl + WORD_SIZE * (%d)] ; VarFree") (get_fvar_index variable fvars)  
  | Set'(Var'(VarFree(variable)), value) -> String.concat "\n" [to_string "; Set VarFree - %s - Start" variable;                                                                
                                                                (generate_code consts fvars value) ;
                                                                to_string ("mov qword [fvar_tbl + WORD_SIZE * (%d)], rax") (get_fvar_index variable fvars) ; 
                                                                "mov rax, SOB_VOID_ADDRESS" ;
                                                                "; Set VarFree End\n"]
  | Def'(Var'(VarFree(variable)), value) -> String.concat "\n" ["; Define Start" ;
                                                                (generate_code consts fvars value); 
                                                                to_string ("mov [fvar_tbl + WORD_SIZE * (%d)], rax") (get_fvar_index variable fvars);
                                                                "mov rax, SOB_VOID_ADDRESS" ;
                                                                "; Define End\n" ;]
  | Seq'(expr_lst) -> String.concat "\n" (List.map (generate_code consts fvars) expr_lst)
  | Or'(expr_lst) ->  (incr label_count);or_format consts fvars expr_lst (!label_count)
  | If'(test,dit,dif) -> (incr label_count); let count = !label_count in String.concat "\n" ["; If Start" ;
                                                                                             "; Test Code Start" ;
                                                                                             (generate_code consts fvars test) ;
                                                                                             "; Test Code End - Cont If" ;
                                                                                             "cmp rax, SOB_FALSE_ADDRESS" ;
                                                                                             to_string ("je Lelse%d") count;
                                                                                             "; Then Code Start" ;
                                                                                             (generate_code consts fvars dit) ;
                                                                                             "; Then Code End - Cont If" ;
                                                                                             to_string ("jmp Lexit%d") count ; 
                                                                                             to_string ("Lelse%d:") count ;
                                                                                             "; Else Code Start" ;
                                                                                             (generate_code consts fvars dif) ; 
                                                                                             "; Else Code End - Cont If" ;
                                                                                             to_string ("Lexit%d:") count ;
                                                                                             "; If End\n" ;]
  | BoxGet'(variable) -> String.concat "\n" ["; BoxGet Start"; (generate_code consts fvars (Var'(variable)));"mov rax, qword [rax]"; "; BoxGet End\n"]
  | BoxSet'(variable, value) -> String.concat "\n" ["; BoxSet Start" ;
                                                    (generate_code consts fvars value) ;
                                                    "push rax" ; 
                                                    (generate_code consts fvars (Var'(variable))) ; 
                                                    "pop qword [rax]" ; 
                                                    "mov rax, SOB_VOID_ADDRESS" ;
                                                    "; BoxSet End\n" ;]
  | Box'(variable) -> String.concat "\n" ["; Box Start"; "MALLOC rbx, 8";(generate_code consts fvars (Var'(variable)));"mov qword [rbx], rax";"mov rax, rbx";"; Box End\n"]
  | LambdaSimple'(params, body) -> (incr label_count);(incr lambda_depth);(lambda_format consts fvars params body !label_count !lambda_depth)
  | LambdaOpt'(params, opt_param, body) -> (incr label_count);(incr lambda_depth);(lambda_opt_format consts fvars params opt_param body !label_count !lambda_depth)
  | Applic'(expression, args) -> String.concat "\n" ["; Applic Start" ;
                                                     "push 7 ; magic number" ;
                                                     (push_applic_args consts fvars args) ;
                                                     "; Applic Code Start" ;
                                                     (generate_code consts fvars expression) ;
                                                     "; Applic Code End - Continue Applic" ;
                                                     "CLOSURE_ENV rsi,rax" ;                                                     
                                                     "push rsi" ; (* env *)
                                                     "CLOSURE_CODE rsi, rax" ;
                                                     "call rsi" ; (* code *)
                                                     "add rsp, 8*1 ; pop env" ; (* pop env *)
                                                     "pop rbx" ; (* pop args count *)                                                     
                                                     "inc rbx ; add the magic num as arg" ;
                                                     "shl rbx, 3" ; (* rbx = rbx * 8 *)
                                                     "add rsp, rbx"; 
                                                     "; Applic End\n"] (* pop args *)
  | ApplicTP'(expression, args) -> String.concat "\n" ["; ApplicTP Start" ;
                                                       "push 7 ; magic number" ;
                                                       (push_applic_args consts fvars args);
                                                       "; ApplicTP Code Start" ;
                                                       (generate_code consts fvars expression) ;
                                                       "; ApplicTP Code End - Continue ApplicTP" ;
                                                       "CLOSURE_ENV rsi,rax" ;                                                     
                                                       "push rsi" ; (* env *)
                                                       "mov rsi,qword [rbp + 8]" ;
                                                       "push rsi" ;
                                                       to_string "mov rsi, %d" (4+(List.length args)) ;
                                                       "mov r13, qword [rbp]" ;
                                                       "F_R_S rsi" ;
                                                       "mov rbp, r13" ;
                                                       "CLOSURE_CODE rsi, rax" ;
                                                       "jmp rsi" ; (* code *)
                                                       "; ApplicTP End\n"]
                                                       
  | _ -> "; NOT_FOUND"

  and or_format consts fvars expr_lst count = match expr_lst with 
    | [expression] -> (generate_code consts fvars expression)^(to_string ("\nLexit%d:\n") count)
    (* TODO: raise? Should return false ? Lexit?*)
    | [] -> (to_string ("\nLexit%d:\n") count)
    | expression::rest -> (generate_code consts fvars expression)^
                          (to_string ("\ncmp rax, SOB_FALSE_ADDRESS\njne Lexit%d\n") count)^
                          (or_format consts fvars rest count)

  and push_applic_args consts fvars args = 
    let n = List.length args in
    let pushed_args = List.fold_right (fun arg acc -> acc^
                                                      "\n; Pushing Applic Arg\n"^
                                                      (generate_code consts fvars arg)^
                                                      "\npush rax\n"^
                                                      "; End Pushing Arg\n") args "" in

    String.concat "\n" [pushed_args;(to_string "push %d ; Number of arguments Pushed" n)]

  and lambda_format consts fvars params body label_c lambda_d = 
    let lambda_label = to_string "Lambda_%d" label_c in
    let lambda_start_label = to_string "Lambda_Code_%d" label_c in
    let lambda_end_label = to_string "End_Lambda_Code_%d" label_c in
    String.concat "\n" ["; Lambda Start";
                        (* Extend Env *)
                        lambda_label^":" ;
                        "mov rsi, qword [rbp+3*WORD_SIZE]";
                        to_string "EXTENV rsi, %d" (lambda_d-1);
                        (* Make Closure (Alocate + Set) *)
                        to_string "MAKE_CLOSURE(rax, rbx, %s)" lambda_start_label ;
                        to_string "jmp %s" lambda_end_label ;
                        (* Body *)
                        lambda_start_label^":" ;
                        "push rbp" ; 
                        "mov rbp, rsp" ;      
                        to_string "mov rax, %d" (List.length params);                  
                        "; Body Code Start" ;
                        (generate_code consts fvars body) ;
                        "; Body Code End" ;
                        "leave" ;
                        "ret" ;
                        lambda_end_label^":";
                        "; Lambda End\n" ;
                        ]
  and lambda_opt_format consts fvars params opt_param body label_c lambda_d =   
    let lambda_label = to_string "LambdaOpt_%d" label_c in 
    let lambda_start_label = to_string "Lambda_Code_Opt_%d" label_c in
    let lambda_end_label = to_string "End_Lambda_Code_Opt_%d" label_c in
    let lambda_error_label = to_string "Lambda_Opt_Error_%d" label_c in
    let params_len = List.length params in
    String.concat "\n" ["; LambdaOpt Start";                                  
                        lambda_label^":" ;
                        (* Extend Env *)
                        "mov rsi,qword [rbp+3*WORD_SIZE]";
                        to_string "EXTENV rsi, %d" (lambda_d-1);
                        (* Make Closure (Alocate + Set) *)
                        to_string "MAKE_CLOSURE(rax, rbx, %s)" lambda_start_label ;
                        to_string "jmp %s" lambda_end_label ;
                        (* Body *)                        
                        lambda_start_label^":" ;
                        "push rbp";
                        "mov rbp, rsp";
                        (* Lambda Opt *)
                        to_string "mov rax, %d" params_len;
                        "cmp rax, C_P";
                        to_string "jg %s" lambda_error_label;
                        (* "creating the optional args list" *)
                        "mov rax,C_P";
                        "mov r8,rax";
                        "dec r8";
                        to_string "sub rax, %d" params_len;
                        "imul rax , WORD_SIZE";
                        (* fff *)
                        "mov rbx,const_tbl + 1 ; initial optional args list with sob_nil";
                        "cmp rax, 0";
                        "mov rax,C_P";
                        to_string "sub rax, %d" params_len;
                        "cmp rax, 0 ; if no opt args, skip";
                        to_string "je end_of_loop_%d" label_c;
                        "dec rax";
                        to_string "opt_loop_%d:" label_c;
                          "mov r13, PVAR(r8)";
                          "mov r12,rbx";
                          "MAKE_PAIR(rbx,r13,r12)";
                          "dec r8";
                          "dec rax";
                          "cmp rax, 0";
                          to_string "jge opt_loop_%d" label_c;
                        to_string "end_of_loop_%d:" label_c;
                        "mov rax,C_P";
                        (* rax <- number of opt args *)
                        to_string "sub rax, %d" params_len ;
                        "mov r15, rax";
                        "S_F_U r15";
                        to_string "mov qword [rbp + WORD_SIZE*(4 + %d)],rbx" params_len;
                        to_string "mov rax, %d" params_len;
                        (* if i have 0 optional args, then ovveride magic *)
                        "cmp r15,0"; 
                        to_string "je not_adding_%d" label_c;
                        "inc rax";
                        to_string "not_adding_%d:" label_c;
                        "mov qword [rbp + 3*WORD_SIZE], rax";                        
                        (* Generate Body Code *)
                        "; Body Code Start" ;
                        (generate_code consts fvars body) ;
                        "; Body Code End" ;
                        "leave" ;
                        "ret" ;
                        (* Lambda Error *)
                        lambda_error_label^":";
                        "mov rbx, 555";
                        lambda_end_label^":";
                        "; LambdaOpt End\n" ;
                       ]
  ;;
                      

(* ========== End Code Generator ========== *)

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "SOB_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* This signature represents the idea of outputing assembly code as a string
     for a single AST', given the full constants and fvars tables. 
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct
  let make_fvars_tbl asts = create_fvars_table asts;;
  let make_consts_tbl asts = (tag_defs := []); create_consts_table asts;;  
  let generate consts fvars e = (lambda_depth := 0); generate_code consts fvars e;;
end;;

#use "reader.ml";;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                          (expr_eq th1 th2) &&
                                          (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                           (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
    (List.for_all2 String.equal vars1 vars2) &&
    (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
    (String.equal var1 var2) &&
    (List.for_all2 String.equal vars1 vars2) &&
    (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
    (expr_eq e1 e2) &&
    (List.for_all2 expr_eq args1 args2)
  | _ -> false;;



  

exception X_syntax_error;;



  (* ---------------------------------------------------------------------------------------------------------------------- *)
  (* Assistance Functions *)
  (* ---------------------------------------------------------------------------------------------------------------------- *)
  let reserved_word_list =
    ["and"; "begin"; "cond"; "define"; "else";
     "if"; "lambda"; "let"; "let*"; "letrec"; "or";
     "quasiquote"; "quote"; "set!"; "unquote";
     "unquote-splicing"];;  
  
  (* Gets a list and a word. returns true if the word in the list, false otherwise *)
  let check_word_in_list l word = List.fold_left (fun acc i-> (((String.equal word i) || acc))) false l
  (* Gets a word, returns true if the word is in the reserved words list, false otherwise *)
  let check_reserved_word word = check_word_in_list reserved_word_list word;;
  (* Gets a word returns the word if it's legal (not reserved) otherwise raise error   *)
  let legal_symb_validation x = if(check_reserved_word x) then (raise X_syntax_error) else x;;

  (* Gets a list of arguments of lambda, returns true if it's a simple one *)
  let rec check_lambda_is_simple args =
    match args with 
    | Symbol(str) -> false
    | Nil -> true
    | Pair(Symbol(str),rest) -> check_lambda_is_simple rest
    | _ -> raise X_syntax_error;;

  (* Gets a sexpr and a predefined list, dismantling the symbols in the sexpr into list of strings while checking they are not in the predefined list nor repeating
     example - (lambda (x x) x) is syntax error cause can't be same variable twice *)
  let rec dismantle_sexpr_to_string_list sexpr l= 
    match sexpr with
    | Nil -> []
    | Pair(Symbol(str),rest) -> if(check_word_in_list l str) then (raise X_syntax_error) else ( (legal_symb_validation str)::(dismantle_sexpr_to_string_list rest (str::l)) )
    | Symbol(str) -> if(check_word_in_list l str) then (raise X_syntax_error) else []
    | _ -> [];;

  (* Gets a sexpr that represent a code_segment like a body on a function dismantling it to a list of all the sexprs it contains *)
  let rec dismantle_to_sexpr_list code_segment_sexpr =
    match code_segment_sexpr with
    | Pair(a,b) -> a::(dismantle_to_sexpr_list b)
    | Nil -> []
    | _-> raise X_syntax_error;;

  (* Gets a sexpr (that probebly represents arguments of a function), returns the last argument*)
  let rec last_sym sexpr =
    match sexpr with
    | Symbol(str) -> str
    | Pair(str,rest) -> last_sym rest
    | _ -> "";;

  (* get an expr type, returns true if it's Var *)
  let check_var expr = match expr with
    | Var(_) -> expr
    | _ -> raise X_syntax_error;;

(* Get flat list of first argument from each pair in list*)
    let rec flat_params_names local_vars = match local_vars with
    | Nil -> Nil
    | Pair(Pair(name, value), rest_list) -> Pair(name, flat_params_names rest_list)
    | _ -> local_vars;;

(* Get flat list of second argument from each pair in list*)
    let rec flat_params_values local_vars = match local_vars with
    | Nil -> Nil
    | Pair(Pair(name, Pair(value, Nil)), rest_list) -> Pair(value, flat_params_values rest_list)
    | _ -> local_vars;;

    let rec attach_whatever_to_var local_vars = match local_vars with
    | Nil -> Nil
    | Pair(Pair(name, value), rest_list) -> Pair(Pair(name, Pair(Pair(Symbol"quote", Pair(Symbol "whatever", Nil)), Nil)), (attach_whatever_to_var rest_list))
    | _ -> local_vars;;

    let rec create_body_letrec local_vars body = match local_vars with
    | Nil -> body
    | Pair(Pair(name, value), rest_list) -> Pair(Pair(Symbol("set!"), Pair(name, value)), (create_body_letrec rest_list body))
    | _ -> local_vars
  (* General function to wrap a sexpr inside a lambda *)
  let rec lambda_wrapper sexpr = Pair(Symbol("lambda"),Pair(Nil,Pair(sexpr,Nil)));;
  (* General function to generate a let function with name and value*)
  let rec let_transform sexpr_name sexpr_value = Pair(Symbol(sexpr_name),Pair(sexpr_value,Nil));;
  (* General functions to generate let bodies  *)
  let rec let_body_gen1 test dit_func dif_func = Pair(Symbol("if"),Pair(Symbol(test),Pair(Pair(Pair(Symbol(dit_func),Nil),Pair(Symbol(test),Nil)),Pair(Pair(Symbol(dif_func),Nil),Nil))));;
  let rec let_body_gen2 test dit_func = Pair(Symbol("if"),Pair(Symbol(test),Pair(Pair(Pair(Symbol(dit_func),Nil),Pair(Symbol(test),Nil)),Nil)));;

  (* -------------------------------------------------------------------------------- *)
  (* The Tag Parser *)
  (* -------------------------------------------------------------------------------- *)

  let rec tag_parse sexpr =
    match sexpr with 
    |Number(num) -> Const(Sexpr(Number(num)))
    |Bool (boolean) -> Const(Sexpr(Bool(boolean)))
    |Char (ch) -> Const(Sexpr(Char(ch)))
    |String(str) -> Const(Sexpr(String(str)))
    |TagRef(str) -> Const(Sexpr(TagRef(str)))
    |TaggedSexpr(str,value) -> Const(Sexpr(TaggedSexpr(str,value)))    
    |Pair(Symbol("quote"),Pair(rest,Nil)) -> Const(Sexpr(rest))
    |Pair(Symbol("if"),Pair(test,Pair(dit, Pair(dif,Nil)))) -> If((tag_parse test), (tag_parse dit),(tag_parse dif))
    |Pair(Symbol("if"),Pair(test,Pair(dit, Nil))) -> If((tag_parse test),(tag_parse dit),Const(Void))
    |Pair(Symbol("lambda"),Pair(Symbol(str),body)) -> LambdaOpt([],legal_symb_validation str,(lambda_body_parse body))
    |Pair(Symbol("lambda"),Pair(args,body)) -> if (check_lambda_is_simple args) then LambdaSimple((dismantle_sexpr_to_string_list args []), (lambda_body_parse body)) else LambdaOpt((dismantle_sexpr_to_string_list args []),(last_sym args),(lambda_body_parse body))
    |Pair(Symbol("or"),body) -> or_parser body
    |Pair(Symbol("define"), Pair(Symbol(str),Nil)) -> Def(Var(legal_symb_validation str),Const(Void))
    |Pair(Symbol("define"), Pair(Symbol(str),Pair(sexpr,Nil))) -> Def(Var(legal_symb_validation str), (tag_parse sexpr)) (* Simple Define *)
    |Pair(Symbol("begin"),sexpr) -> begin_parse sexpr
    |Pair(Symbol("set!"), Pair(x,Pair(y,Nil))) -> Set((check_var (tag_parse x)),(tag_parse y))
    (* macro expansions *)
    |Pair(Symbol("define"), Pair(Pair(Symbol(str),args),body)) -> (exp_define str args body)  (* MIT Define *)
    |Pair(Symbol("and"), body) -> tag_parse (exp_and body)    
    |Pair(Symbol("quasiquote"), Pair(sexpr,Nil)) -> tag_parse (exp_quasiquote sexpr)
    |  Pair(Symbol("cond"),body) -> tag_parse (exp_cond body)
    |  Pair(Symbol("let"), let_expr) -> tag_parse (exp_let let_expr)
    |  Pair(Symbol("let*"), letstar_expr) -> tag_parse (exp_letstar letstar_expr)
    |  Pair(Symbol("letrec"), letrec_expr) -> tag_parse (exp_letrec letrec_expr)
    |Pair(sexpr,rest) -> Applic((tag_parse sexpr),(List.map tag_parse (dismantle_to_sexpr_list rest)))
    |Symbol(str) -> Var(legal_symb_validation str)
    |_ -> raise X_syntax_error

  (* ---------------------------------------------------------------------------------------------------------------------- *)
  (* Macro - Expansions *)
  (* ---------------------------------------------------------------------------------------------------------------------- *)
  and exp_and and_body = match and_body with
    | Nil -> Bool(true)
    | Pair(sexpr, Nil) -> sexpr
    | Pair(sexpr, rest) -> Pair(Symbol("if"), Pair(sexpr, Pair( (exp_and rest), Pair( Bool(false), Nil ))))
    | _ -> raise X_syntax_error
  and exp_define str args define_body =
    let l = (List.map tag_parse (dismantle_to_sexpr_list define_body)) in
    if(List.length l != 0) then 
      (Def(Var(legal_symb_validation str), tag_parse (Pair(Symbol("lambda"), Pair(args, define_body)))))
    else raise X_syntax_error
  and exp_let let_expr = match let_expr with
  | Pair(local_vars, body) -> Pair(Pair((Symbol("lambda")), Pair((flat_params_names local_vars), body)), (flat_params_values local_vars)) 
  | _ -> let_expr

  and exp_letstar letstar_expr = match letstar_expr with
  (* [(let* () ⟨expr 1 ⟩ · · · ⟨expr m ⟩)]= [(let () ⟨expr 1 ⟩ · · · ⟨expr m ⟩)] *)
  | Pair(Nil, body) -> Pair(Symbol("let"), letstar_expr)
  (* [(let* ((v ⟨Expr⟩)) ⟨expr 1 ⟩ · · · ⟨expr m ⟩)] = [(let ((v Expr)) ⟨expr 1 ⟩ · · · ⟨expr m ⟩)] *)
  | Pair(Pair(Pair(name, value), Nil), body) -> Pair(Symbol("let"), letstar_expr)
  (* 
    [(let* ((v 1 ⟨Expr 1 ⟩) (v 2 ⟨Expr 2 ⟩) · · · (v n ⟨Expr n ⟩)) ⟨expr 1 ⟩ · · · ⟨expr m ⟩)]
    = [(let ((v 1 ⟨Expr 1 ⟩)) 
        (let* ((v 2 ⟨Expr 2 ⟩) · · · (v n ⟨Expr n ⟩)) ⟨expr 1 ⟩ · · · ⟨expr m ⟩))] *)
  | Pair(Pair(first_value, rest_vars), body) -> Pair(Symbol("let"), Pair(Pair(first_value, Nil),
                                                      Pair(Pair(Symbol("let*"), Pair(rest_vars, body)), Nil)))
  | _ -> letstar_expr

  and exp_letrec letrec_expr = match letrec_expr with
  | Pair(local_vars, body) -> Pair(Symbol("let"),Pair((attach_whatever_to_var local_vars), (create_body_letrec local_vars body)))
  | _ -> letrec_expr
  and exp_cond cond_body =
    match cond_body with
    |  Pair(Pair(test,Pair(Symbol("=>"),Pair(dit,Nil))),Nil) -> Pair(Symbol("let"),Pair(Pair((let_transform "value" test),Pair((let_transform "f" (lambda_wrapper dit)),Nil)),Pair((let_body_gen2 "value" "f"),Nil)))
    |  Pair(Pair(test,Pair(Symbol("=>"),Pair(dit,Nil))),dif) -> Pair(Symbol("let"),Pair(Pair((let_transform "value" test),Pair((let_transform "f" (lambda_wrapper dit)),Pair((let_transform "rest" (lambda_wrapper (Pair(Symbol("cond"),dif)))),Nil))),Pair((let_body_gen1 "value" "f" "rest"),Nil)))
    |  Pair(Pair(Symbol("else"),dit),_) -> Pair(Symbol("begin"),dit)
    |  Pair(Pair(test,dit),Nil) -> Pair(Symbol("if"),Pair(test,Pair(Pair(Symbol("begin"),dit),Nil)))
    |  Pair(Pair(test,dit),dif) -> Pair(Symbol("if"),Pair(test,Pair(Pair(Symbol("begin"),dit),Pair(Pair(Symbol("cond"),dif),Nil))))
    |  _ -> cond_body
  and exp_quasiquote x = match x with
    | Pair(Symbol("unquote"), Pair(sexpr,Nil)) -> sexpr
    | Pair(Symbol("unquote-splicing"), Pair(_,Nil)) -> (raise X_syntax_error)
    | Pair(Pair(Symbol("unquote-splicing"), Pair(sexpr1,Nil)),sexpr2) -> Pair(Symbol "append", Pair(sexpr1, Pair(exp_quasiquote sexpr2, Nil)))
    | Pair(sexpr1, Pair(Symbol("unquote-splicing"), sexpr2)) -> Pair(Symbol "cons", Pair(exp_quasiquote sexpr1, sexpr2))
    | Pair(sexpr1,sexpr2) -> Pair(Symbol "cons", Pair(exp_quasiquote sexpr1, Pair(exp_quasiquote sexpr2, Nil)))
    | Symbol(sexpr) -> Pair(Symbol("quote"),Pair(Symbol(sexpr),Nil))
    | Nil -> Pair(Symbol("quote"),Pair(Nil,Nil))
    | _ -> x

  (* ---------------------------------------------------------------------------------------------------------------------- *)
  (* Unique - Expressions - Parser *)
  (* ---------------------------------------------------------------------------------------------------------------------- *)
  and or_parser or_body =
    match or_body with 
    | Pair(sexpr, Nil) -> tag_parse sexpr
    | Pair(sexpr,rest) -> Or((List.map tag_parse (dismantle_to_sexpr_list or_body)))
    | Nil -> Const(Sexpr(Bool(false)))
    | _-> raise X_syntax_error
  and begin_parse begin_body = match begin_body with
    | Pair(sexpr,Nil)-> tag_parse sexpr
    | Pair(sexpr,rest)-> Seq((List.map tag_parse (dismantle_to_sexpr_list begin_body)))
    | Nil -> Const(Void)
    | _-> raise X_syntax_error
  and lambda_body_parse body =
    match body with
    |Pair(sexpr,Nil) -> tag_parse sexpr
    |Pair(sexpr,rest) -> Seq((List.map tag_parse (dismantle_to_sexpr_list body)))
    | _-> raise X_syntax_error;;
  

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

  let reserved_word_list =
    ["and"; "begin"; "cond"; "define"; "else";
     "if"; "lambda"; "let"; "let*"; "letrec"; "or";
     "quasiquote"; "quote"; "set!"; "unquote";
     "unquote-splicing"];;  

     let tag_parse_expression sexpr = tag_parse sexpr;;

let tag_parse_expressions sexpr = (List.map tag_parse_expression sexpr);;
  



end;; (* struct Tag_Parser *)

  



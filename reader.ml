#use "pc.ml";;
(* open Pc;; *)
open PC;;
exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type number =
  | Int of int
  | Float of float;;

type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | TaggedSexpr of string * sexpr
  | TagRef of string;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | TaggedSexpr(name1, expr1), TaggedSexpr(name2, expr2) -> (name1 = name2) && (sexpr_eq expr1 expr2) 
  | TagRef(name1), TagRef(name2) -> name1 = name2
  | _ -> false;;


(* General *)
let extract_AST (ast,rest) = ast;;
let nt_whitespaces = star (nt_whitespace);;
let make_paired nt_left nt_right nt =
  let nt = caten nt_left nt in
  let nt = pack nt (function (_, e) -> e) in
  let nt = caten nt nt_right in
  let nt = pack nt (function (e, _) -> e) in
  nt;;
let make_spaced nt = make_paired nt_whitespaces nt_whitespaces nt;;
let digit = range '0' '9';;

let get_wrapped_sexpr token_left exp token_right = 
  let wrapped_exp = caten token_left exp in
  let wrapped_exp = caten wrapped_exp token_right in
  let wrapped_exp = pack wrapped_exp (fun ((_,e),_) -> e) in
  wrapped_exp;;

let tok_lparen = make_spaced (char '(');;
let tok_rparen = make_spaced (char ')');;
let tok_lparen_curly = make_spaced (char '{');;
let tok_rparen_curly = make_spaced (char '}');;
let tok_dotparen = make_spaced (char '.');;
let not_digits = 
  const (fun ch -> ch > '9') ;;
let symbol_list = ref [];;

let rec star_with_effect nt s =
  try let (e, s) = (nt s) in
    symbol_list := [];
    let (es, s) = (star_with_effect nt s) in
    (e :: es, s)
  with X_no_match -> ([], s);;


let quote_tokens = (disj_list [word("\'") ; word("`") ; word(",@") ; word(",")]);;

let get_qoute_name s = 
  match s with
  | "\'" -> "quote"
  | "`" -> "quasiquote"
  | ",@" -> "unquote-splicing"
  | "," -> "unquote"
  | _ -> raise X_no_match;;



(* Boolean *)
let nt_true = disj (word "#t") (word "#T");;
let nt_false = disj (word "#f") (word "#F");;
let nt_boolean = 
  let check = disj nt_true nt_false in
  pack check (fun (ds) -> match ds with 
      | ['#';'t'] -> Bool true
      | ['#';'T'] -> Bool true
      | ['#';'f'] -> Bool false
      | ['#';'F'] -> Bool false
      | _ -> raise X_no_match  );;

(* Char *)
let nt_char_prefix = word "#\\";;
let nt_nul = word_ci "nul";;
let nt_newline = word_ci "newline";;
let nt_return = word_ci "return";;
let nt_tab = word_ci "tab";;
let nt_page = word_ci "page";;
let nt_space = word_ci "space";;

let nt_null_to_char  = pack nt_nul (fun (ds) -> '\000');;
let nt_newline_to_char  = pack nt_newline (fun (ds) -> '\010');;
let nt_return_to_char  = pack nt_return (fun (ds) -> '\013');;
let nt_tab_to_char  = pack nt_tab (fun (ds) -> '\009');; 
let nt_page_to_char  = pack nt_page (fun (ds) -> '\012');;
let nt_space_to_char  = pack nt_space (fun (ds) -> '\032');;

let nt_named_char = disj_list [nt_null_to_char;nt_newline_to_char;nt_return_to_char;nt_space_to_char;nt_tab_to_char;nt_page_to_char];;

let nt_named_chars = caten nt_char_prefix nt_named_char;;
let nt_visible_char = caten nt_char_prefix (range '\032' '\255');;


let nt_char  =
  let check = disj nt_named_chars nt_visible_char in
  pack check (fun (ds) -> match ds with
      |(_,l) -> Char (l)
    );;

(* Symbol *)
let nt_special_char = 
  let nt_exclemation = char '!' in
  let nt_dollar =  char '$' in
  let nt_power = char '^' in
  let nt_star = char '*' in
  let nt_score =  char '-'  in
  let nt_underscore =  char '_' in
  let nt_eq =  char '='  in
  let nt_plus = char '+' in
  let nt_left_arrow =  char '<' in
  let nt_right_arrow =  char '>' in
  let nt_quest_mark =  char '?' in
  let nt_slash =  char '/' in
  let nt_colon =  char ':' in  
  let nt = disj_list [nt_exclemation ; nt_dollar ; nt_power ; nt_star ; nt_score ; nt_underscore ; nt_eq ; nt_plus ; 
                      nt_left_arrow ; nt_right_arrow ; nt_quest_mark ; nt_slash ; nt_colon ] in
  nt;; 

let nt_lower_case_abc = range 'a' 'z';;
let nt_upper_case_abc = pack (range 'A' 'Z') (fun(x) -> Char.lowercase_ascii x );;

let nt_symbol_char =    
  let nt = disj_list [digit ; nt_special_char; nt_lower_case_abc ; nt_upper_case_abc] in  
  nt;;

let nt_symbol = 
  let nt = plus nt_symbol_char in
  let nt  = not_followed_by nt (disj (char '@') (char '.')) in
  pack nt (fun (ds) ->  Symbol (list_to_string ds) );;


(* Number *)
let nt_natural =  (* Digit+ *)
  let digits = plus digit in
  pack digits (fun (ds) -> (int_of_string (list_to_string ds)));;


let nt_integer = 
  let nt_plus = pack (char '+') (fun _-> +1) in
  let nt_minus = pack (char '-') (fun _-> -1) in
  let nt = disj nt_plus nt_minus in
  let nt = maybe nt in
  let nt = pack nt (function | None -> +1
                             | Some(mult) -> mult) in
  let nt = caten nt nt_natural in
  pack nt (fun (mult,n) -> mult * n);;

let make_float =     
  let digits = pack nt_integer (fun(e) -> string_to_list (string_of_int e)) in
  let nt = pack (caten digits (char '.')) (fun(e,l) -> e@[l])  in
  let nt = pack (caten nt (plus digit)) (fun(ds) -> match ds with
        (e,l) -> e@l) in
  pack nt (fun(ds) -> (float_of_string (list_to_string ds)));;  

let nt_float = 
  let nt_plus = pack (char '+') (fun _-> +1.) in
  let nt_minus = pack (char '-') (fun _-> -1.) in
  let nt = disj nt_plus nt_minus in
  let nt = maybe nt in
  let nt = pack nt (function | None -> +1.
                             | Some(mult) -> mult) in
  let nt = caten nt make_float in
  pack nt (fun (mult,n) -> mult *. n);;


(* scientfic number *)
let rec power a b = 
  if b = 0 then 1.0  
  else ( 
    if b < 0 then ((power a (b+1) /. a)) 
    else (a *. (power a (b - 1)))
  );;


let nt_scientific_number =
  let scientific_exponent = disj (pack (char 'e') (fun(ds) -> [ds])) (pack (char 'E') (fun(ds) -> [ds])) in
  let nt = caten (disj nt_float (pack nt_integer (fun (x) -> float_of_int(x)))) (pack scientific_exponent (fun (e) -> 10.0)) in   
  let nt = caten nt nt_integer in  
  let nt = pack nt (fun ((a,e),b) -> (a *. power e b)) in  
  nt;;


let nt_number  =
  let scientific_number = (pack (not_followed_by nt_scientific_number (disj (char '.') (char '@'))) (fun (ds) -> Float(ds))) in
  let float_number =  (pack (not_followed_by nt_float (disj (char '.') (char '@'))) (fun(ds) -> Float(ds))) in
  let int_number = (pack (not_followed_by nt_integer (disj (char '.') (char '@'))) (fun(ds) -> Int(ds))) in
  let nt = pack (disj_list [ scientific_number ; float_number ; int_number]) (fun(ds) -> Number(ds)) in
  not_followed_by nt nt_symbol_char;;

(* radix *)

let check_radix_base base=
  if base < 2 || base > 36 then raise X_no_match
  else base;;

let check_n_for_base n base = 
  if n >= base then raise X_no_match else n;;

let radix_get_number_from_char c base = 
  if c >= '0' && c <= '9' then (int_of_char(c) - 48)
  else (
    if c >= 'a' && c <= 'z' then (check_n_for_base (int_of_char(c) - 87) base)
    else (
      if c >= 'A' && c <= 'Z' then (check_n_for_base (int_of_char(c) - 55) base)
      else raise X_no_match
    )
  );;

(* Sigma of (d_i ^ p) b  pow<=p<=stop_power*)
let rec calc_sum d_list base pow sum stop_power len= 
  if pow = stop_power then sum +. float_of_int(radix_get_number_from_char (List.nth d_list (len)) base)
  else (
    let p = if pow < 0 then (0-pow) else pow in
    (calc_sum d_list base (pow-1) sum stop_power len) +.
    ((power (float_of_int(base)) pow) *. float_of_int(radix_get_number_from_char (List.nth d_list (len -p)) base))
  );;

let rec calc_sum_frac d_list base pow sum stop_power len= 

  if pow == stop_power then sum +. ((power (float_of_int(base)) pow) *. float_of_int(radix_get_number_from_char (List.nth d_list (len )) base))
  else (

    (calc_sum_frac d_list base (pow-1) sum stop_power len) +.
    ((power (float_of_int(base)) pow) *. float_of_int(radix_get_number_from_char (List.nth d_list (len - (0 - pow))) base))
  );;

let calc_radix_int base d_list = 
  let len = (List.length d_list) - 1 in
  let stop_power = 0 in       
  match d_list with 
  | '-'::d ->     (0. -. (calc_sum d base (len-1) 0. stop_power (len-1)))
  | '+'::d ->     calc_sum d base (len-1) 0. stop_power (len-1)
  | _ ->     calc_sum d_list base len 0. stop_power len;;


let calc_radix_fraction base frac = 
  let len = List.length(frac) -1 in
  let stop_power = (0 - List.length(frac)) in     
  calc_sum_frac frac base (-1) 0. stop_power len;;

let calc_radix_float base d_list frac =
  match d_list with 
  | '-'::d ->     (0. -. ((calc_radix_int base d) +. (calc_radix_fraction base frac)) )
  | '+'::d ->     ((calc_radix_int base d) +. (calc_radix_fraction base frac))
  | _ ->    ((calc_radix_int base d_list) +. (calc_radix_fraction base frac));;

let nt_calc_radix base n = 
  let b = check_radix_base base in
  let n_str = list_to_string n in  
  let index = try (String.index n_str '.') with Not_found -> (-1) in

  if index == (-1) then (Int( int_of_float(calc_radix_int b n))) else (
    let d = String.sub n_str 0 index in
    let d = string_to_list d in
    let frac = String.sub n_str (index + 1) ((String.length n_str) - 1 - index) in
    let frac = string_to_list frac in
    Float(calc_radix_float base d frac)
  );;   


let nt_radix =     
  let radix_prefix = pack (char '#') (fun(ds) -> [ds]) in
  let raidx_notation = disj (pack (char 'r') (fun(ds) -> [ds])) (pack (char 'R') (fun(ds) -> [ds])) in
  let nt_base = caten radix_prefix nt_integer in
  let baseR = caten nt_base raidx_notation in
  let nt_sign = disj (pack (char '+') (fun(ds) -> [ds])) (pack (char '-') (fun(ds) -> [ds])) in    
  let nt_n  = caten (maybe nt_sign) (plus (disj_list [nt_lower_case_abc ; nt_upper_case_abc ; digit ; (char '.')])) in
  let baseRn = caten baseR nt_n in
  let nt = pack baseRn (fun (((hashtag, base) , r) , (sign, n)) -> (
        nt_calc_radix base (match sign with | None -> n | Some s -> s@n )
      )) in 
  pack nt (fun (x) -> Number(x));;




(* String  *)
let nt_meta_string =
  let nt_backslash = pack (word "\\\\") (fun _ -> '\\') in
  let nt_quote = pack (word "\\\"") (fun _ -> '"') in
  (* let nt_quote2 = pack (char '"') (fun _ -> '"') in *)
  let nt_tab = pack (word_ci "\\t") (fun _ -> '\t') in
  let nt_f = pack (word_ci "\\f") (fun _ -> '\012') in
  let nt_n = pack (word_ci "\\n") (fun _ ->'\n') in
  let nt_n2 = pack (word_ci "\n") (fun _ ->'\n') in
  let nt_r = pack (word_ci "\\r") (fun _ ->'\r') in
  let nt = disj_list [nt_backslash; nt_quote; nt_tab; nt_f; nt_n;nt_n2; nt_r;] in
  nt;; 

let nt_literal_char = pack (range '\032' '\255') (fun(ds) -> match ds with
    | '\\' -> raise X_no_match
    | '\"' -> raise X_no_match
    | _ -> ds );;

let nt_string_char = 
  let nt = disj nt_literal_char nt_meta_string in
  nt;;


let nt_string = 	
  let nt = caten_list [(pack (char '"') (fun(ds) -> [ds])) ; (star nt_string_char) ; (pack (char '"') (fun(ds) -> [ds]))] in
  let nt = pack nt (fun(ds) -> match ds with
      | [a;b;c] -> b
      | _ -> raise X_no_match) in
  pack nt (fun(ds) -> String (list_to_string ds));;

let line_comment_check s =
  let check = try  ((char ';')s) with X_no_match -> ('b',s) in 
  match check with | (';',_) -> true
                   | _ -> false


let rec nt_sexpr s = (make_spaced (disj_list [ nt_simple_sexpr ; nt_tagsexpr ])) (line_comments s)
and nt_simple_sexpr s = (disj_list [nt_boolean ; nt_char ; nt_number ; nt_radix ; nt_string ; nt_symbol ;  nt_list  ; nt_dotted_list  ; nt_any_quote ; nt_sexpr_comment 0]) s
and nt_tagsexpr s = (disj_list [nt_tagged_expr ; nt_tag]) s

(* Line Comments *)
and line_comments s =
  let nt = caten (char ';') (star (disj (range '\000' '\009') (range '\011' '\255'))) in
  let nt = caten nt (disj nt_end_of_input (pack (char '\010') (fun(x) ->[x]))) in
  let nt = make_spaced nt in
  let ln = try (nt s) with X_no_match -> (('a',['a']),['a']),s 
  in match ln with (a,b) -> if(line_comment_check b) then line_comments b else b

(* List *)
and nt_list s =   
  let nt_1 = (caten tok_lparen (star nt_any)) s in
  let rs_1 = match nt_1 with ((a,b),c) -> a :: line_comments b in 
  let nt_2 = caten tok_lparen (star nt_sexpr) rs_1 in 
  let nt_2 = match nt_2 with ((a,l),b) -> if(List.mem (Number(Int (7582))) l) then (let l2 = (List.filter (fun x -> (not (sexpr_eq x (Number(Int 7582)))) ) l) in ((a,l2),b)) else ((a,l),b) in
  let rs_2 = match nt_2 with (a,b) -> line_comments b in
  let nt_3 = tok_rparen rs_2 in
  let finish = match nt_3 with (a,b) -> b in
  let nt_4 = match nt_2 with ((a,b),c) -> ((a,b),finish) in 
  match nt_4 with  ((a,l),b) -> (List.fold_right (fun a b -> Pair(a,b)) l Nil,b)

and nt_dotted_list s = 
  let nt_1 = (caten tok_lparen (star nt_any)) s in
  let rs_1 = match nt_1 with ((a,b),c) -> a :: line_comments b in 
  let nt_2 = caten tok_lparen (plus nt_sexpr) rs_1 in
  let nt_2 = match nt_2 with ((a,l),b) -> if(List.mem (Number(Int (7582))) l) then (let l2 = (List.filter (fun x -> (not (sexpr_eq x (Number(Int 7582)))) ) l) in ((a,l2),b)) else ((a,l),b) in
  let first = match nt_2 with (a,b) -> a in
  let rs_2 = match nt_2 with (a,b) -> line_comments b in 
  let nt_3 = tok_dotparen rs_2 in
  let dot = match nt_3 with (a,b) -> a in
  let rs_3 = match nt_3 with (a,b) -> line_comments b in
  let nt_4 = nt_sexpr rs_3 in 
  let second = match nt_4 with (a,b) -> a in
  let rs_4 = match nt_4 with (a,b) -> line_comments b in
  let fix_1 = tok_rparen rs_4 in
  let rs_5 = match fix_1 with (a,b) -> b in
  let nt_5 = first,dot,second in
  match nt_5 with ((a,l),c,r) -> (List.fold_right (fun a b -> Pair(a,b)) l r,rs_5)


(* Quotes *)
and nt_any_quote s =  
  let nt = caten quote_tokens (nt_sexpr) in
  (pack nt (fun (name, exp) -> Pair(Symbol(get_qoute_name (list_to_string name) ), Pair(exp, Nil)))) s

(* Tags *)
and nt_tag s =
  let nt_sulamit = char '#' in
  let nt = caten nt_sulamit (get_wrapped_sexpr tok_lparen_curly (plus nt_symbol_char) tok_rparen_curly)
  in (pack nt (fun(ds) -> match ds with 
      | (_,symbol) -> TagRef (list_to_string symbol))) s 

and nt_tagged_expr s =
  let nt_sulamit = char '#' in
  let nt = caten_list [pack nt_sulamit (fun x -> [x]) ; pack (char '{') (fun x -> [x])  ;  plus nt_symbol_char  ; pack (char '}') (fun x -> [x]) ; pack (char '=') (fun x -> [x])] in
  let nt2 = (pack nt (fun e -> match e with 
      | [_;_;symbol;_;_] -> symbol
      | _-> raise X_no_match)) s in
  let symbol = match nt2 with (a,b) -> a in
  let rs = match nt2 with (a,b) -> b in
  if(List.mem symbol !symbol_list) then raise X_this_should_not_happen else
    (
      symbol_list := symbol::!symbol_list;
      let nt = nt_sexpr rs in
      match nt with (a,b) -> (TaggedSexpr ((list_to_string symbol),a),b)
    ) 
(* Sexpr comments *)
and nt_sexpr_comment count s =
  let separated = (make_spaced (word "#;")) s in
  match separated with 
  | (_,rs) -> try (nt_sexpr_comment (count+1) rs) with X_no_match -> remove_sexprs (count+1) rs

and remove_sexprs num rs =
  if(num == 0) then (try(nt_sexpr rs) with X_no_match-> Number(Int 7582)  ,rs) else 
    let nt = nt_sexpr rs in
    let expr = match nt with (a,b) -> a in
    match expr with | (TaggedSexpr (x,y))  ->  (symbol_list := List.filter (fun(z) -> if ((compare (list_to_string z) x)==0) then false else true) !symbol_list ; match nt with (_,rrs) -> remove_sexprs (num-1) rrs)                                                                                                                         
                    | _ -> match nt with (_,rrs) -> remove_sexprs (num-1) rrs;;


module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
  let normalize_scheme_symbol str =
    let s = string_to_list str in
    if (andmap
          (fun ch -> (ch = (lowercase_ascii ch)))
          s) then str
    else Printf.sprintf "|%s|" str;;

  let read_sexpr string = 
    symbol_list:=[];
    let list_of_chars = string_to_list string in
    extract_AST (nt_sexpr list_of_chars);;

  let read_sexprs string = 
    symbol_list:=[];
    let list_of_chars = string_to_list string in
    let nt = star_with_effect nt_sexpr in
    extract_AST (nt list_of_chars);;


end;; (* struct Reader *)







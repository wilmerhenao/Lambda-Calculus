(*Wilmer Henao*)
open Printf;;
open String;;

type location = int ;;

type type_specifier =
    IntegerSpecifier of location  | FunctionSpecifier of location * type_specifier * type_specifier
  ;;

type expression =
    AbstractionNode of location * string * type_specifier * expression
  | ApplicationNode of location * expression * expression
  | VariableNode of location * string  | IntegerNode of location * string
  ;;

type sort =
    IntegerT
  | FunctionT of sort * sort
  ;;

let rec convert_type_spec = function
    IntegerSpecifier _ -> IntegerT
  | FunctionSpecifier(_, t1, t2) ->
      FunctionT(convert_type_spec t1, convert_type_spec t2)
  ;;

(* ================================= Parsing =============================== *)

(* The result of a parsing function: it either matches the input,
 * returning the index of the next token (skipping any white space)
 * and any value, or it fails, omitting any error reporting for now.
 *)

type 'a parse_result =
    ParseMatch of int * 'a
  | ParseError
  ;;

exception IllegalState ;;

let result_is_match = function ParseMatch _ -> true | _ -> false ;;
let result_is_error = function ParseError -> true   | _ -> false ;;

let result_index = function
    ParseMatch ( idx, _ ) -> idx
  | ParseError -> raise IllegalState
  ;;

let result_value = function
    ParseMatch ( _, v ) -> v
  | ParseError -> raise IllegalState
  ;;

(* Useful predicates on individual characters. *)
let is_space c = (c = ' ' || c = '\t' || c ='\n') ;;
let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ;;
let is_num c = (c >= '0' && c <= '9') ;;

(* Scan for chracters matching a predicate. *)
let rec scan pred s i =
  if i >= String.length s then i else
  if pred s.[i] then scan pred s (i+1)
  else i
  ;;

(* Make a parsing function recognizing a fixed string t.
 *
 * Note that this definition leverages O'Caml's support
 * for "currying", i.e., a function with more than one
 * argument really is a function that returns a function
 * just as in the lambda calculus.
 *)
let make_parse_string t s i =
  let tlen = String.length t in
  let slen = String.length s in
  if i >= slen || i+tlen > slen then ParseError else
  if t <> String.sub s i tlen then ParseError else
  ParseMatch(scan is_space s (i+tlen), ())    (* Skip trailing spaces. *)
  ;;

(* Parsing functions for the fixed tokens. *)
let parse_open = make_parse_string "(";;
let parse_close = make_parse_string ")";;
let parse_backslash = make_parse_string "\\";;
let parse_colon = make_parse_string ":";;
let parse_int = make_parse_string "int";;
let parse_arrow = make_parse_string "->";;
let parse_dot = make_parse_string ".";;

(* Parsing function for the identifier and number tokens. *)
let parse_token p s i =
   let j = scan p s i in
   if i = j then ParseError
   else ParseMatch(scan is_space s j, String.sub s i (j-i))
   ;;

(* Parsing functions for the hierarchical syntax. *)
let rec parse_sort s i =
   let left = parse_sort_base s i in
   if result_is_error left then ParseError
   else let arr = parse_arrow s (result_index left) in 
   if result_is_error arr then left    (* No arrow -> no function spec. *)
   else let right = parse_sort s (result_index arr) in
   if result_is_error right then ParseError
   else ParseMatch(result_index right,
                   FunctionSpecifier(i, result_value left, result_value right))
       (*yo creo que functionSpecifier es clave para encontrar el typo de la fn*)

and parse_sort_base s i =
   let res = parse_int s i in                  (* An int specifier. *)
   if result_is_match res
   then ParseMatch(result_index res, IntegerSpecifier i) (*devuelve la pos. final de int y donde comienza el IntegerSpecifier*)

   else let op = parse_open s i in             (* A parenthesized type spec. *)
   if result_is_error op then ParseError
   else let res = parse_sort s (result_index op) in
   if result_is_error res then ParseError
   else let cl = parse_close s (result_index res) in
   if result_is_error cl then ParseError
   else ParseMatch(result_index cl, result_value res)
   ;;

let rec parse_expr s i =
  let res = parse_base_expr s i in
  if result_is_error res then ParseError (*if there's error throw it*)
  else parse_app_expr res s (result_index res) (*if not application continues*)
     
and parse_app_expr base s i =
   (* Applications are left associative.  To ensure that the abstract
      * syntax tree reflects that fact, we use an extra argument
      * representing the base value for each recursive invocation.
   *)
  let res = parse_base_expr s i in
  if result_is_error res then base
  else let new_base = ParseMatch(result_index res,
                                  ApplicationNode(result_index base,
                                                  result_value base,
                                                  result_value res)) in
   parse_app_expr new_base s (result_index res)

and parse_base_expr s i =
   let res = parse_lambda_expr s i in          (* A lambda. *)
   if result_is_match res
   then res

   else let res = parse_token is_alpha s i in  (* A variable name. *)
   if result_is_match res
   then ParseMatch(result_index res, VariableNode(i, result_value res))

   else let res = parse_token is_num s i in    (* An integer literal. *)
   if result_is_match res
   then ParseMatch(result_index res, IntegerNode(i, result_value res))

   else let op = parse_open s i in             (* A parenthesized expr. *)
   if result_is_error op then ParseError
   else let res = parse_expr s (result_index op) in
   if result_is_error res then ParseError
   else let cl = parse_close s (result_index res) in
   if result_is_error cl then ParseError
   else ParseMatch(result_index cl, result_value res)

and parse_lambda_expr s i =
   let bs = parse_backslash s i in                             (* Backslash. *)
   if result_is_error bs then ParseError
   else let par = parse_token is_alpha s (result_index bs) in  (* Parameter. *)
   if result_is_error par then ParseError
   else let col = parse_colon s (result_index par) in          (* Colon. *)
   if result_is_error col then ParseError
   else let typ = parse_sort s (result_index col) in           (* Type spec. *)
   if result_is_error typ then ParseError
   else let dot = parse_dot s (result_index typ) in            (* Dot. *)
   if result_is_error dot then ParseError
   else let bod = parse_expr s (result_index dot) in           (* Expression. *)
   if result_is_error bod then ParseError
   else ParseMatch(result_index bod,
                   AbstractionNode(i,
                                   result_value par,
                                   result_value typ,
                                   result_value bod))
   ;;

let parse s =
   let start = scan is_space s 0 in
   let res = parse_expr s start in
   if result_is_error res then None
   else if result_index res <> String.length s then None
   else Some (result_value res)
   ;;
(*this is where I play*)

(*get the middle member*)
let fun_middle fs = match fs with
  FunctionSpecifier( _ , stuff, _ ) -> stuff
| _ -> raise IllegalState
    ;;

(*get the last member of the type structure*)
let fun_last fs = match fs with
  FunctionSpecifier( _ , _ , stuff) -> stuff
| _ -> raise IllegalState
    ;;

(*get the integer position given an IntegerSpecifier member*)
let findposit tspec = match tspec with
  IntegerSpecifier(a) -> a
  | _ -> raise IllegalState
      ;;

let ctos x =
  String.make 1 x
;;

(*this is where I left yesterday*)
let rec print_between s z fin =
    let a = ctos s.[z] in
    print_string a;
    if z < fin then
      print_between s (z+1) fin
else print_string ")->"
      ;;

(*get the expression that corresponds a FunctionSpecifier "type"*)
let string_finder s funob =
  let the_middle = fun_middle funob in
  let the_end = fun_last funob in
  let start_pos = findposit the_middle in
  let end_pos = findposit the_end in
  print_string "(";
  print_between s start_pos (end_pos+2)
    ;;


(*"(" ^ print_between s start_pos end_pos ^ ")->" *)
(*gettin' particular members of my expression types of type "type_specifier"*)
(*gettin' the 3rd*)
let get_third_from ast = match ast with
  AbstractionNode( _ , _ , stuff , _ ) -> stuff
| _ -> raise IllegalState
    ;;

let get_third_from_an_appl_node ast = match ast with
  ApplicationNode( _ , _ , stuff ) -> stuff
| _ -> raise IllegalState
    ;;

(*gettin' the 4th*)
let get_fourth_from ast = match ast with
  AbstractionNode( _ , _ , _ , stuff ) -> stuff
| _ -> raise IllegalState
    ;;

(* This is where most of the printing takes place*)
   let rec print_types s ast =
   let the_third = get_third_from ast in
   string_finder s the_third;
    (*let type1pr = string_finder s the_third in*)
    (*print_string type1pr;  or an expression like it *)
   let the_fourth = get_fourth_from ast in
   let third_in_app = get_third_from_an_appl_node the_fourth in
   analyze_application s third_in_app
  

(*if it's an integer node print int;  if it's an abstraction node cont. print_types*)
and analyze_application s appl = match appl with
  AbstractionNode( _ , _ , _ , _ ) -> print_types s appl (*continue with ast*)
| IntegerNode( _ , _ ) -> print_string "int"
|  _ -> raise IllegalState
      ;;

(*Here I get the cdr of a ParseMatch type*)
let eval1 s obj =
  let ast = result_value obj in
  print_types s ast
  ;;
    
let rec print_out s =
   print_string ("\n" ^ s ^ " :: ");
   let res = parse_expr s 0 in
   eval1 s res
;;

(*This is the function in charge of the loop*)

let _ =
  let rec printline () =
    try
      print_endline "";
      print_string ">";
      flush stdout;
      let line = input_line stdin in
      print_out line;
      printline()
    with End_of_file -> ()
  in
  printline()
    ;;

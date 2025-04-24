(* camlp5o *)
(* streams.ml,v *)

(* open Genlex

let lexer = make_lexer ["+";"-";"*";"/"; "("; ")"]

let list_of_stream strm =
let rec listrec acc = parser
  [< 't ; strm >] -> listrec (t::acc) strm
| [< >] -> List.rev acc
in listrec [] strm

let pleft f sep =
let rec paux v1 = parser
  [< op = sep ; v2 = f ; rv = paux (op v1 v2) >] -> rv
| [< >] -> v1
in parser
  [< v = f ; rv = paux v >] -> rv


let additives = parser
  [< 'Kwd"+" >] -> (fun x y -> x + y)
| [< 'Kwd"-" >] -> (fun x y -> x - y)

let multiplicatives = parser
  [< 'Kwd"*" >] -> (fun x y -> x * y)
| [< 'Kwd"/" >] -> (fun x y -> x / y)


let rec expr strm = expr1 strm
and expr1 = parser
  [< rv = pleft expr2 additives >] -> rv

and expr2 = parser
  [< rv = pleft expr3 multiplicatives >] -> rv

and expr3 = parser
  [< 'Int n >] -> n
| [< 'Kwd"(" ; e = expr1 ; 'Kwd")" >] -> e;;

print_endline ({| 1 + 1 |} |> Stream.of_string |> lexer |> expr |> string_of_int);; *)

let quotexpander s =
  if String.sub s 0 1 = "|" && String.sub s (String.length s - 1) 1 = "|" then
    "secondary_parser \""^
    (String.escaped (String.sub s 1 (String.length s - 2)))^"\""
  else "default_parser \""^(String.escaped s)^"\"";;

Quotation.add "" (Quotation.ExStr (fun x -> quotexpander));;

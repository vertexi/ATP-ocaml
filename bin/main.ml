(* let () = print_endline "Hello, World!!" *)

type expression =
  | Var of string
  | Const of int
  | Add of expression * expression
  | Mul of expression * expression

let temp = Add (Mul (Const 2, Var "x"), Var "y")

let simplify1 expr =
  match expr with
  | Add (Const m, Const n) -> Const (m + n)
  | Mul (Const m, Const n) -> Const (m * n)
  | Add (Const 0, x) -> x
  | Add (x, Const 0) -> x
  | Mul (Const 0, _) -> Const 0
  | Mul (_, Const 0) -> Const 0
  | Mul (Const 1, x) -> x
  | Mul (x, Const 1) -> x
  | _ -> expr

let rec simplify expr =
  match expr with
  | Add (e1, e2) -> simplify1 (Add (simplify e1, simplify e2))
  | Mul (e1, e2) -> simplify1 (Mul (simplify e1, simplify e2))
  | _ -> simplify1 expr

let e = Add (Const 12, Mul (Const 3, Add (Const 1, Mul (Const 0, Var "x"))))

let rec explode s =
  match s with
  | "" -> []
  | _ -> String.sub s 0 1 :: explode (String.sub s 1 (String.length s - 1))

let rec mem c s =
  match s with [] -> false | c_ :: cs -> if c = c_ then true else mem c cs

let matches s =
  let chars = explode s in
  fun c -> mem c chars

let space = matches " \t\n\r"
and punctuation = matches "()[]{},"
and symbolic = matches "~`!@#$%^&*-+=|\\:;<>.?/"
and numeric = matches "0123456789"

and alphanumeric =
  matches "abcdefghijklmnopqrstuvwxyz_'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"

let rec lexwhile prop inp =
  match inp with
  | c :: cs when prop c ->
      let tok, rest = lexwhile prop cs in
      (c ^ tok, rest)
  | _ -> ("", inp)

let test x = match x with x when x > 10 -> 10 | _ -> x

let first_l l =
  match l with l_ :: _ -> l_ | [] -> raise @@ Failure "first: empty l"

(** get the first element from tuple*)
let first_t t = match t with first, _ -> first

let second_t t = match t with _, second -> second

let rec index l i =
  if i < 1 then raise @@ Failure "index: less than 1"
  else
    match (i, l) with
    | _, [] -> raise @@ Failure "index: empty l"
    | 1, _ -> first_l l
    | _, _ :: ls -> index ls (i - 1)

let rec range a b = if a > b then [] else a :: range (a + 1) b
let ( -- ) a b = range a b


(** take char list and tokenize to token list *)
let rec lex inp =
  match second_t (lexwhile space inp) with
  | [] -> []
  | c :: cs ->
      let prop =
        if numeric c then numeric
        else if alphanumeric c then alphanumeric
        else if symbolic c then symbolic
        else fun _ -> false
      in
      let tok, rest = lexwhile prop cs in
      (c ^ tok) :: lex rest

let rec forall f xs =
  match xs with x :: [] -> f x | x :: xs_ -> f x && forall f xs_ | [] -> false


(** parse algebra expression
the grammar BNF-form:
expression -> juxta
              juxta + expression
juxta      -> production
              production " " juxta
production -> atom
              atom * production
atom       -> (expression)
              Const
              Val

a -> a
     b "s" a
b s (b s (b s (b s (a))))
the infix operator is right-associative in the BNF-form

the operators form BNF is increasing poriority, + " " *.
So atom parse first then productions then summations.

Perhaps there is another way to implement juxtapostion --
modify the lex to produce " " operator
*)
let rec parse_expression i =
  match parse_juxta i with
  | e1, "+" :: i1 ->
      let e2, i2 = parse_expression i1 in
      (Add (e1, e2), i2)
  | e1, i1 -> (e1, i1)

and parse_juxta i =
  match parse_product i with
  | e1, [] -> (e1, [])
  | e1, i1 -> (
      match i1 |> first_l |> explode |> first_l with
      | c when alphanumeric c || c = "(" ->
          let e2, i2 = parse_juxta i1 in
          (Mul (e1, e2), i2)
      | _ -> (e1, i1))

and parse_product i =
  match parse_atom i with
  | e1, "*" :: i1 ->
      let e2, i2 = parse_product i1 in
      (Mul (e1, e2), i2)
  | e1, i1 -> (e1, i1)

and parse_atom i =
  match i with
  | [] -> raise @@ Failure "parse empty string"
  | "(" :: is -> (
      let e1, i1 = parse_expression is in
      match i1 with
      | ")" :: rest -> (e1, rest)
      | _ -> raise @@ Failure "not bracket pair")
  | tok :: i1 ->
      if forall numeric (explode tok) then (Const (int_of_string tok), i1)
      else (Var tok, i1)

(*
(* debug from top level directives *)
#trace parse_atom;;
#trace parse_product;;
#trace parse_juxta;;
#trace parse_expression;;

#untrace parse_atom;;
#untrace parse_product;;
#untrace parse_expression;;
*)

let make_parser pfn s =
  match s |> explode |> lex |> pfn with
  | x, [] -> x
  | _ -> raise @@ Failure "unparse string exists"

let default_parser = make_parser parse_expression

(* 
original code from book

let rec parse_expression i =
  match parse_product i with
  | e1, "+" :: i1 ->
      let e2, i2 = parse_expression i1 in
      (Add (e1, e2), i2)
  | e1, i1 -> (e1, i1)

and parse_product i =
  match parse_atom i with
  | e1, "*" :: i1 ->
      let e2, i2 = parse_product i1 in
      (Mul (e1, e2), i2)
  | e1, i1 -> (e1, i1)

and parse_atom i =
  match i with
  | [] -> raise @@ Failure "parse empty string"
  | "(" :: is -> (
      let e1, i1 = parse_expression is in
      match i1 with
      | ")" :: rest -> (e1, rest)
      | _ -> raise @@ Failure "not bracket pair")
  | tok :: i1 ->
      if forall numeric (explode tok) then (Const (int_of_string tok), i1)
      else (Var tok, i1) *)

let rec string_of_exp e =
  match e with
  | Var s -> s
  | Const n -> string_of_int n
  | Add (e1, e2) -> "(" ^ string_of_exp e1 ^ " + " ^ string_of_exp e2 ^ ")"
  | Mul (e1, e2) -> "(" ^ string_of_exp e1 ^ " * " ^ string_of_exp e2 ^ ")"

let rec string_of_exp pr e =
  match e with
  | Var s -> s
  | Const n -> string_of_int n
  | Add (e1, e2) ->
      let str = string_of_exp 3 e1 ^ " + " ^ string_of_exp 2 e2 in
      if pr > 2 then "(" ^ str ^ ")" else str
  | Mul (e1, e2) ->
      let str = string_of_exp 5 e1 ^ " * " ^ string_of_exp 4 e2 in
      if pr > 4 then "(" ^ str ^ ")" else str

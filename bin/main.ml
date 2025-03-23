(* let () = print_endline "Hello, World!!" *)

type expression =
  | Var of string
  | Const of int
  | Add of expression * expression
  | Sub of expression * expression
  | Mul of expression * expression
  | Pow of expression * expression
  | Neg of expression

let temp = Add (Mul (Const 2, Var "x"), Var "y")

let rec simplify1 expr =
  match expr with
  | Add (Const m, Const n) -> Const (m + n)
  | Add (Const 0, x) -> x
  | Add (x, Const 0) -> x
  | Add (x1, x2) when x1 = Neg x2 || Neg x1 = x2 -> Const 0
  | Mul (Const m, Const n) -> Const (m * n)
  | Mul (Const 0, _) -> Const 0
  | Mul (_, Const 0) -> Const 0
  | Mul (Const 1, x) -> x
  | Mul (x, Const 1) -> x
  | Mul (x1, x2) when x1 = x2 -> Pow(x1, Const 2)
  | Mul (x1, Pow(x2, e)) when x1 = x2 -> Pow(x1, simplify1 @@ Add(e, Const 1))
  | Sub (x1, x2) when x1 = x2 -> Const 0
  | Sub (x, Const 0) -> x
  | Sub (Const 0, x) -> Neg x
  | Pow (x, Const 1) -> x
  | Neg (Neg x) -> x
  | _ -> expr

let rec simplify expr =
  match expr with
  | Add (e1, e2) -> simplify1 (Add (simplify e1, simplify e2))
  | Mul (e1, e2) -> simplify1 (Mul (simplify e1, simplify e2))
  | Sub (e1, e2) -> simplify1 (Sub (simplify e1, simplify e2))
  | Pow (e1, e2) -> simplify1 (Pow (simplify e1, simplify e2))
  | Neg e -> simplify1 (Neg (simplify e))
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
(* parse algebra expression the grammar BNF-form:
expression -> sub
            | sub + expression
sub        -> juxta
            | sub - juxta
juxta      -> production
            | production " " juxta
production -> pow
            | pow * production
pow        -> neg
            | neg ^ pow
neg        -> atom
            | - neg
atom       -> (expression)
            | Const
            | Val

a -> a
    | b "s" a
b s (b s (b s (b s (a))))
the infix operator is right-associative in the BNF-form

a -> a
    | a "s" b
(((a s b) s b) s b) s b
the infix operator is left-associative in the BNF-form

left-associative is like lex process 'longest possible pattern'

the operators form BNF is increasing poriority, + - " " * ^ (). So atom parse first
then productions then summations.

Perhaps there is another way to implement juxtapostion -- modify the lex to
produce " " operator *)
[@@ocamlformat "wrap-comments=false"]

let rec parse_expression i =
  match parse_sub i with
  | e1, "+" :: i1 ->
      let e2, i2 = parse_expression i1 in
      (Add (e1, e2), i2)
  | e1, "-" :: i1 ->
      let e2, i2 = parse_juxta i1 in
      (Sub (e1, e2), i2)
  | e1, i1 -> (e1, i1)

and parse_sub_i i =
  match i with
  | e1, "-" :: tokens_ ->
      let e2, i2 = parse_juxta tokens_ in
      parse_sub_i (Sub (e1, e2), i2)
  | e1, i1 -> (e1, i1)

and parse_sub i = parse_sub_i @@ parse_juxta i

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
  match parse_pow i with
  | e1, "*" :: i1 ->
      let e2, i2 = parse_product i1 in
      (Mul (e1, e2), i2)
  | e1, i1 -> (e1, i1)

and parse_pow i =
  match parse_neg i with
  | e1, "^" :: i1 ->
      let e2, i2 = parse_pow i1 in
      (Pow (e1, e2), i2)
  | e1, i1 -> (e1, i1)

and parse_neg i =
  match parse_atom i with
  | Var "-", i1 ->
      let e2, i2 = parse_neg i1 in
      (Neg e2, i2)
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
  | Sub (e1, e2) -> "(" ^ string_of_exp e1 ^ " - " ^ string_of_exp e2 ^ ")"
  | Mul (e1, e2) -> "(" ^ string_of_exp e1 ^ " * " ^ string_of_exp e2 ^ ")"
  | Pow (e1, e2) -> "(" ^ string_of_exp e1 ^ " ^ " ^ string_of_exp e2 ^ ")"
  | Neg e1 -> "(-" ^ string_of_exp e1 ^ ")"

let rec string_of_exp pr e =
  match e with
  | Var s -> s
  | Const n -> string_of_int n
  | Add (e1, e2) ->
      let str = string_of_exp 3 e1 ^ " + " ^ string_of_exp 2 e2 in
      if pr > 2 then "(" ^ str ^ ")" else str
  | Sub (e1, e2) ->
      let str = string_of_exp 4 e1 ^ " - " ^ string_of_exp 5 e2 in
      if pr > 4 then "(" ^ str ^ ")" else str
  | Mul (e1, e2) ->
      let str = string_of_exp 7 e1 ^ " * " ^ string_of_exp 6 e2 in
      if pr > 6 then "(" ^ str ^ ")" else str
  | Pow (e1, e2) ->
      let str = string_of_exp 9 e1 ^ " ^ " ^ string_of_exp 8 e2 in
      if pr > 8 then "(" ^ str ^ ")" else str
  | Neg e1 -> (
      match e1 with
      | Var _ | Neg _ -> "-" ^ string_of_exp 0 e1 ^ ""
      | _ -> "-(" ^ string_of_exp 0 e1 ^ ")")

(*
the most complicated test case:
string_of_exp @@ default_parser "b5^(10 kk2) + x_1 - (y_2 - z) k (1 - 3 x + (2y^xy)^ -bb - -b -z -y -k -c -( b - -d) k)";;
*)

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
  | Add (x2, Mul (Const n, x1)) when x1 = x2 ->
      simplify1 @@ Mul (x1, Const (n + 1))
  | Add (Add (x1, x2), x3) -> simplify1 @@ Add (x1, simplify1 @@ Add (x2, x3))
  | Mul (Const m, Const n) -> Const (m * n)
  | Mul (Const 0, _) -> Const 0
  | Mul (_, Const 0) -> Const 0
  | Mul (Const 1, x) -> x
  | Mul (x, Const 1) -> x
  | Mul (x, Const n) -> Mul (Const n, simplify1 @@ x)
  | Mul (Add (x1, x2), Add (x3, x4)) ->
      simplify1 @@ Add (Mul (x1, Add (x3, x4)), Mul (x2, Add (x3, x4)))
  | Mul (x1, Add (x2, x3)) -> simplify1 @@ Add (Mul (x1, x2), Mul (x1, x3))
  | Mul (x1, x2) when x1 = x2 -> Pow (x1, Const 2)
  | Mul (x1, Pow (x2, e)) when x1 = x2 -> Pow (x1, simplify1 @@ Add (e, Const 1))
  | Sub (x, Const 0) -> x
  | Sub (Const 0, x) -> Neg x
  | Sub (x1, x2) when x1 = x2 -> Const 0
  | Sub (x1, x2) -> Add (x1, Neg x2)
  | Pow (x, Const 1) -> x
  | Neg (Const 0) -> Const 0
  | Neg (Const n) -> Const (-1 * n)
  | Neg (Neg x) -> simplify1 x
  | _ -> expr

let rec simplify expr =
  let expr_ =
    match expr with
    | Add (e1, e2) -> simplify1 (Add (e1, e2))
    | Mul (e1, e2) -> simplify1 (Mul (e1, e2))
    | Sub (e1, e2) -> simplify1 (Sub (e1, e2))
    | Pow (e1, e2) -> simplify1 (Pow (e1, e2))
    | Neg e -> simplify1 (Neg e)
    | Const n -> Const n
    | Var v -> Var v
  in
  match expr_ with
  | Add (e1, e2) -> simplify1 (Add (simplify e1, simplify e2))
  | Mul (e1, e2) -> simplify1 (Mul (simplify e1, simplify e2))
  | Sub (e1, e2) -> simplify1 (Sub (simplify e1, simplify e2))
  | Pow (e1, e2) -> simplify1 (Pow (simplify e1, simplify e2))
  | Neg e -> simplify1 (Neg (simplify e))
  | Const n -> Const n
  | Var v -> Var v

(* complicated simplify cases:
simplify  @@ default_parser "(x*x*x - x^3) - (x*x*x - x^3)";;
simplify  @@ default_parser "(x*x*x - x^3)*0";;
simplify  @@ default_parser "x - - - - - x";;
*)

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

let tail_l l =
  match l with _ :: ls -> ls | [] -> raise @@ Failure "tail_l: empty l"

let hl l = first_l l
let tl l = tail_l l

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

let make_parser_debug pfn s =
  match s |> explode |> lex |> pfn with x, [] -> (x, []) | x, l -> (x, l)

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

type 'a formula =
  | False
  | True
  | Atom of 'a
  | Not of 'a formula
  | And of 'a formula * 'a formula
  | Or of 'a formula * 'a formula
  | Imp of 'a formula * 'a formula
  | Iff of 'a formula * 'a formula
  | Forall of string * 'a formula
  | Exists of string * 'a formula

(* ------------------------------------------------------------------------- *)
(* General parsing of iterated infixes.                                      *)
(* ------------------------------------------------------------------------- *)

type prop = P of string

let pname (P s) = s

(* general infix operator parse constructor *)
let rec parse_ginfix opsym opupdate sof
    (subparser : string list -> prop formula * string list) (inp : string list)
    =
  let e1, inp1 = subparser inp in
  if inp1 <> [] && hl inp1 = opsym then
    parse_ginfix opsym opupdate (opupdate sof e1) subparser (tl inp1)
  else (sof e1, inp1)

let parse_left_infix opsym opcon =
  parse_ginfix opsym (fun f e1 e2 -> opcon (f e1, e2)) (fun x -> x)

let parse_right_infix (opsym : string)
    (opcon : prop formula * prop formula -> prop formula) =
  parse_ginfix opsym (fun f e1 e2 -> f (opcon (e1, e2))) (fun x -> x)

let parse_list opsym =
  parse_ginfix opsym (fun f e1 e2 -> f e1 @ [ e2 ]) (fun x -> [ x ])

let papply f (ast, rest) = (f ast, rest)
let nextin inp tok = inp <> [] && hl inp = tok

let parse_bracketed subparser cbra inp =
  let ast, rest = subparser inp in
  if nextin rest cbra then (ast, tl rest)
  else failwith "Closing bracket expected"

let rec parse_atomic_formula (ifn, afn) vs inp =
  match inp with
  | [] -> failwith "formula expected"
  | "false" :: rest -> (False, rest)
  | "true" :: rest -> (True, rest)
  | "(" :: rest -> (
      try ifn vs inp
      with Failure _ -> parse_bracketed (parse_formula (ifn, afn) vs) ")" rest)
  | "~" :: rest ->
      papply (fun p -> Not p) (parse_atomic_formula (ifn, afn) vs rest)
  | "forall" :: x :: rest ->
      parse_quant (ifn, afn) (x :: vs) (fun (x, p) -> Forall (x, p)) x rest
  | "exists" :: x :: rest ->
      parse_quant (ifn, afn) (x :: vs) (fun (x, p) -> Exists (x, p)) x rest
  | _ -> afn vs inp

and parse_quant (ifn, afn) vs qcon x inp =
  match inp with
  | [] -> failwith "Body of quantified term expected"
  | y :: rest ->
      papply
        (fun fm -> qcon (x, fm))
        (if y = "." then parse_formula (ifn, afn) vs rest
         else parse_quant (ifn, afn) (y :: vs) qcon y rest)

and parse_formula (ifn, afn) vs inp =
  parse_right_infix "<=>"
    (fun (p, q) -> Iff (p, q))
    (parse_right_infix "==>"
       (fun (p, q) -> Imp (p, q))
       (parse_right_infix "\\/"
          (fun (p, q) -> Or (p, q))
          (parse_right_infix "/\\"
             (fun (p, q) -> And (p, q))
             (parse_atomic_formula (ifn, afn) vs))))
    inp

let parse_propvar vs inp =
  match inp with
  | p :: oinp when p <> "(" -> (Atom (P p), oinp)
  | _ -> failwith "parse_propvar"

let parse_prop_formula =
  make_parser (parse_formula ((fun _ _ -> failwith ""), parse_propvar) [])

let default_parser = parse_prop_formula

open Format

let bracket p n f x y =
  if p then print_string "(" else ();
  open_box n;
  f x y;
  close_box ();
  if p then print_string ")" else ()

let rec strip_quant fm =
  match fm with
  | Forall (x, (Forall (y, p) as yp)) | Exists (x, (Exists (y, p) as yp)) ->
      let xs, q = strip_quant yp in
      (x :: xs, q)
  | Forall (x, p) | Exists (x, p) -> ([ x ], p)
  | _ -> ([], fm)

let rec do_list f l =
  match l with
  | [] -> ()
  | h :: t ->
      f h;
      do_list f t

let print_formula pfn =
  let rec print_formula pr fm =
    match fm with
    | False -> print_string "false"
    | True -> print_string "true"
    | Atom pargs -> pfn pr pargs
    | Not p -> bracket (pr > 10) 1 (print_prefix 10) "~" p
    | And (p, q) -> bracket (pr > 8) 0 (print_infix 8 "/\\") p q
    | Or (p, q) -> bracket (pr > 6) 0 (print_infix 6 "\\/") p q
    | Imp (p, q) -> bracket (pr > 4) 0 (print_infix 4 "==>") p q
    | Iff (p, q) -> bracket (pr > 2) 0 (print_infix 2 "<=>") p q
    | Forall (x, p) -> bracket (pr > 0) 2 print_qnt "forall" (strip_quant fm)
    | Exists (x, p) -> bracket (pr > 0) 2 print_qnt "exists" (strip_quant fm)
  and print_qnt qname (bvs, bod) =
    print_string qname;
    do_list
      (fun v ->
        print_string " ";
        print_string v)
      bvs;
    print_string ".";
    print_space ();
    open_box 0;
    print_formula 0 bod;
    close_box ()
  and print_prefix newpr sym p =
    print_string sym;
    print_formula (newpr + 1) p
  and print_infix newpr sym p q =
    print_formula (newpr + 1) p;
    print_string (" " ^ sym);
    print_space ();
    print_formula newpr q
  in
  print_formula 0

let print_qformula pfn fm =
  open_box 0;
  print_string "<<";
  open_box 0;
  print_formula pfn fm;
  close_box ();
  print_string ">>";
  close_box ()

let mk_and p q = And (p, q)
and mk_or p q = Or (p, q)
and mk_imp p q = Imp (p, q)
and mk_iff p q = Iff (p, q)
and mk_forall x p = Forall (x, p)
and mk_exists x p = Exists (x, p)

let print_propvar prec p = print_string (pname p)
let print_prop_formula = print_qformula print_propvar

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

let parse_algebra = make_parser parse_expression
let default_parser = parse_algebra

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
;;

(*
the most complicated test case:
string_of_exp @@ default_parser "b5^(10 kk2) + x_1 - (y_2 - z) k (1 - 3 x + (2y^xy)^ -bb - -b -z -y -k -c -( b - -d) k)";;
*)

(
  string_of_exp 0
    (
      parse_algebra "b5^(10 kk2) + x_1 - (y_2 - z) k (1 - 3 x + (2y^xy)^ -bb - -b -z -y -k -c -( b - -d) k)"
    )
    |> print_endline
) [@ocamlformat "disable"]
;;

parse_algebra "b5^(10 kk2) + x_1 - (y_2 - z) k (1 - 3 x + (2y^xy)^ -bb - -b -z -y -k -c -(b - -d) k)" [@ocamlformat "disable"]

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

let parse_propvar _ inp =
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
  | Forall (x, (Forall (_, _) as yp)) | Exists (x, (Exists (_, _) as yp)) ->
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
    | Forall (_, _) -> bracket (pr > 0) 2 print_qnt "forall" (strip_quant fm)
    | Exists (_, _) -> bracket (pr > 0) 2 print_qnt "exists" (strip_quant fm)
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
  close_box ();
  print_newline ()

let print_propvar _ p = print_string (pname p)
let print_prop_formula = print_qformula print_propvar

let mk_and p q = And (p, q)
and mk_or p q = Or (p, q)
and mk_imp p q = Imp (p, q)
and mk_iff p q = Iff (p, q)
and mk_forall x p = Forall (x, p)
and mk_exists x p = Exists (x, p)

let dest_iff fm =
  match fm with Iff (p, q) -> (p, q) | _ -> failwith "dest_iff"

let dest_and fm =
  match fm with And (p, q) -> (p, q) | _ -> failwith "dest_iff"

let rec dest_conjuncts fm =
  match fm with
  | And (p, q) -> dest_conjuncts p @ dest_conjuncts q
  | _ -> [ fm ]

let dest_or fm = match fm with Or (p, q) -> (p, q) | _ -> failwith "dest_or"

let rec dest_disconjuncts fm =
  match fm with
  | Or (p, q) -> dest_disconjuncts p @ dest_disconjuncts q
  | _ -> [ fm ]

let dest_imp fm =
  match fm with Imp (p, q) -> (p, q) | _ -> failwith "dest_imp"

let antecedent fm = fst (dest_imp fm)
let consequent fm = snd (dest_imp fm)

let rec onatoms f fm =
  match fm with
  | Atom a -> f a
  | Not p -> Not (onatoms f p)
  | And (p, q) -> And (onatoms f p, onatoms f q)
  | Or (p, q) -> Or (onatoms f p, onatoms f q)
  | Imp (p, q) -> Imp (onatoms f p, onatoms f q)
  | Iff (p, q) -> Iff (onatoms f p, onatoms f q)
  | Forall (x, p) -> Forall (x, onatoms f p)
  | Exists (x, p) -> Exists (x, onatoms f p)
  | _ -> fm

let rec overatoms f fm b =
  match fm with
  | Atom a -> f a b
  | Not p -> overatoms f p b
  | And (p, q) | Or (p, q) | Imp (p, q) | Iff (p, q) ->
      overatoms f p (overatoms f q b)
  | Forall (_, p) | Exists (_, p) -> overatoms f p b
  | _ -> b

let rec uniq l =
  match l with
  | x :: (y :: _ as t) ->
      let t' = uniq t in
      if compare x y = 0 then t' else if t' == t then l else x :: t'
  | _ -> l

let map f =
  let rec mapf l =
    match l with
    | [] -> []
    | x :: t ->
        let y = f x in
        y :: mapf t
  in
  mapf

let rec merge ord l1 l2 =
  match l1 with
  | [] -> l2
  | h1 :: t1 -> (
      match l2 with
      | [] -> l1
      | h2 :: t2 ->
          if ord h1 h2 then h1 :: merge ord t1 l2 else h2 :: merge ord l1 t2)

let sort ord =
  let rec mergepairs l1 l2 =
    match (l1, l2) with
    | [ s ], [] -> s
    | l, [] -> mergepairs [] l
    | l, [ s1 ] -> mergepairs (s1 :: l) []
    | l, s1 :: s2 :: ss -> mergepairs (merge ord s1 s2 :: l) ss
  in
  fun l -> if l = [] then [] else mergepairs [] (map (fun x -> [ x ]) l);;

let ss = sort ( < ) in ss [3;2;1];;

(* let setify =
  let rec canonical lis =
    match lis with
    | x :: (y :: _ as rest) -> compare x y < 0 && canonical rest
    | _ -> true
  in
  fun l ->
    if canonical l then l else uniq (sort (fun x y -> compare x y <= 0) l) *)

let setify x = List.sort_uniq (fun a b -> compare a b) x
let atom_union f fm = setify (overatoms (fun a b -> f a @ b) fm [])

let rec eval fm v =
  match fm with
  | True -> true
  | False -> false
  | Atom p -> v p
  | Not p -> not (eval p v)
  | And (p, q) -> eval p v && eval q v
  | Or (p, q) -> eval p v || eval q v
  | Imp (p, q) -> ( match eval p v with false -> true | true -> eval q v)
  | Iff (p, q) -> eval p v = eval q v
  | _ -> failwith "eval: not implemented"
;;

eval (default_parser "p /\\ q ==> q /\\ r") (fun fm ->
    match fm with
    | P "p" -> true
    | P "q" -> false
    | P "r" -> true
    | _ -> failwith "unvalue")

let atoms p = atom_union (fun x -> [ x ]) p;;

"p /\\ q \\/ s ==> ~ p \\/ (r <=> s)" |> parse_prop_formula |> atoms

let rec onallvaluations evalformula v ats =
  match ats with
  | [] -> evalformula v
  | p :: ps ->
      let v' t q = if q = p then t else v q in
      onallvaluations evalformula (v' false) ps
      && onallvaluations evalformula (v' true) ps

let rec itlist f l b = match l with [] -> b | h :: t -> f h (itlist f t b)

let print_truthtable fm =
  print_newline ();
  fm |> print_prop_formula;
  let ats = atoms fm in
  let width = itlist (fun a b -> max (String.length @@ pname a) b) ats 5 + 1 in
  let fixw s = s ^ String.make (width - String.length s) ' ' in
  let truthstring p = fixw (if p then "true" else "false") in
  let mk_row v =
    let lis = map (fun x -> truthstring (v x)) ats
    and ans = truthstring (eval fm v) in
    print_string (itlist ( ^ ) lis ("| " ^ ans));
    print_newline ();
    true
  in
  let separator = String.make ((width * List.length ats) + 9) '-' in
  print_string (itlist (fun s t -> fixw (pname s) ^ t) ats "| formula");
  print_newline ();
  print_string separator;
  print_newline ();
  let _ = onallvaluations mk_row (fun _ -> false) ats in
  print_string separator;
  print_newline ();
  print_newline ();;

(* "p /\\ q" |> parse_prop_formula |> print_truthtable;; *)

(* tautology *)
(* "p /\\ q ==> p \\/ q" |> parse_prop_formula |> print_truthtable;; *)
"((p ==> q) ==> p) ==> p" |> parse_prop_formula |> print_truthtable;;

let tautology fm = onallvaluations (eval fm) (fun _ -> false) (atoms fm)
let unsatisfiable fm = tautology @@ Not fm
let satisfiable fm = not @@ unsatisfiable fm;;

(* unsatifiable example *)
"(p /\\ q) /\\ (~p /\\ q)" |> parse_prop_formula |> unsatisfiable

type ('a, 'b) func =
  | Empty
  | Leaf of int * ('a * 'b) list
  | Branch of int * int * ('a, 'b) func * ('a, 'b) func

let undefined = Empty

let applyd =
  let rec apply_listd l d x =
    match l with
    | (a, b) :: t ->
        let c = compare x a in
        if c = 0 then b else if c > 0 then apply_listd t d x else d x
    | [] -> d x
  in
  fun f d x ->
    let k = Hashtbl.hash x in
    let rec look t =
      match t with
      | Leaf (h, l) when h = k -> apply_listd l d x
      | Branch (p, b, l, r) when k lxor p land (b - 1) = 0 ->
          look (if k land b = 0 then l else r)
      | _ -> d x
    in
    look f

let apply f = applyd f (fun _ -> failwith "apply")
let tryapplyd f a d = applyd f (fun _ -> d) a
let tryapplyl f x = tryapplyd f x []
let psubst subfn = onatoms (fun p -> tryapplyd subfn p (Atom p))

let ( |-> ), combine =
  let newbranch p1 t1 p2 t2 =
    let zp = p1 lxor p2 in
    let b = zp land -zp in
    let p = p1 land (b - 1) in
    if p1 land b = 0 then Branch (p, b, t1, t2) else Branch (p, b, t2, t1)
  in
  let rec define_list ((x, _) as xy) l =
    match l with
    | ((a, _) as ab) :: t ->
        let c = compare x a in
        if c = 0 then xy :: t
        else if c < 0 then xy :: l
        else ab :: define_list xy t
    | [] -> [ xy ]
  and combine_list op z l1 l2 =
    match (l1, l2) with
    | [], _ -> l2
    | _, [] -> l1
    | ((x1, y1) as xy1) :: t1, ((x2, y2) as xy2) :: t2 ->
        let c = compare x1 x2 in
        if c < 0 then xy1 :: combine_list op z t1 l2
        else if c > 0 then xy2 :: combine_list op z l1 t2
        else
          let y = op y1 y2 and l = combine_list op z t1 t2 in
          if z y then l else (x1, y) :: l
  in
  let ( |-> ) x y =
    let k = Hashtbl.hash x in
    let rec upd t =
      match t with
      | Empty -> Leaf (k, [ (x, y) ])
      | Leaf (h, l) ->
          if h = k then Leaf (h, define_list (x, y) l)
          else newbranch h t k (Leaf (k, [ (x, y) ]))
      | Branch (p, b, l, r) ->
          if k land (b - 1) <> p then newbranch p t k (Leaf (k, [ (x, y) ]))
          else if k land b = 0 then Branch (p, b, upd l, r)
          else Branch (p, b, l, upd r)
    in
    upd
  in
  let rec combine op z t1 t2 =
    match (t1, t2) with
    | Empty, _ -> t2
    | _, Empty -> t1
    | Leaf (h1, l1), Leaf (h2, l2) ->
        if h1 = h2 then
          let l = combine_list op z l1 l2 in
          if l = [] then Empty else Leaf (h1, l)
        else newbranch h1 t1 h2 t2
    | (Leaf (k, _) as lf), (Branch (p, b, l, r) as br) ->
        if k land (b - 1) = p then
          if k land b = 0 then
            match combine op z lf l with
            | Empty -> r
            | l' -> Branch (p, b, l', r)
          else
            match combine op z lf r with
            | Empty -> l
            | r' -> Branch (p, b, l, r')
        else newbranch k lf p br
    | (Branch (p, b, l, r) as br), (Leaf (k, _) as lf) ->
        if k land (b - 1) = p then
          if k land b = 0 then
            match combine op z l lf with
            | Empty -> r
            | l' -> Branch (p, b, l', r)
          else
            match combine op z r lf with
            | Empty -> l
            | r' -> Branch (p, b, l, r')
        else newbranch p br k lf
    | Branch (p1, b1, l1, r1), Branch (p2, b2, l2, r2) ->
        if b1 < b2 then
          if p2 land (b1 - 1) <> p1 then newbranch p1 t1 p2 t2
          else if p2 land b1 = 0 then
            match combine op z l1 t2 with
            | Empty -> r1
            | l -> Branch (p1, b1, l, r1)
          else
            match combine op z r1 t2 with
            | Empty -> l1
            | r -> Branch (p1, b1, l1, r)
        else if b2 < b1 then
          if p1 land (b2 - 1) <> p2 then newbranch p1 t1 p2 t2
          else if p1 land b2 = 0 then
            match combine op z t1 l2 with
            | Empty -> r2
            | l -> Branch (p2, b2, l, r2)
          else
            match combine op z t1 r2 with
            | Empty -> l2
            | r -> Branch (p2, b2, l2, r)
        else if p1 = p2 then
          match (combine op z l1 l2, combine op z r1 r2) with
          | Empty, r -> r
          | l, Empty -> l
          | l, r -> Branch (p1, b1, l, r)
        else newbranch p1 t1 p2 t2
  in
  (( |-> ), combine)

let ( |=> ) = fun x y -> (x |-> y) undefined
let kk = fun x y -> (x, y);;

psubst
  (P "p" |=> parse_prop_formula "p /\\ q")
  ("p /\\ q /\\ p /\\ q" |> parse_prop_formula)
|> print_prop_formula
;;

print_truthtable @@ parse_prop_formula "p <=> (q <=> r) <=> (p <=> q) <=> r";;

forall tautology
  (map parse_prop_formula
     [
       "true <=> false ==> false";
       "~p <=> p ==> false";
       "p /\\ q <=> (p ==> q ==> false) ==> false";
       "p \\/ q <=> (p ==> false) ==> q";
       "(p <=> q) <=> ((p ==> q) ==> (q ==> p) ==> false) ==> false";
     ])

let rec dual fm =
  match fm with
  | True -> False
  | False -> True
  | Not p -> Not (dual p)
  | And (p, q) -> Or (dual p, dual q)
  | Or (p, q) -> And (dual p, dual q)
  | Atom _ -> fm
  | _ -> failwith "dual: contains ==> or <=> is illegal"
;;

"p /\\ q" |> parse_prop_formula |> dual |> print_prop_formula;;

let psimplify1 fm =
  match fm with
  | Not False -> True
  | Not True -> False
  | Not (Not p) -> p
  | And (_, False) | And (False, _) -> False
  | And (p, True) | And (True, p) -> p
  | Or (p, False) | Or (False, p) -> p
  | Or (_, True) | Or (True, _) -> True
  | Imp (False, _) | Imp (_, True) -> True
  | Imp (True, p) -> p
  | Imp (p, False) -> Not p
  | Iff (True, p) | Iff (p, True) -> p
  | Iff (False, p) | Iff (p, False) -> Not p
  | _ -> fm

let rec psimplify fm =
  match fm with
  | Not p -> psimplify1 (Not (psimplify p))
  | And (p, q) -> psimplify1 (And (psimplify p, psimplify q))
  | Or (p, q) -> psimplify1 (Or (psimplify p, psimplify q))
  | Imp (p, q) -> psimplify1 (Imp (psimplify p, psimplify q))
  | Iff (p, q) -> psimplify1 (Iff (psimplify p, psimplify q))
  | _ -> fm
;;

print_prop_formula @@ psimplify
@@ parse_prop_formula "(true ==> (x <=> false)) ==> ~(y \\/ false /\\ z)"
;;

print_prop_formula @@ psimplify
@@ parse_prop_formula "((x ==> y) ==> true \\/ ~false)"

let negative = function Not Atom _ -> true | _ -> false
let positive lit = not (negative lit)
let negate = function Not p -> p | p -> Not p;;

let rec nnf fm =
  match fm with
  | True -> True
  | False -> False
  | Atom p -> Atom p
  | And (p, q) -> And (nnf p , nnf q)
  | Or (p, q) -> Or (nnf p , nnf q)
  | Imp (p, q) -> Or (nnf (Not p), nnf q)
  | Iff (p, q) -> Or (And (nnf p, nnf q), And (nnf (Not p), nnf (Not q)))
  | Not (Not p) -> nnf p
  | Not (And (p, q)) -> Or (nnf (Not p), nnf (Not q))
  | Not (Or (p, q)) -> And (nnf (Not p), nnf (Not q))
  | Not (Imp (p, q)) -> And (nnf p, nnf (Not q))
  | Not (Iff (p, q)) -> And (Or (nnf (Not p), nnf (Not q)), Or (nnf p, nnf q))
  | Not True -> False
  | Not False -> True
  | Not (Atom p) -> Not (Atom p)
  | _ -> print_prop_formula fm; failwith "not implement in nnf"

let nnf fm = nnf(psimplify fm);;

print_newline ();
print_prop_formula @@ nnf @@ parse_prop_formula @@ "(p <=> q) <=> ~(r ==> s)";;
let fm = parse_prop_formula @@ "(p <=> q) <=> ~(r ==> s)" in
  let pt x = match x with | true -> print_endline "true" | _ -> print_endline "false" in
  pt @@ tautology @@ (Iff (fm, nnf fm));;


let rec nenf fm =
  match fm with
  | True -> True
  | False -> False
  | Atom p -> Atom p
  | And (p, q) -> And (nenf p, nenf q)
  | Or (p, q) -> Or (nenf p, nenf q)
  | Imp (p, q) -> Or (Not (nenf p), nenf q)
  | Iff (p, q) -> Iff (nenf p, nenf q)
  | Not (Not p) -> nenf p
  | Not And (p, q) -> Or (nenf (Not p), nenf (Not q))
  | Not Or (p, q) -> And (nenf (Not p), nenf (Not q))
  | Not Imp (p, q) -> And (nenf p, nenf (Not q))
  | Not Iff (p, q) -> Iff (nenf (Not p), nenf q)
  | Not True -> False
  | Not False -> True
  | Not (Atom p) -> Not (Atom p)
  | _ -> print_prop_formula fm; failwith "not implement in nenf"

let nenf fm = nenf(psimplify fm);;

print_newline ();
print_prop_formula @@ nenf @@ parse_prop_formula @@ "(p <=> q) <=> ~(r ==> s)";;
let fm = parse_prop_formula @@ "(p <=> q) <=> ~(r ==> s)" in
  let pt x = match x with | true -> print_endline "true" | _ -> print_endline "false" in
  pt @@ tautology @@ (Iff (fm, nenf fm));;

(* <<p /\\ q ==> q /\\ r>> *)
let debugging = true

#define debug(args) if debugging then print_endline args else ()

let () = print_endline ""
let () = print_endline "Hello, World!!"
let () = debug("Hello, World!!")
let () = print_endline ""

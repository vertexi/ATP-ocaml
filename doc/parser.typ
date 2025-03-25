// set up codly for code-block formatter
#import "@preview/codly:1.2.0": *
#import "@preview/codly-languages:0.1.1": *
#show: codly-init.with()
#codly(languages: codly-languages, zebra-fill: luma(247), display-icon: false, display-name: false)

// for BNF-form render
#import "@preview/simplebnf:0.1.1": *

// mitex for latex-like equation rendering
#import "@preview/mitex:0.2.4": *
#assert.eq(mitex-convert("\alpha x"), "alpha  x ")

#show heading: it => {
  if it.level == 1 {
    text(size: 24pt, it)
    par(leading: 1.5em)[#text(size: 0.0em)[#h(0.0em) placehold]]
  } else if it.level == 2 {
    text(size: 20pt, it)
    par(leading: 1.5em)[#text(size: 0.0em)[#h(0.0em) placehold]]
  } else if it.level == 3 {
    text(size: 18pt, it)
    par(leading: 1.5em)[#text(size: 0.0em)[#h(0.0em) placehold]]
  }
}
#set par(first-line-indent: 2em)
#show image: it => {
  align(center, it)
  v(-1.5em)
  par(leading: 1.5em)[#text(size: 0.0em)[#h(0.0em) placehold]]
}

// #show pagebreak: it => {
//   it
//   v(-1.5em)
//   par(leading: 1.5em)[#text(size: 0.0em)[#h(0.0em) placehold]]
// }

#show math.equation: it => {
  it
  if it.block == true {
    v(-1.5em)
    par(leading: 1.5em)[#text(size: 0.0em)[#h(0.0em) placehold]]
  }
}

#let mybnf(body) = {
  bnf(body)
  v(-1.5em)
  par(leading: 1.5em)[#text(size: 0.0em)[#h(0.0em) placehold]]
}

#show raw.where(block: true): it => {
  it
  v(-1.5em)
  par(leading: 1.5em)[#text(size: 0.0em)[#h(0.0em) placehold]]
}

#set page(paper: "a4", margin: 30pt)

#set text(size: 16pt)

= Notes

== Parser for propositional logic formular

The grammar tree:

#mybnf(
  Prod(
    $a' "formular"$,
    delim: $→$,
    annot: $bold(sans("type"))$,
    {
      Or[False][]
      Or[True][]
      Or[Atom][_a'_]
      Or[Not][_a' formular_]
      Or[And][_a' formular \* a' formular_]
      Or[Or][_a' formular \* a' formular_]
      Or[Imp][_a' formular \* a' formular_]
      Or[Iff][_a' formular \* a' formular_]
      Or[Forall][_string \* a' formular_]
      Or[Exists][_string \* a' formular_]
    },
  ),
)

Atom 构造子的参数是多态的，为了后续一阶逻辑做准备。但是，目前命题逻辑所设计的 Atom 仅为 prop 类型其构造子仅为 P 接受 string。所以此章可以认为 ```ocaml a' formular = prop formular```。

本章解析器只接受字符串组成的原子命题以及True、False布尔常量和布尔运算符组成的式子。如f(x)（原子命题中含有括号）、((x)/\\q)（原子命题中含有括号）不支持。

```ocaml
type prop = P of string
```

最底层的解析单元中，常含有`vs`参数，该参数为后续一阶逻辑使用，现在为`[]`。

`parse_propvar`接受token串，当第一个token不为"（"时，返回(Atom(P p), oinp)，即返回当前token为原子命题p，以及剩余token串。否则返回错误。

```ocaml
let parse_propvar vs inp =
  match inp with
  | p :: oinp when p <> "(" -> (Atom (P p), oinp)
  | _ -> failwith "parse_propvar"
```

下面的代码实现了一种较为通用的解析器，分别是通用解析器具体的实现`parse_ginfix`，左结合`parse_left_infix`和右结合`parse_right_infix`以及列表解析`parse_list`。

其中`opsym`都为诸如`<=>`、`==>`等二元操作符，`opupdate`与`sof`为重要的结合函数用来堆砌左右结合表达式，`sof`为组成表达式最终式子的函数，`opupdate`组合前序`sof`表达式函数与原子命题组成新的`sof`最终实现表达式树递归形成：

以左结合为例：

#no-codly[
  ```ocaml
  opupdate = (fun f e1 e2 -> opcon (f e1, e2))
  sof = (fun x -> x)
  ```
]

$
  "sof" &=> ("fun" x -> x)\
  ("opupdate" "sof" "e1") &=> ("fun" "e" -> "opcon" ("e1, e"))\
  ("opupdate" ("opupdate" "sof" "e1") "e1"') &=> ("fun" "e" -> "opcon" ("opcon" ("e1, e1"'), "e"))
$

下为右结合：

#no-codly[
  ```ocaml
  opupdate = (fun f e1 e2 -> f opcon (e1, e2))
  sof = (fun x -> x)
  ```
]

$
  "sof" &=> ("fun" x -> x)\
  ("opupdate" "sof" "e1") &=> ("fun" "e" -> "opcon" ("e1, e"))\
  ("opupdate" ("opupdate" "sof" "e1") "e1"') &=> ("fun" "e" -> "opcon" ("e1," "opcon" ("e1"', "e")))
$

sof 递归迭代形成的函数闭包内含有以前所有的原子命题组成的语法树，以及当前原子命题应处的位置。

当没有发现原子命题后面没有二元运算符后，就返回`(sof e1, inp1)`，表达式全部解析完成。

该解析器存在的bug为"p /\\ ="解析为"And(Atom (P "p"), Atom (P "="))"。即式子必须为原子命题和二元运算符结合。

```ocaml
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
```

解析括号的封闭性，在解析到原子命题时如遇括号，则调用`parse_bracketed`且配合`parse_formula`作为subparser解析子表达式。

```ocaml
let parse_bracketed subparser cbra inp =
  let ast, rest = subparser inp in
  if nextin rest cbra then (ast, tl rest)
  else failwith "Closing bracket expected"
```

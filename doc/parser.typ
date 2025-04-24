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

// for shadow box
#import "@preview/showybox:2.0.4": showybox

#import "@preview/quick-maths:0.2.1": shorthands

// #show: shorthands.with(
//   ($+-$, $plus.minus$),
//   ($|-$, math.tack),
//   ($<=$, math.arrow.l.double), // Replaces '≤'
// )

// remove cjk space in line break
#import "@preview/cjk-unbreak:0.1.0": *
#show: remove-cjk-break-space

#show heading.where(level: 1): it => text(size: 24pt, it)
#show heading.where(level: 2): it => text(size: 20pt, it)
#show heading.where(level: 3): it => text(size: 18pt, it)

#set par(first-line-indent: (amount: 2em, all: true))
#show image: it => {
  align(center, it)
}

#set page(paper: "a4", margin: 30pt, numbering: "1")

#set text(size: 14pt)

= Notes

== Parser for propositional logic formular

The grammar tree:

#bnf(
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

顶层的parser代码如下所示，在`parse_formula`中，不同的二元运算符按优先级从低到高嵌套，均为右结合。

```ocaml
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
```

下面的代码实现了对所有可能的布尔变量组合表示式求值，对`ats`原子变量表遍历，每个变量要么true，要么false，```ocaml let v' t q = if q = p then t else v q in```这个实现了原子变量集赋值函数。`onallvaluations`最终会执行$2^n$次，实现所有排列组合表达式求解。

```ocaml
let rec onallvaluations evalformula v ats =
  match ats with
  | [] -> evalformula v
  | p :: ps ->
      let v' t q = if q = p then t else v q in
      onallvaluations evalformula (v' false) ps && onallvaluations evalformula (v' true) ps
```

If p ⇒ q is a tautology, i.e. any valuation that satisfies p also satisfies q, we say that q is a logical consequence of p. If p ⇔ q is a tautology, i.e. a valuation satisfies p if and only if it satisfies q, we say that p and q are logically equivalent. Many important tautologies naturally take this latter form, and trivially if p is a tautology then so is p ⇔ T.

$p,q$逻辑等价就是$p<=>q$始终为真，即$p<=>q$为重言式。$p=>q$是重言式就意味着q是p的后果，两者有因果关系。

== About Kepler Conjucture Proof

=== Convex set

#image("figs/convex-set.svg")

如果$C subset.eq RR^n$，并且$forall x,y in C, {tau|tau = (1-lambda)x + lambda y, lambda in [0,1]} subset.eq C $，那么$C$是一个Convex set。

=== Convex Hull

最小能够包围住点集$C$的凸多边形就是凸包。凸包像是一根线紧绷围住点集。凸包多边形的边必须满足所有点集中的点在其一侧。

#image("figs/convex-hull.svg")

=== Voronoi Diagram

#image(width: 50%, "figs/voronoi.svg")

Voronoi 每个点是一个generater，生成一个Voronoi cell。两两相邻点之间画一条垂直平分线，去除不要的部分就是Voronoi cell。每一个 Voronoi cell 中的每一点都距离该 cell 所属的 generater 最近，换句话说 cell 中每一点和点集其它点的距离都比和 generater 的距离要长。
这一属性在发电站选址有用。

=== Delaunay Triangulation

Delaunay triangulation(DT) 中每一个三角的外接圆中不含有其它点。当外接圆上有四个点时，DT不唯一。2D DT求解可以转化为将每个点映射到三维空间求凸包，然后再投影到二维（忽略坐标z），映射办法为保持x,y坐标不变，令$z=|(x,y)|^2$，其凸包多边形应为三角形，否则意味着二维上多点共圆，DT不唯一。

DT 的性质是使三角化中三角形最小内角最大化。

Delaunay triangulation(DT) 和 Voronoi diagram(VD) 是对偶关系，意味着一个VD都有DT和其对应，并且构成VD的每一个元素都有与之对应的DT中的元素。

#grid(
  columns: 2,
  column-gutter: 5em,
  image("assets/VT.png"), image("assets/VT-DT.png"),
)

VT中的面变成点，边变成边，点变成面。

DT中每条边的垂直平分线的交点连成多边形就是VT，连接VT中每条边对应的两个点就是DT。


== Thue's Theoreom (Circle Packing)

#showybox(
  footer-style: (
    sep-thickness: 0pt,
    align: left,
    color: black,
  ),
  title: "Thue's Theoreom",
  // footer: [

  // ]
)[
  正六边形堆积是圆在平面上的最密堆积，其堆积密度为

  $ pi / sqrt(12) approx 0.9069 $
]

欲证明此定理先定义堆积密度。在 Thomas C.Hales @halesCannonballsHoneycombs 的文献中 Kepler 猜想的三维球在空间中的堆积密度定义为：

#showybox(
  footer-style: (
    sep-thickness: 0pt,
    align: left,
    color: black,
  ),
  title: "球堆积密度",
  // footer: [

  // ]
)[
  Density is the fraction of a region of space filled by the solid balls. If this region is *bounded*, this fraction is the ratio of the volume of the balls to the volume of the region. If any ball crosses the boundary of the region, only the part of the ball inside the region is used. If the region is *unbounded*, the density of the intersection of the region with a ball of radius R is calculated, and the density of the full region is defined as the lim sup over R.
]

密度->饱和堆积->构建平铺多边形->推导平铺多边形密度->求和

#bibliography("bib.bib", style: "gb-7714-2015-numeric")

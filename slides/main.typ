#import "@preview/touying:0.5.5": *
#import "@preview/cetz:0.3.1" as cetz: *
#import "@preview/pinit:0.2.2": *
#import "@preview/fletcher:0.5.5" as fletcher: diagram, node, edge
#import "/style.typ": my-theme, title-slide
#import "/macros.typ": *

#show: my-theme

#let diagram-alt = touying-reducer.with(
  reduce: fletcher.diagram, cover: fletcher.hide
)

#let node-common = (
  shape: fletcher.shapes.pill,
  inset: 0.5em,
  outset: 12pt,
)
#let node-c-act = (
  stroke: (paint: color.blue, dash: "solid"),
  ..node-common
)
#let node-c-pas = (
  stroke: (paint: color.blue, dash: "dashed"),
  ..node-common
)
#let node-s-act = (
  stroke: (paint: color.red, dash: "solid"),
  ..node-common
)
#let node-s-pas = (
  stroke: (paint: color.red, dash: "dashed"),
  ..node-common
)

#let edge-args = (
 label-side: center,
  crossing-fill: colors.neutral-lightest
)

#pdfpc.config(
  duration-minutes: 45,
  last-minutes: 5,
  note-font-size: 12,
  disable-markdown: false,
  default-transition: (
    type: "replace",
    duration-seconds: 0,
  ),
)


#title-slide()

#pdfpc.speaker-note(```md
  - program lang. semantics
  - math framework type theory
```)

= Program Semantics and Contextual Equivalence

#pdfpc.speaker-note(```md
  - semantics: giving meaning
  - quick intro
```)


== What is the Meaning of A Program?

#pdfpc.speaker-note(```md
  - you write a program; want to re
```)

#only("1-7")[
#v(2em)
    #bold[Actually, what is a program?]
#v(1fr)
]


#only("2", centering(image(width: 35%, "/img/program-stacking-1.excalidraw.png")))
#only("3", centering(image(width: 50%, "/img/program-stacking-2.excalidraw.png")))
#only("4", centering(image(width: 60%, "/img/program-stacking-3.excalidraw.png")))
#only("5", centering(image(width: 70%, "/img/program-stacking-4.excalidraw.png")))
#only("6", centering(image(width: 65%, "/img/program-stacking-5.excalidraw.png")))
#only("7", centering(image(width: 65%, "/img/program-stacking-6.excalidraw.png")))
#only("8")[
#v(1fr)
    #centering[#block(stroke: 1pt, outset: 8pt, radius: 8pt)[
        #set align(left)
    #puzzle Program fragment \
    #puzzle-ctx Context
  ]]
    #v(1fr)
  #centering[
    #bold[We are concerned with #alrt[program fragments]]
  ]
]
#v(1fr)

== Contextual Equivalence

#place(dx: 17.5cm, dy: 0.4cm)[#block(stroke: 1pt, outset: 8pt, radius: 8pt)[
        #set align(left)
    #puzzle Program fragment \
    #puzzle-ctx Context
]]
#v(1fr)

#bold[Contextual Equivalence]

Given $p, q in #puzzle$, we say that
#alrt[$quad quad "   " p approx_"ctx" q$]

when #alrt[for any context] $C in #puzzle-ctx$
$quad quad "eval"(C[p]) approx_"result" "eval"(C[q])$

#[ #set text(size: 0.6em)
(with $approx_"result"$ some suitable equivalence, usually cotermination)]

#pause
#v(1fr)

#bold[Problem]

There are infinitely many contexts... \
... even for _extremely_ simple programs \
Hence: working with contextual equivalence is hard

#v(1fr)

== Models and Full Abstraction

#place(dx: 17.5cm, dy: 0.4cm)[#block(stroke: 1pt, outset: 8pt, radius: 8pt)[
        #set align(left)
    #puzzle Program fragment \
    #puzzle-ctx Context
]]

#v(1fr)
#bold[Denotational Model]
$quad quad #pin(1)alrt(interp(bk(-)))#pin(2) cl #pin(3)#puzzle#pin(4) -> #pin(5)alrt(M)#pin(6)$
#pause
#pinit-point-from((1,2), pin-dy: 20pt, offset-dy: 50pt, offset-dx: 20pt, body-dy: 5pt, body-dx: -30pt)[
    interpret
]
#pinit-point-from((3,4), pin-dy: -20pt, offset-dy: -50pt, offset-dx: 20pt, body-dy: -30pt, body-dx: -35pt)[
    programs
]
#pinit-point-from((5,6), pin-dx: 10pt, pin-dy: 7pt, offset-dy: 30pt, offset-dx: 40pt, body-dy: 5pt, body-dx: -5pt)[
    denotations
]

#v(1.2fr)
#pause

#box($
& #bold[Soundness] & alrt(interp(bk(p))) alrt(approx_M) alrt(interp(bk(q))) => p approx_"ctx" q \ \
#pause
& #bold[Completeness] & alrt(interp(bk(p))) alrt(approx_M) alrt(interp(bk(q))) arrow.double.l p approx_"ctx" q \ \
#pause
& #bold[Full Abstraction] & quad alrt(interp(bk(p))) alrt(approx_M) alrt(interp(bk(q))) <=> p approx_"ctx" q $)
#v(0.6fr)
#pause
#centering[#bold[Our goal:] build a #alrt[sound] model called \ #alrt["Operational Game Semantics"] (OGS)]
#v(0.2fr)

== Contributions

#v(0.2fr)
#centering(image(height: 40%, "/img/repo-screen.png"))
#v(1fr)

- A #alrt[language-generic] OGS model
- Soundness proof w.r.t. a variant of contextual equivalence
- High-level #alrt[axiomatization of programming language]
- Everything #alrt[mechanized in Rocq]~#box(baseline: 2pt, image(height: 0.75em, "/img/rocq.svg")) with examples

#v(1fr)
#centering(txtt("https://lapin0t.github.io/ogs/Readme.html"))

#v(0.5fr)

== Mini-map

#v(-4em)
#centering(image(height: 116%, "/img/ogs-outline.excalidraw.png"))

= OGS in a Nutshell

== Game Semantics

#box(height: 100%, width: 54%, align(horizon)[
#bold[Idea] \
- Forget about the concrete context
- Focus on the #alrt[interaction] at the boundary
#v(2em)
#bold[Programs as strategies] \
#alrt[Programs] modelled as
#alrt[strategies] in a #alrt[dialogue]
with an unknown context
// TODO dialoguing??
])
#h(1fr)
#box(height: 100%, align(horizon)[
#block(h(0.92cm) + box(radius: 15pt, clip: true, image(width: 42%, "/img/Abelard_and_Heloise.jpeg")))
#set text(size: 10pt)
#h(2.5em)Héloïse & Abelard, shamelessly stolen from slides by P.-A. Melliès!
])

== OGS, Setting the Intuitions

#v(1fr)
$ blue(txtt("twice"))(f, x) := f(f(x)) $

#pause
#v(1fr)
#table(columns: 2, stroke: 0pt, row-gutter: 0.3em,
blue[Program], [--- I know the function #blue(txtt("twice"))],
pause + red[Context], [--- What is the output of $blue(txtt("twice"))(red(f), 5)$?#pin(1)],
pause + blue[Program], [--- What is the output of $red(f)(5)$?#pin(2)],
pause + red[Context], [--- The output is $4$#pin(3)
#pinit-point-from(2, pin-dy: -5pt, offset-dx: 50pt, offset-dy: -5pt, body-dy: 0pt, body-dx: -5.03em, thickness: 1pt,
    arrow-width: 8, arrow-height: 8,
    rect(stroke: (bottom: 1pt, right: 1pt), width: 5em, height: 1.4em))
],
pause + blue[Program], [--- What is the output of $red(f)(4)$?#pin(4)],
pause + red[Context], [--- The output is $2$#pin(5)
#pinit-point-from(4, pin-dy: -5pt, offset-dx: 50pt, offset-dy: -5pt, body-dy: 0pt, body-dx: -5.03em, thickness: 1pt,
    arrow-width: 8, arrow-height: 8,
    rect(stroke: (bottom: 1pt, right: 1pt), width: 5em, height: 1.4em))
],
pause + blue[Program], [--- The output is $2$#pin(6)
#pinit-point-from(1, pin-dy: -5pt, offset-dx: 50pt, offset-dy: -5pt, body-dy: 0pt, body-dx: -7.83em, thickness: 1pt,
    arrow-width: 8, arrow-height: 8,
    rect(stroke: (bottom: 1pt, right: 1pt), width: 7.8em, height: 7em))
])

#pause
#v(1fr)

#centering(bold[We never exchange function definitions!] + [ (only names)])

#v(1fr)

== Running Example: A Simply-Typed CBV $lambda$-calculus

#v(1fr)
#bold[Syntax]

#v(-1em)
$ & && && #h(15em) \
  & "Type"      && in.rev A, B && ::= #only("2")[#alrt[$stlc.bool$]] #only("3-4")[$stlc.bool$] #only("3")[$|$ #alrt[$A -> B$]] #only("4")[$| A -> B$] #only("1-2", hide($|$)) \
  & "Value"      && in.rev V, W && ::= x #only("1", hide($|$)) #only("2")[$|$ #alrt(stlc.tt) $|$ #alrt(stlc.ff)] #only("3-4")[$| stlc.tt | stlc.ff$] #only("3")[$|$ #alrt($stlc.lam x. P$)] #only("4")[$| stlc.lam x. P$] \
  & "Term"       && in.rev P, Q && ::= V #only("1-2", hide($|$)) #only("3")[$|$ #alrt($P Q$)] #only("4")[$| P Q$] #only("4")[$|$ #alrt($bot$)] #only("1-3", hide($| bot$))\
  & "Eval. Ctx." && in.rev E, F && ::= square #only("1-2", hide($|$)) #only("3")[$|$ #alrt($E V$) $|$ #alrt($P E$)] #only("4")[$| E V | P E$] $

#v(1fr)
#bold[Reduction]

#v(-1em)
$ #h(6em) & \
  E[P]                quad & ~> quad E[Q] quad quad "whenever " P ~> Q \
  #only("1-2", hide($(P)$))
  #only("3")[#alrt[$(stlc.lam x. P) V quad & ~> quad P[x |-> V]$]]
  #only("4")[$(stlc.lam x. P) V quad & ~> quad P[x |-> V]$] \
  #only("1-3", hide($bot$))
  #only("4")[#alrt($bot                 quad & ~> quad bot$)]
  $
#v(1fr)

== Identity function at #sym.space.quad #stlc.bool → #stlc.bool

#h(0.5fr) #blue[Program] #h(1fr) #red[Context] #h(0.45fr)
#align(center + horizon, diagram-alt(
  spacing: (8cm, 1.5cm),
  node((0,0), ..node-c-act)[$stlc.lam x.x$],
  node((1,0), ..node-s-pas)[$square stlc.tt$],
  pause,
  edge((0,0), (1,1), "->", bend: 10deg, ..edge-args)[#small($ogs.ret""(blue(f))$)],
  pause,
  node((0,1), ..node-c-pas)[$blue(f) |-> stlc.lam x.x$],
  pause,
  node((1,1), ..node-s-act)[$blue(f) bk(stlc.tt)$],
  pause,
  edge((1,1), (0,2), "->", bend: 10deg, ..edge-args)[#small($blue(f) dot ogs.call""(stlc.tt)$)],
  pause,
  node((0,2), ..node-c-act)[$(stlc.lam x.x) stlc.tt$],
  pause,
  edge((0,2), (0,3), "->", bend: -70deg, ..edge-args)[$tau$],
  node((0,3), ..node-c-act)[$stlc.tt$],
  pause,
  edge("->", bend: 10deg, ..edge-args)[#small($ogs.ret""(stlc.tt)$)],
  edge((1,1), (1,4), "-->", bend: 50deg)[],
  pause,
  node((1,4), ..node-s-act)[$"stop"[stlc.tt]$],
))



/*
---

#v(1fr)
#bold[Game Rules]

- The players exchange #alrt[function symbols] but do not disclose their definition
  to each other.
- Functions symbols are introduced by #alrt[calling] an existing symbol or
  by #alrt[returning].

#v(1fr)*/
/*
#bold[The Strategy]

- Evaluate the given term to a normal form $N$.
- When $N$ is a value $V$:
  - #alrt[Hide] any function inside $V$ using a fresh symbol.
  - #alrt[Return] it.
- When $N$ is a stuck call $E[x V]$
  - #alrt[Hide] any function inside $V$ using a fresh symbol.
  - #alrt[Call] $x$ with 

#v(1fr)

*/


== Decomposing Values

#let sact(..xs) = {
  blue(txtt("act(")) + xs.pos().join(",") + blue(txtt(")"))
}
#let spas(..xs) = {
  red(txtt("pas(")) + xs.pos().join(",") + red(txtt(")"))
}
//#let spas = text(stroke: red, txtt("pas"))
#let abstr = "abstr"

#let xred = $attach(~>, tr: *)$
#let transa(x) = blue(math.attach(math.stretch($=>$, size: 4em), t: bk(x)))
#let transp(x) = red(math.attach(math.stretch($=>$, size: 4em), t: bk(x)))

#v(1fr)
#bold[#alrt[Abstraction:] hiding functional values]

- $ogs.pat V " "$ the #alrt[pattern]: first-order, visible
- $ogs.fil V " "$ the #alrt[filling]: higher-order, hidden

#v(1fr)
#centering(table(
  columns: 3,
  inset: 0.5em,
  table.header(
    [value \ $V$], [pattern \ $ogs.pat V$], [filling \ $ogs.fil V$],
  ),
  $V cl A -> B$, $x$, $x |-> V$,
  $stlc.tt cl stlc.bool$, $stlc.tt$, $emptyset$,
  $stlc.ff cl stlc.bool$, $stlc.ff$, $emptyset$ + pause,
  //$(V_1, V_2) cl A times B$, $(cnorm(ogs.pat)V_1, ogs.pat""V_2)$, $ogs.fil""V_1 union.plus ogs.fil V_2$,
  $(stlc.tt, stlc.lam x.x)$, $(stlc.tt, f)$, $f |-> stlc.lam x.x$
  // TODO code couleur truc caché vs pas
))
#v(1fr)


/*
$ & abstr_(S -> T)(V)    && := (x, {x |-> V}) quad & #[with $x$ a fresh symbol] \
  pause
  & abstr_(stlc.bool)(stlc.tt) && := (stlc.tt, {}) \
  pause
  & abstr_(stlc.bool)(stlc.ff) && := (stlc.ff, {}) $
*/

== OGS strategy: a labelled transition system (LTS)

#v(1fr)

Active State #h(2cm) #box(baseline: 10pt, diagram(node(..node-c-act)[$#pin(0)P#pin(1), #pin(2)S#pin(3), #pin(4)gamma#pin(5)$])) \
Passive State #h(2cm) #box(baseline: 10pt, diagram(node(..node-c-pas)[$S, gamma$]))
#pause
#pinit-point-from((0,1),
    pin-dx: -8pt,
    pin-dy: -18pt,
    offset-dx: -30pt,
    offset-dy: -40pt,
    body-dx: -65pt,
    body-dy: -20pt,
)[Program]
#pinit-point-from((2,3),
    pin-dx: 8pt,
    pin-dy: -18pt,
    offset-dx: 30pt,
    offset-dy: -40pt,
    body-dx: -10pt,
    body-dy: -20pt,
    box($"Stack" in.rev S && ::= "stop" | E cnorm(colon.double) S$))
#pinit-point-from((4,5),
    pin-dx: 10pt,
    pin-dy: 0pt,
    offset-dx: 50pt,
    offset-dy: 10pt,
    body-dx: 10pt,
    body-dy: -15pt,
)[Environment\ (value assignment)]

#pause
#v(1fr)

#diagram-alt(
  spacing: (3cm, 0.5cm),
  node((0,0), ..node-c-act)[$P, S, gamma$],
  edge((0.5, 0), (1.5, 0), "->")[$tau$],
  node((2,0), ..node-c-act)[$P', S, gamma$],
  node((2.8,0))[when $P ~> P'$],
  pause,
  node((0,1), ..node-c-act)[$V, S, gamma$],
  edge((0.5, 1), (1.5, 1), "->")[#scale(70%, reflow: true, $cnorm(ogs.ret)(ogs.pat V)$)],
  node((2,1), ..node-c-pas)[$S, gamma union.plus cnorm(ogs.fil)V$],
  pause,
  node((0,2), ..node-c-act)[$E[x V], S, gamma$],
  edge((0.5, 2), (1.5, 2), "->")[#scale(70%, reflow: true, $x dot cnorm(ogs.call)(ogs.pat V)$)],
  node((2,2), ..node-c-pas)[$E cnorm(colon.double) S, gamma union.plus ogs.fil V$],
  pause,
  node((0,3), ..node-c-pas)[$E cnorm(colon.double) S, gamma$],
  edge((0.5, 3), (1.5, 3), "->")[#scale(70%, reflow: true, $cnorm(ogs.ret)(Z)$)],
  node((2,3), ..node-c-act)[$E[Z],S, gamma$],
  pause,
  node((0,4), ..node-c-pas)[$S, gamma$],
  edge((0.5, 4), (1.5, 4), "->")[#scale(70%, reflow: true, $x dot cnorm(ogs.call)(Z)$)],
  node((2,4), ..node-c-act)[$gamma(x) th Z,S, gamma$],
)
#v(1fr)

== Abstracting Away the Language: Why?

#v(1fr)

- The OGS recipe has been applied to a #alrt[variety of languages]
- Must be reconstructed and worked out #alrt[each time!]
- Soundness proof is quite hard to understand
  - #alrt[Essential complexity:] OGS soundness is subtle
  - #alrt[Accidental complexity:] facts about a particular language

#pause
#v(1fr)
#bold[My PhD goal]

- Provide an actual #alrt[generic construction]
- Separate the #alrt[OGS-specific] from the #alrt[language-specific]
- Decompose the proof into meaningful high-level arguments

#v(1fr)

= Axiomatizing Abstract Machines

== Mini-map

#v(-4em)
#centering(image(height: 116%, "/img/ogs-outline-machine.excalidraw.png"))

== Simplifying the Setting

#v(1fr)

#bold[#alrt[Weird asymetry] between #ogs.call and #ogs.ret]

#box(width: 6em, $x dot ogs.call""(M)$) "send $M$ to the function #alrt[pointed to by $x$]" \
#box(width: 6em, $ogs.ret""(M)$) "send $M$ to the context #alrt[at the top of the stack]"

#v(1fr)
#pause
#centering(bold[Let us make context (continuation) names explicit])

#v(1fr)

---

#bold[Revisiting the identity function at $quad stlc.bool -> stlc.bool$] \ \

// avant: pin named term & continuation
#only("1")[
  #pinit-point-from((0,1),
    pin-dx: 8pt,
    pin-dy: -2pt,
    offset-dx: 30pt,
    offset-dy: 20pt,
    body-dx: 15pt,
    body-dy: -15pt,
  )[Current\ continuation]
  #pinit-point-from((2,3),
    pin-dx: -8pt,
    pin-dy: 5pt,
    offset-dx: -30pt,
    offset-dy: 35pt,
    body-dx: -75pt,
    body-dy: 5pt,
  )[Next continuation]
]

#align(center + top, diagram-alt(
  spacing: (8cm, 1.5cm),
  node-outset: 10pt,
  node((1,0), ..node-s-pas)[$red(alpha) |-> cfg(square stlc.tt, #pin(2)"stop"#pin(3))$],
  node((0,0), ..node-c-act)[$cfg(stlc.lam x.x, #pin(0)red(alpha)#pin(1))$],
  pause,
  pause,
  edge((0,0), (1,1), "->", bend: 10deg, ..edge-args)[#small($red(alpha) dot ogs.ret""(blue(f))$)],
  node((0,1), ..node-c-pas)[$blue(f) |-> stlc.lam x.x$],
  pause,
  node((1,1), ..node-s-act)[$cfg(blue(f) bk(stlc.tt), "stop")$],
  pause,
  edge((1,1), (0,2), "->", bend: 10deg, ..edge-args)[#small($blue(f) dot ogs.call""(stlc.tt, red(beta))$)],
  node((1,2), ..node-s-pas)[$red(beta) |-> cfg(square, "stop")$],
  pause,
  node((0,2), ..node-c-act)[$cfg((stlc.lam x.x)""stlc.tt, red(beta))$],
  pause,
  edge("->", bend: -75deg, ..edge-args)[#small($tau$)],
  node((0,3), ..node-c-act)[$cfg(stlc.tt, red(beta))$],
  pause,
  edge("->", bend: 10deg, ..edge-args)[#small($red(beta) dot ogs.ret""(stlc.tt)$)],
  pause,
  node((1,4), ..node-s-act)[$cfg(stlc.tt, "stop")$],
))

#pause
#centering[#bold[Restored symmetry!]]

== Configurations and Generalized Values

#v(1fr)
#bold[What did we just do?]

$not A "     "$ add new types for continuations \
#pause
$cfg(E,alpha) "  "$ add new values for continuations \
#pause
$cfg(P, alpha) "  "$ reduce "named terms", or #alrt[configurations] #box[#scale(80%, reflow: true)[(instead of mere terms)]]

#v(1fr)
#pause
#bold[What is the benefit?]

- #ogs.ret and #ogs.call now #alrt[look similar]
- #alrt[No more stack,] only the environment

#v(1fr)
#centering(strong[Simpler to axiomatize!])

#v(1fr)

== Language Machine I: Syntax

#v(1fr)

#bold[Axiomatizing the syntax] \
#box($ & ogs.ty cl base.type                         & #[Object language types] \
  & ogs.scope cl base.type                      & #[Object language scopes] \
  & ogs.cfg cl ogs.scope -> base.type           & #[Machine configurations] \
  & ogs.val cl ogs.scope -> ogs.ty -> base.type #h(2em) & #[Machine values] $)

#pause
#v(1fr)
#bold[Substitution: as usual] \
Assignments $ Gamma =>_ogs.val Delta := {A cl ogs.ty} -> #pin(0)A in Gamma#pin(1) -> ogs.val Delta th A $
#pinit-point-from((0,1),
    pin-dx: 0pt,
    pin-dy: -18pt,
    offset-dx: 30pt,
    offset-dy: -50pt,
    body-dx: -70pt,
    body-dy: -20pt,
)[Proof-relevant membership]
Parallel substitution
$ txtt("sub")_ogs.cfg th {Gamma th Delta} cl ogs.cfg Gamma -> (Gamma =>_ogs.val Delta) -> ogs.cfg Delta  $


#v(1fr)

== Language Machine II: Observation and Evaluation

#v(2em)
#bold[Normal form configurations decompose as triples]
- a #alrt[head] variable
- a first-order #alrt[observation] (copattern)
- the #alrt[filling,] a value assignment

#v(1fr)
#pause

#centering(table(
  columns: 4,
  inset: 0.5em,
  table.header(
    [Normal Config.], [Head], [Observation], [Filling],
  ),
  $cfg(stlc.tt, alpha)$, $alpha$, $ogs.ret""(stlc.tt)$, $emptyset$,
  $cfg(stlc.lam x . x, alpha)$, $alpha$, $ogs.ret""(f)$, $f |-> stlc.lam x.x$,
  $cfg(E[x th stlc.tt], alpha)$, $x$, $ogs.call""(stlc.tt, beta)$, $beta |-> cfg(E, alpha)$,
  $cfg(E[f th (stlc.lam x.x)], alpha)$, $f$, $ogs.call""(g, beta)$, $ g & |-> stlc.lam x.x\ beta & |-> cfg(E, alpha) $,
))

#v(1fr)

---

#v(1fr)

#bold[Axiomatizing observations] \
#box($ & ogs.obs cl ogs.ty -> base.type        & #[Observations] \
  & ogs.args cl ogs.obs A -> ogs.scope #h(3em) & #[Observation arguments] $)

/*
#pause
#v(1fr)
#centering(table(
  columns: 3,
  inset: 0.5em,
  table.header(
    [Type], [Observation], [Arguments],
  ),
  $stlc.bool -> C$, $\ ogs.call""(stlc.tt, alpha) \ ogs.call""(stlc.ff, alpha)$, $alpha cl not C$,
  $(A -> B) -> C$, $ogs.call""(x, alpha)$, $x cl A -> B, alpha cl not C$,
  $not""stlc.bool$, $\ ogs.ret""(stlc.tt)\ ogs.ret""(stlc.ff)$, $emptyset$,
  $not (A -> B)$, $ogs.ret""(x)$, $x cl A -> B$,
))
#v(1fr)
*/

#v(1fr)
#pause

#pinit-highlight(0,1)
#pinit-highlight(2,3)
#pinit-highlight(4,5)
#pinit-point-from((0,1),
    pin-dx: -5pt,
    pin-dy: -20pt,
    offset-dx: -30pt,
    offset-dy: -40pt,
    body-dx: -45pt,
    body-dy: -20pt,
)[Head]
#pinit-point-from((2,3),
    pin-dx: 0pt,
    pin-dy: -20pt,
    offset-dx: 0pt,
    offset-dy: -40pt,
    body-dx: -65pt,
    body-dy: -20pt,
)[Observation]
#pinit-point-from((4,5),
    pin-dx: 20pt,
    pin-dy: -20pt,
    offset-dx: 30pt,
    offset-dy: -40pt,
    body-dx: -15pt,
    body-dy: -20pt,
)[Filling]
#bold[Evaluation] \ #v(-0.4em)
#box($ & ogs.nf th Gamma := {A cl ogs.ty} times #pin(0)""(A in Gamma)#pin(1) times #pin(2)""(o cl ogs.obs A)#pin(3) times #pin(4)""(ogs.args o =>_ogs.val Gamma)#pin(5) \
  #v(-1em) \
  pause
  & ogs.eval cl ogs.cfg Gamma -> #pin("a")base.delay#pin("b") (ogs.nf Gamma) \
$)

#pinit-point-from(("a","b"),
    pin-dx: 20pt,
    pin-dy: 10pt,
    offset-dx: 120pt,
    offset-dy: 30pt,
    body-dx: 5pt,
    body-dy: -25pt,
)[$base.delay X := nu A. X + A$ \ models divergence]

#pause
#v(1fr)
#bold[Observation application] \
#box($ - dot.circle - cl ogs.val Gamma th A -> (o cl ogs.obs A) -> ogs.cfg (Gamma + ogs.args o) $)
#pause
$ && V & dot.circle ogs.call""(Z, alpha) && := cfg(V Z, alpha) \
  && (cfg(E,alpha)) & dot.circle ogs.ret""(Z) && := cfg(E[Z], alpha) $
#pause
#v(1fr)
#centering(strong[And this is it!])

== Substitution Equivalence

#v(1fr)
#bold[An alternative way to see CIU-equivalence]

Fix some $" "Omega cl ogs.scope$ \
For any $" "p, q cl ogs.cfg Gamma$,
$ alrt(p approx_"sub" q) quad := quad (gamma cl Gamma =>_ogs.val Omega) " " -> " "ogs.eval""(p[gamma]) #pin(0)approx#pin(1) ogs.eval""(q[gamma]) $

#pinit-highlight(0,1)
#pinit-point-from((0,1),
    pin-dx: 0pt,
    pin-dy: 5pt,
    offset-dx: -30pt,
    offset-dy: 34pt,
    body-dx: -80pt,
    body-dy: 5pt,

)[Cotermination at the same \ head and observation]

#v(1fr)
#pause
To recover CIU we choose $quad quad Omega := ( "stop" cl not""stlc.bool )$

#v(1fr)

== Language Machines

#v(1fr)
#bold[Axiomatization Recap]

#alrt[Language Machine] $:=$

#stack(dir: ltr, spacing: 1fr)[][
#alrt[Typing] \
- types
- scopes
#v(1.3em)
][
#alrt[Syntax]
- configurations
- values
- observations
][
#alrt[Operations]
- substitution
- evaluation
- observation application
]

#v(1fr)

#bold[Instances]
- polarized #mumu;-calculus with recursive types
- #sym.lambda;-calculi (typed, untyped, CBV, CBN, ...)
- Jump-with-Argument

#v(1fr)

= Generic OGS: First Steps

== Mini-map

#v(-4em)
#centering(image(height: 116%, "/img/ogs-outline-ogs.excalidraw.png"))

== Strategies in Type Theory

#box(height: 100%, width: 54%)[

#v(1.1fr)
#bold[
  Let's forget about OGS \
  How do we represent a strategy?
]
#pause
#v(0.5em)
Automata community: \ #h(2em) states & transition #alrt[relation] #v(0.3em)
#pause
Game semantics community: \ #h(2em) prefix-closed #alrt[set of traces] #v(0.3em)
#pause
Type Theory: \ #h(2em) #strong[infinite (coinductive) tree]
#v(1fr)
]
#meanwhile
#box(height: 100%, width: 45%)[
    //#centering(image(width: 100%, "/img/more-fun-compute.png"))
    #centering(box(radius: 15pt, clip: true, image(width: 100%, "/img/computer-world.jpg")))
    #place(dy: -20pt, dx: 6pt, text(font: "Minecart LCD", weight: "bold", size: 18.5pt)[IT'S MORE FUN TO COMPUTE])
]

== Strategies in Type Theory: Infinite trees

#only("1", centering(image("/img/col-tree-0.excalidraw.png")))
//#only("2", centering(image("/img/col-tree-1.excalidraw.png")))
#only("2", centering(image("/img/col-tree-2.excalidraw.png")))
//#only("3", centering(image("/img/col-tree-4.excalidraw.png")))
#only("3", centering(image("/img/col-tree-5.excalidraw.png")))

== Strategies in Type Theory: Constraining the Moves

#only("1", centering(image("/img/col-tree-6.excalidraw.png")))
#only("2", v(-0.4cm) + centering(image(width: 104%, "/img/col-tree-7.excalidraw.png")))

== Game Rules

#v(1fr)

#centering(image(width: 50%, "/img/half-games.excalidraw.png"))

#pause
#v(1fr)

#box($ & game.hg th (I th J cl base.type) cl base.type := \
  & pat(game.mv cl I -> base.type th,
        game.nx th {i} cl game.mv th i -> J) $)
#h(4cm)
#box($ & game.g th (I th J cl base.type) cl base.type := \
  & pat(game.cli cl game.hg th I th J,
        game.srv cl game.hg th J th I)$)

#v(0.5cm)
#pause
📖 Levy & Staton, "Transition Systems over Games", LICS'14

#v(1fr)

== Indexed Interaction Trees: Forgetting the Passive Side

#only("1", centering(h(1.5cm) + box(image(width: 82%, "img/tree-grouped-0.excalidraw.png"))))
#only("2", centering(image("/img/tree-grouped.excalidraw.png")))
#only("3", centering(image("/img/tree-grouped-2.excalidraw.png")))
#only("4", centering(image("/img/half-to-poly.excalidraw.png")))

== Indexed Interaction Trees

//#v(1fr)
#v(1fr)
#bold[Indexed Container] (a.k.a. polynomial functors) \
/*
#box($ & txtt("ICont") th (I cl base.type) cl base.type \
  & pat(txtt("Query") cl I -> base.type,
        txtt("Reply") th {i} cl txtt("Query") i -> base.type ,
        game.nx {i} th {q cl txtt("Query") i} cl txtt("Reply") q -> I) $)*/
#small[#box($ & interp(-) cl txtt("Game") I th J -> base.type^I -> base.type^I \
  & interp(C, S) th X th i := (q cl C.""txtt("Move") th i) times lr(((r cl S.txtt("Move") th (C.""txtt("next") q)) -> X th (S.""txtt("next") th r)), size: #140%) $)]

#pause
#v(1fr)

/*
== Indexed Interaction Trees: Coinductive Construction

#v(1fr)
*/

#bold[Various known Fixed Points]

- $mu interp(G) quad$ finite trees
- $nu interp(G) quad$ infinite trees

#pause
#v(1fr)

#bold[#alrt[Indexed] Interaction Trees]

#box($
  txtt("itree")_Sigma th X := nu A th i. th (#pin(1)X th i#pin(2) + #pin(3)A th i#pin(4) + #pin(5)interp(G) th A th i#pin(6))
$)

#pinit-highlight(1, 2)
#pinit-highlight(3, 4)
#pinit-highlight(5, 6)
#pinit-point-from((1,2), offset-dx: -20pt, body-dx: -25pt)[Leaf]
#pinit-point-from((3,4), offset-dx: 5pt, body-dx: -35pt)[Silent Move]
#pinit-point-from((5,6))[Actual Move]
#v(2fr)
#pause
📖 Xia _et al._, "Interaction Trees: Representing Recursive and Impure Programs in Coq", POPL'20
#v(-0.5em)

== The Naive OGS Game

#v(1fr)
#bold[The Game]
// TODO pin explications scopes

#pinit-highlight(1, 4)
//#pinit-highlight(3, 4)
#pinit-point-from((1,2),
  pin-dy: -15pt,
  offset-dy: -50pt,
  body-dx: -35pt,
  body-dy: -30pt,
)[
Symbols for the next player
]
#pinit-point-from((3, 4),
  pin-dx: 20pt,
  pin-dy: -20pt,
  offset-dy: -30pt,
  offset-dx: 60pt,
  body-dy: -20pt,
  body-dx: 0pt
)[Symbols for the\ previous player]
#box($
  & txtt("Position") := #pin(1)ogs.scope#pin(2) times #pin(3)ogs.scope#pin(4)
    \
  #pause
  //& ogs.hg cl game.hg th ogs.pos th ogs.pos \
  //#pause
  & game.mv th (Gamma, Delta) := #pin(10){A cl ogs.ty} times (A in Gamma) times (ogs.obs th A)#pin(11) \
#pinit-highlight(10, 11, fill: color.purple.transparentize(90%), dy: -16pt, extended-height: 28pt)
  & game.nx th {Gamma, Delta} th (x, o) := (Delta + ogs.args o, Gamma) \
$)
#h(1fr)
// TODO wider box
#box(baseline: 30pt, scale(70%, reflow: true, diagram(
  spacing: (0cm, -0.6cm),
  node((0,1), shape: fletcher.shapes.rect, corner-radius: 10pt, stroke: 1pt, inset: 1.8em,
       fill: color.purple.transparentize(90%))[
    $ A cl ogs.ty \ x cl A in Gamma \ o cl ogs.obs A $
  ],
  node((0,0), shape: fletcher.shapes.pill, stroke: 1pt, inset: 0.4em,
        fill: color.red.lighten(90%))[
    $Delta + ogs.args o, Gamma$
  ],
  node((0,2), shape: fletcher.shapes.pill, stroke: 1pt, inset: 0.4em,
        fill: color.red.lighten(90%))[
    $Gamma, Delta$
  ],
)))


#pause
#v(1fr)
#bold[The Strategy] #v(0.2em)
// TODO couleur pour les args de play + interieur tuile
// TODO expliquer play avec des pins

#h(0.5fr)
#box[$
  & interp(-) cl ogs.cfg th Gamma times (Delta =>_ogs.val Gamma) -> txtt("itree")_"OGS" th bot th (Gamma, Delta)  \
  & interp(c,gamma) := \
  pause
  & quad (x, o, delta) <- ogs.eval""(c) \
  pause
  & quad #pin(5)""(y, p)#pin(6) <- txtt("play")#pin(7)""(x, o)#pin(8) \
#pinit-point-from((5, 6),
  pin-dx: -25pt,
  pin-dy: -5pt,
  offset-dy: -20pt,
  offset-dx: -70pt,
  body-dy: -20pt,
  body-dx: -80pt
)[Server\ answer]
#pinit-point-from((7, 8),
  pin-dx: 30pt,
  pin-dy: 0pt,
  offset-dy: -10pt,
  offset-dx: 70pt,
  body-dy: -10pt,
  body-dx: 5pt
)[Client move]
#pinit-highlight(5, 6, fill: color.purple.transparentize(90%), dy: -16pt)
#pinit-highlight(7, 8, fill: color.purple.transparentize(90%), dy: -16pt)
  pause
  & quad gamma' := gamma union.plus delta \
  pause
  & quad interp(gamma'(y) dot.circle p, gamma')$]
/*
#h(1fr)
#box[$ & interp(gamma)^- := \
  & quad (x, o) <- txtt("receive"); \
  & quad interp(ogs.apply""(gamma[x], o), gamma)^+ \
  & #hide($interp(gamma)$)
$]
*/
#h(0.5fr)
/*
#box[#box($
  & txtt("State")^+ th (Gamma, Delta) := ogs.cfg th Gamma times (Delta =>_ogs.val Gamma) \
  #v(-1.4em) \
  & txtt("State")^- th (Delta, Gamma) := (Delta =>_ogs.val Gamma) $)
  #pause
  #pinit-highlight(5, 6)
  #pinit-point-from((5,6), pin-dy: -20pt, offset-dy: -50pt, body-dy: -30pt, body-dx: -10pt)[
    $Delta + ogs.args o =>_ogs.val Gamma$
  ]
  #v(-1.2em)
  $ & txtt("play") th (c, gamma) := \
  & quad (A, i, o, delta) <- ogs.eval""(c) \
  & quad txtt("emit")th (A, i, o) txtt(" and goto") #pin(5)""(gamma union.plus delta)#pin(6) \
  #pause
  & txtt("coplay") th gamma th (A, i, o) := txtt("goto") th th (ogs.apply""(gamma[i], o), gamma) \
$]
*/


#v(1fr)

== Soundness w.r.t. Substitution Equivalence

#v(1fr)
#bold[OGS Model]

$ interp(-) cl ogs.cfg Gamma -> txtt("itree")_"OGS" th bot th (Gamma, emptyset) $

#pause
#v(1fr)
#bold[Soundness]

$ interp(p) #pin(0)approx#pin(1) interp(q) -> p approx_"sub" q $
#pinit-highlight(0,1)
#pinit-point-from((0,1),
    body-dx: -30pt,
    body-dy: 7pt,
)[#alrt[Weak bisimilarity]]


#pause
#v(1fr)
#bold[Hypotheses]
- Evaluation commutes with substitution.
- Observation application commutes with substitution.
- Small technical #alrt(text(font: "PicNic", "mystery")) hypothesis.

#v(1fr)
= Proving Soundness Generically

== Mini-map

#v(-4em)
#centering(image(height: 116%, "/img/ogs-outline-proof.excalidraw.png"))

== Composition of Strategies

#v(1fr)
#bold[Proof blueprint]

Define composition of strategies $-||-$ #pause
such that #alrt[adequacy] holds:


$ ogs.eval""(c[gamma]) approx interp(c)^+ || interp(gamma)^- $

#v(1fr)
#pause

#bold[Proof of] $quad interp(c_1)^+ approx interp(c_2)^+ -> c_1 approx_"sub" c_2$ \
#v(0.2em)
#pause
Assume $interp(c_1)^+ approx interp(c_2)^+$. #pause For any $gamma$,

$ ogs.eval""(c_1[gamma]) & approx interp(c_1)^+ || interp(gamma)^- & #[(adequacy)] \
                         pause
                         & approx interp(c_2)^+ || interp(gamma)^- #h(7em) & #[(congruence)] \
                         pause
                         & approx ogs.eval""(c_2[gamma]) & #[(adequacy)] & pause quad square.filled $
//#block(stroke: 0pt, outset: 0.6em, radius: 7pt)[#bold[Hence] #strong[$quad c_1 approx_"sub" c_2$.]]
#v(1fr)

---

#v(-4em)
#centering(image(height: 116%, "/img/ogs-outline-soundness.excalidraw.png"))


/*
---

#v(1fr)
#strong[Problem 1:] #bold[defining composition]

Candidate type:
#only("1")[#box($ -||- cl game.sp th bot th (Gamma, emptyset) -> game.sn th bot th (Gamma, Omega) -> txtt("Delay") th (ogs.obs Omega) $)]
#only("2-3")[#box($ -||- cl game.sp th bot th (Gamma, Delta) -> game.sn th bot th (Gamma, #pin(1)Omega#pin(2) + Delta) -> txtt("Delay") th (ogs.obs Omega) $)
    #pinit-highlight(1,2)
    #pinit-point-from((1,2), pin-dy: -20pt, offset-dy: -50pt, body-dy: -60pt, body-dx: -35pt
    )[Need special handling: \ #alrt[aborts] composition.]
]

#pause
#pause

#v(1fr)
#strong[Fix:] #bold["final" moves using leaves.]

#box($ -||- & cl game.sp th (ogs.obs Omega) th (Gamma, Delta) -> game.sn th (ogs.obs Omega) th (Gamma, Delta) \ & quad -> txtt("Delay") th (ogs.obs Omega) $)

Requires minor tweaks to the OGS strategy.

#v(1fr)
*/

== Adequacy of Composition

#v(1fr)
$ ogs.eval""(c[gamma]) approx interp(c)^+ || interp(gamma)^- $
#v(1fr)

#bold[Proof idea]

- Composition is the #alrt[fixed point] of an #alrt[equation] (a.k.a. while loop)
- $ogs.eval""(c[gamma])$ is #alrt[also a fixed point] of the same equation
- #alrt[Uniqueness] of fixed points for the composition equation

#v(1fr)

---

#v(-4em)
#only("1", centering(image(height: 116%, "/img/ogs-outline-adequacy.excalidraw.png")))
#only("2", centering(image(height: 116%, "/img/ogs-outline-eval-fix.excalidraw.png")))
#only("3", centering(image(height: 116%, "/img/ogs-outline-compo-guard.excalidraw.png")))

/*
#v(1fr)
#strong[Problem 2:] #bold[need to generalize to]

#box($ c cl ogs.cfg th (Omega + Gamma) \
       gamma^+ cl Delta =>_ogs.val Omega + Gamma \
       gamma^- cl Gamma =>_ogs.val Omega + Delta $)
#h(1fr)
#box(height: 1em)[
    #v(-5em)
#box($ ogs.eval""(c[gamma^+#pin(1)""arrows.rl""#pin(2)gamma^-]) approx (c, gamma^+) || gamma^- $)]
#h(1fr)
#pause
    #pinit-highlight(1,2)
    #pinit-point-from((1,2), pin-dy: 10pt//, offset-dy: -50pt, body-dy: -60pt, body-dx: -35pt
    )[This loops.]

#v(1fr)
#strong[Fix:] #bold[keep track of time in the game]

- Values can only depend on earlier variables.
- Refined positions: $[ Gamma_0, Delta_0, Gamma_1, Delta_1, ... ]$
- Refined assignments: #alrt[telescopes].

#v(1fr)
*/

= Conclusion

== Conclusion

#v(1fr)
#bold[Contributions]

// TODO wording
// TODO couleurs

- #alrt[Generic OGS] model, with soundness
- First steps for game semantics in type theory

#v(1fr)
#bold[Not shown today]
- Soundness of #alrt[normal form bisimilarity]
- Instances:
   - #alrt[polarized #mumu;-calculus]
   - Jump-with-Argument
   - pure untyped $lambda$-calculus

#v(1fr)
#bold[Future work]

- Capture effectful languages (hard!)
- More general treatment of composition
- Better comparison to standard constructions and examples

#v(1fr)

== Thank You!

#v(-4em)
#centering(image(height: 116%, "/img/ogs-outline.excalidraw.png"))

/*
#show: appendix

== Proving Unicity

#v(1fr)
#alrt[Not every equation] has unique solutions (e.g. $x = x$).

#alrt[Guarded equations] do.

$ x = #pin(1)2 times #pin(2)x#pin(3)+ 1#pin(4) $
#pinit-highlight(1,2, outset: -2pt, radius: 1pt)
#pinit-highlight(3,4, outset: -2pt, radius: 1pt)
#pinit-highlight(1,4, fill: rgb(0, 0, 0, 0), stroke: 4pt + rgb(255, 0, 0, 20))
#pinit-point-from((3,4), pin-dy: 10pt, offset-dy: 40pt)[$x$ is guarded]

#pause
#v(1fr)

#bold[Iterating equations in a monad]

Equation $quad txtt("step") cl X -> M th (X + Y) $ \
Solution $quad" "txtt("loop") cl X -> M th Y quad$ \ such that
$quad txtt("loop") th x approx (txtt("step") th x bind [txtt("loop"), txtt("ret")] )$

#alrt[Guardedness:] for any $x$ and $y$, $txtt("step") th x approx.not txtt("ret")th (txtt("inl") th y)$

#v(1fr)

---

#v(1fr)
#bold[#strong[Problem 3]: composition equation is not guarded!]

#pause
#v(1fr)
#bold[#strong[Fix:] #alrt[eventual] guardedness is enough for unicity.]

For any $x$ there exists $n$ such that for every $y$,
$ txtt("step")^n th x approx.not txtt("ret")th (txtt("inl") th y) $

E.g., the following is fine $ x & = y \ y & = 2 times x + 1 $

#v(1fr)
---

#v(1fr)

#bold[Why is composition eventually guarded?]

- Values can only depend on #alrt[earlier] variables.
#pause
- After some chit-chat, a #alrt[final variable] or a #alrt[non-variable] will be hit.
#pause
- Surely a redex appears when observing a non-variable. #bold[WRONG]
#pause

#v(1fr)

#alrt(text(font: "PicNic", "Finite Redexes")): the following relation is #alrt[well-founded]!
#inferrule(
  ($i cl Gamma in.rev alpha_1$,
   $o_1 cl ogs.obs th alpha_1$,
   $o_2 cl ogs.obs th alpha_2$,
   $gamma_1 cl ogs.args th o_1 =>_ogs.val Gamma$,
   $gamma_2 cl ogs.args th o_2 =>_ogs.val Gamma$,
   $v cl ogs.val th Gamma th alpha_2$,
   $H_1 cl not txtt("isvar") th v $,
   $H_2 cl ogs.eval th (ogs.apply th v th o_2 th gamma_2) approx txtt("ret") th ((i dot o_1), gamma_1)$
  ),
  $txtt("bad") th H_1 th H_2 cl o_1 lt o_2$
)

#v(1fr)

== Identity function at #sym.space.quad (#stlc.bool → #stlc.bool) → (#stlc.bool → #stlc.bool)

#place(box[#blue[Program] #h(1fr) #red[Context]])
#align(center + horizon, diagram-alt(
  spacing: (8cm, 0.4cm),
  node-outset: 10pt,
  node((1,0), ..node-s-pas)[$square (stlc.lam x.x)stlc.tt$],
  node((0,0), ..node-c-act)[$stlc.lam x.x$],
  pause,
  node((0,1), ..node-c-pas)[$blue(f) |-> stlc.lam x.x$],
  edge((0,0), (1,1), bend: 5deg, "->", ..edge-args)[#small($ogs.ret""(blue(f))$)],
  pause,
  node((1,1), ..node-s-act)[$blue(f) (stlc.lam x.x)""stlc.tt$],
  pause,
  edge((1,1), (0,2), "->", bend: 5deg, ..edge-args)[#small($blue(f) dot ogs.call""(red(g))$)],
  node((1,2), ..node-s-pas)[$red(g) |-> stlc.lam x.x$],
  pause,
  node((0,2), ..node-c-act)[$(stlc.lam x.x) red(g)$],
  pause,
  edge((0,2), (0,3), "->", bend: -85deg, ..edge-args)[#small($tau$)],
  node((0,3), ..node-c-act)[$red(g)$],
  pause,
  edge((0,3), (1,4), "->", bend: 5deg, ..edge-args)[#small($ogs.ret""(blue(h))$)],
  node((0,4), ..node-c-pas)[$blue(h) |-> red(g)$],
  edge((1,1), (1,4), "-->", bend: 70deg)[],
  pause,
  node((1,4), ..node-s-act)[$blue(h) stlc.tt$],
  pause,
  edge((1,4), (0,5), "->", bend: 5deg, label-side: right, ..edge-args)[#small($blue(h) dot ogs.call""(stlc.tt)$)],
  pause,
  node((0,5), ..node-c-act)[$red(g) stlc.tt$],
  pause,
  edge("->", bend: -5deg, ..edge-args)[#small($red(g) dot ogs.call""(stlc.tt)$)],
  pause,
  node((1,6), ..node-s-act)[$(stlc.lam x.x)""stlc.tt$],
  edge((1,6), (1,7), "->", bend: 85deg, ..edge-args)[#small($tau$)],
  node((1,7), ..node-s-act)[$stlc.tt$],
  pause,
  edge("->", bend: -5deg, ..edge-args)[#small($ogs.ret""(stlc.tt)$)],
  edge((0,5), (0,8), "-->", bend: -70deg)[],
  pause,
  node((0,8), ..node-c-act)[$stlc.tt$],
  pause,
  edge("->", bend: -5deg, ..edge-args)[#small($ogs.ret""(stlc.tt)$)],
  edge((1,4), (1,9), "-->", bend: 70deg)[],
  pause,
  node((1,9), ..node-s-act)[$"stop"[stlc.tt]$],
))
*/

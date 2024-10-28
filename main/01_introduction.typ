#import "/lib/all.typ": *

= Introduction <ch-intro>

== Interactive Semantics: Context and Motivations

#let xred = $attach(~>, tr: *)$

This thesis can be broadly set in the field of _programming language
semantics_, whose central question, "What is the meaning of this program?", is
an essential premise to any mathematical study of programs and programing
languages. As it happens, most mainstream programming languages are large and
complex beasts, comprising a number of intertwined features and subtle
interactions with their underlying runtime system. Programs are thus far
removed from the more neatly described traditional objects of mathematical
interest such as say numbers or vector spaces. Paradoxically, although programs
are purely formal constructs, this gives to the study of their semantics the
feel of a natural science, where models are built to capture an ever increasing
level of detail. For sure, a handful of languages do admit models a exhaustive
semantics, but this arguably only ever happens when they are designed with this
intent (e.g., Lisp or #txsc[WebAssembly]). In fact, even for programing
languages strongly rooted in the theoretical computer science community and
routinely used by semanticists, such as proof assistants like Agda or Coq, an
exhaustive description of their semantics is still elusive!#margin-note[To
completely be honest, in the case of Coq _kernel_, the #txsc[MetaCoq]
project is increasingly close to the ground truth.]. #peio[all the refs]

Programing language semantics was born even before the appearence of computers
as we know them, when in the 1930s three equivalent notions of computations
were put forward: general recursive functions~#mcite(<Godel34>),
#short.llc~#mcite(dy: 3em, <Church36>) and #nm[Turing] machines~#mcite(dy: 4.7em, <Turing37>).
These minimalistic models still satisfyingly characterize what it means for a
function's output to be _computable_ from its input. For realistic programming
languages, however, it becomes particularly for the semantics to also take into
account the fine grained interactions between a program and its runtime
environment. As we know, most programs are not limited to taking an input and
producing an output, but may instead react to user keystrokes, display visual
feedback, or interact with networking hardware. In this thesis we will only
consider _pure_ languages, which do not feature any such side effects, and
hence still fit into the "input to output" model, with nothing of interest a
priori appearing during execution. However, perhaps surprisingly, there is a
strong case to be made for interaction: not between a program and the outside
world, but between several programs.

wip wip wip

Interactions between programs appear in pure languages as soon as we want to
give semantics to _program fragments_, e.g., software libraries or code
snippets. Resoning on such fragments becomes a necessity, either to modularly
reason a complex assembly of software components or to study software modules
per se.

While the semantics of whole programs is typically 

First, whole programs can be given semantics either _denotationally_ by
associating to each one some mathematical object, typically some kind of
partial function, or _operationally_ by constructing a _reduction relation_
between programs, describing the computation steps that may be taken. Then




#pagebreak()
#pagebreak()

== A Primer to Operational Game Semantics

=== Simply-Typed #short.llc

== Mechanizing Mathematics with Coq

- coder les maths: important pour l'accessibilité
- coder les maths: important pour juger l'abstraction
- cette thèse: manuel du code (idealisé), guide de réimplementation

explications technique:
- def-eq vs prop-eq vs ext-eq
- setoid rewriting, proper?
- with abstraction
- copattern matching
- implicit arguments
- set vs prop vs strict-prop
- typical ambiguity
- typeclasses

== Thesis Overview

- expliquer "we" vs "I"


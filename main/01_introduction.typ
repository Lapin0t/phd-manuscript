#import "/lib/all.typ": *

= Introduction <ch-intro>

== Interactive Semantics: Context and Motivations

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
level of detail. For sure, a handful of languages do admit exhaustive semantic
descriptions, but this arguably only ever happens when they are designed with
this intent (e.g., Lisp or #txsc[WebAssembly] #peio[ref]). In fact, even for
programing languages strongly rooted in the theoretical computer science
community and routinely used by semanticists, such as proof assistants like
Agda or Coq #peio[ref], a perfect description is still elusive!#margin-note[To
completely be honest, in the case of Coq _kernel_, the #txsc[MetaCoq]
#peio[ref] project is increasingly close to the ground truth.] Yet, this
predicament never stopped anyone from programing and simplified semantics from
being useful. In fact, the value of a mathematical model does not reside in its
faithfullness to reality in all its gruesome details, but in its ability to
ease reasoning on a particular aspect of interest.

In this thesis, the aspect of interest starts with the following question:
When can two _programs fragments_ be considered equivalent? The basis for
studying program fragments---i.e., code snippets, modules, individual
functions, etc.---is a practical one. It can be abstractly argued that
approaching large programs is most easily done by cutting them into smaller
parts to be studied independantly. But to a greater degree, programs are
_written_ modularly in the first place. Languages live and die by the means
they provide to organize abstractions and interfaces, and organizing bits and
pieces is perhaps the primary task of the programer. Then, equivalence is our
first step towards a meaning, and it is already sufficient for a variety of tasks
such as justifying correctness by comparison to a reference implementation,
or verifying optimisations and simplifications, in particular in the context
of compilation---the art of translating programs.

The most important definition for equivalence of program fragments is due to
#nm[Morris]#peio[ref]: _observational_ (or _contextual_) equivalence. It builds
upon the notion of _context_, that is, a program with a hole, which can be
combined with a program fragment to yield a complete program. Then, two program
fragments are considered observationally equivalent, whenever for any context
they might be combined with, the two program compute the same final result. As
the name suggests, observational equivalence characterises program fragments
which cannot be distinguished by programatically interacting with them in any
way, and it is in a precise sense the "best" (weakest) such notion.
Observational equivalence is the gold standard, but it is also quite hard to
work with directly, as it is as much of a property on two programs as a
statement on all the contexts they could fit in. As simple as the programs may
be, the intricacy of the possible contexts is without limit. In consequence, a
fruitful area of research has been to develop alternative characterisations of
observational equivalence, more intrinsically related to the programs at hand,
with the hope of being easier to establish in concrete cases. Among such efforts,
one particular strand of prime importance for us is dubbed _game semantics_.

#[
#let twice = txtt("twice")
#let ff = txtt("f")
#let xx = txtt("x")
#let aa = txtt("a")
#let bb = txtt("b")

For our concerns, the core idea of game semantics is to abstract away the
concrete nature of the observing contexts and instead put the focus on the
ways they would _interact_ with a given program fragment. By keeping the inner
working of the context opaque, we can concentrate on what actually matters,
that is, what it would do to our program fragment. To set things straight, let
us illustrate this idea with a short example: assume our program fragment is
the following function, $twice$.

$ twice(ff, xx) := ff(ff(xx)) $

A sample (polite) interaction with an undescribed context might look like this.

#block(inset: (left: 1.5em),
  grid(columns: 2, rows: 1.5em,
    [Prog.~], [--- You can ask me about $twice$.],
    [Cont.~], [--- What is the output of $twice(aa, 10)$? You can ask me about $aa$.],
    [Prog.~], [--- Well, first what is the output of $aa(10)$?],
    [Cont.~], [--- The output is $5$.],
    [Prog.~], [--- Still, what is the output of $aa(5)$?],
    [Cont.~], [--- It is $3$.],
    [Prog.~], [--- Then the output you asked for is $3$.]
  )
)

A number of different concrete contexts might generate this interaction with $twice$, as
for example several implementations of $aa$ would fit the bill of mapping $10$ to
$5$ and $5$ to $3$. However, any such context would still learn the same thing
about our candidate fragment, namely that when called with such a function $aa$ and the number
$10$, it will output $3$. For the purpose of testing the behavior of $twice$, we do
not loose anything to conflate all these contexts.
The precise rules of such dialogues will be elucidated in due time, but for now
let us return to our exposition.
]

Under this light a program fragment can be understood on its own without any
mention of contexts, as a blueprint or _strategy_, describing how to react to
any possible action. Equivalence of such strategies---reacting the same way to
any action---can then serve as replacement for observational equivalence. Put
more succintly, game semantics is a family of models in which program fragments
are interpreted as strategies for restricted forms of dialogues between them
and the rest of the program. This basic idea is quite flexible and suitable to
model a wide range of features. In fact it originates as part of a wider
interpretation not of programs but of _proofs_, i.e., evidences. Game semantics
in this wider acception is sometimes known as _dialogical logic_, but we will
not try to trace it down to its origins since the connection between logic and
argumentative dialogues is most likely as old as logic itself.

Although it has been motivated as a practical tool for reasoning with
observational equivalence, and that its flexibility has been demonstrated to
apply to a number of advanced programming language features, game semantics has
not yet truly gone out of the hands of the game semanticists and into the
everyday toolkit of the generalist programing language researcher. This can be
contrasted with alternative tools with intersecting usecases, such as the
framework of _logical relations_~#mcite(<DreyerNB12>), also known as
#nm[Tait]'s method of computability~#mcite(dy: 4.2em, <Tait67>). The reasons
for this shortcoming are hard to pin down for certain, but our belief is that
wip!!


/*
#peio[dubious paragraph..]
Programing language semantics was born even before the appearence of computers
as we know them, when in the 1930s three equivalent notions of computations
were put forward: general recursive functions~#mcite(<Godel34>),
#short.llc~#mcite(dy: 1.8em, <Church36>) and #nm[Turing]
machines~#mcite(dy: 4.7em, <Turing37>). These minimalistic models
still satisfyingly characterize _computations_, i.e. programs for transforming
an input into an output. For more recent programming languages, though, it
becomes particularly important for the semantics to also take into account the
fine grained interactions between a program and its runtime environment. As we
know, most programs are not limited to taking an input and producing an output,
but may instead react to user keystrokes, display visual feedback, or interact
with networking hardware. In this thesis we will only consider _pure_
languages, which do not feature any such side effects, and hence still fit into
the "input to output" model, with nothing of interest a priori appearing during
execution. However, perhaps surprisingly, there is still a strong case to be
made for considering interactions: not between a program and the outside world,
but between several programs. Indeed, interactions between programs appear
almost as soon as we want to give semantics not to _whole programs_, but to
_program fragments_, e.g., software libraries or code snippets. Resoning on
such fragments becomes a necessity, either to modularly reason a complex
assembly of software components or to study software modules per se.



To go into a bit more
details, instead of trying to pinpoint the meaning of a program, let us consider
the slightly simpler question "When are two programs equivalent?"

#peio[blabla program fragments. Problème: en vrai c'est open terms +
higher-order functions, qui crée de l'intéraction.]

While the semantics of whole programs is typically 

First, whole programs can be given semantics either _denotationally_ by
associating to each one some mathematical object, typically some kind of
partial function, or _operationally_ by constructing a _reduction relation_
between programs, describing the computation steps that may be taken. Then
*/




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


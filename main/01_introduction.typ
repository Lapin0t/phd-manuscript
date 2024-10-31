#import "/lib/all.typ": *

= Introduction <ch-intro>

== Interactive Semantics: Context and Motivations

This thesis can be broadly set in the field of _programming language
semantics_, whose central question, "What is the meaning of this program?", is
an essential premise to any mathematical study of programs and programming
languages. As it happens, most mainstream programming languages are large and
complex beasts, comprising a number of intertwined features and subtle
interactions with their underlying runtime system. Programs are thus far
removed from the more neatly described traditional objects of mathematical
interest such as say numbers or vector spaces. Paradoxically, although programs
are purely formal constructs, this gives to the study of their semantics the
feel of a natural science, where mathematical models are built to capture an
ever increasing level of detail. For sure, a handful of languages do admit
truly exhaustive semantic descriptions, but this arguably only ever happens when they
are designed with this intent (e.g., Lisp or #txsc[WebAssembly] #peio[ref]). In
fact, even for programming languages strongly rooted in the theoretical
computer science community and routinely used by semanticists, such as proof
assistants like Agda or Coq #peio[ref], a perfect description is still
elusive!#margin-note[To completely be honest, in the case of Coq _kernel_, the
#txsc[MetaCoq] #peio[ref] project is increasingly close to the ground
truth.] Yet, this predicament never stopped anyone from programming and
simplified semantics from being useful. In fact, the value of a mathematical
model does not reside in its faithfullness to reality in all its gruesome
details, but in its ability to ease reasoning on a particular aspect of
interest.

In this thesis, the aspect of interest starts with the following question:
When can two _programs fragments_ be considered equivalent? The basis for
studying program fragments---i.e., code snippets, modules, individual
functions, etc.---is a practical one. It can be abstractly argued that
approaching large programs is most easily done by cutting them into smaller
parts to be studied independantly. But to a greater degree, programs are
_written_ modularly in the first place. Programming languages live and die by
the means they provide to organize abstractions and interfaces, and organizing
bits and pieces is perhaps the primary task of the programmer. Then,
equivalence is our first step towards a meaning, and it is already sufficient
for a variety of tasks such as justifying correctness by comparison to a
reference implementation, or verifying optimisations and simplifications, in
particular in the context of compilation---the art of translating programs.

The most important definition for equivalence of program fragments is due to
#nm[Morris]#peio[ref]: _observational_ (or _contextual_) equivalence. It builds
upon the notion of _context_, that is, a program with a hole, which can be
combined with a program fragment to yield a complete program. Then, two program
fragments are considered observationally equivalent, whenever for any context
they might be combined with, the two program compute the same final result. As
the name suggests, observational equivalence characterizes program fragments
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
interpretation not of programs in programming languages but of _proofs_, i.e.,
evidences, in logical systems. Game semantics in this wider acception is
sometimes known as _dialogical logic_, but we will not try to trace it down to
its origins since the connection between logic and argumentative dialogues is
most likely as old as logic itself.

Although it has been motivated as a practical tool for reasoning with
observational equivalence, and that its flexibility has been demonstrated to
apply to a number of advanced programming language features, game semantics has
not yet truly gone out of the hands of the game semanticists and into the
everyday toolkit of the generalist programming language researcher. This can be
contrasted e.g. with the framework of _logical relations_, also known as
#nm[Tait]'s method of computability~#mcite(dy: 4.2em, <Tait67>), which has
intersecting usecases~#mcite(<DreyerNB12>) and which enjoys a very large number
of introductory material, tutorials and proof walk throughs. While game
semantics is relatively lively as a research area, it has seen comparably
little activity in digesting existing methods, streamlining proofs and
definitions, and making them technically approachable to a wider community.
This venture is a wide ranging one, and it will require an important collective
effort, but it is with this motivation in the back of the mind that this thesis
is written. More precisely---and as we will detail in the following---this
thesis commits to reconstructing from the ground up a particular flavour of
dialog models, _operational game semantics_, a the mathematical language
familiar to computer-assisted proofs: _type theory_.

== Programming Mathematics: How and Why?

For most people, the phrase "computer-assisted proof" usually evocates the idea
of a computer program, checking if some formula or some other kind of
mathematical problem is true or false. This kind of algorithms, known as
_solvers_ are indeed useful in a number of situations, but several landmark
results early in the 20#super[th] century have shown that this can very quickly
become infeasible. First, #nm[Gödel]~#mcite(<Godel31>) showed that for any
logical system, as soon as some moderate level of expressivity is attained,
there are some statements which are neither provable nor disprovable. Quickly
thereafter, #nm[Church]~#mcite(<Church36>) and #nm[Turing]~#mcite(dy: 3em, <Turing37>)
independently showed that there are some tasks which no program can solve,
i.e., functions that we can specify but not _compute_. Hence, the "computer
assistance" we make use of in this thesis is of another kind. Instead of asking
for a program to come up with the proofs, we will write them ourselves in a
purpose designed language. A program understanding this language will then help
us both during the writing, e.g., by providing information about the ongoing
proof, and at the end, when it will check that the proofs we have written are
correct and missing no argument.

There are a number of such systems, but the one we have used in the code
artifact accompagning this thesis is Coq#peio[ref] (or the #txsc[Rocq] Prover,
as it is in the process of being renamed). It is part of a wider family of
systems which we will simply call _type theories_ and whose distinguishing
characteristic is that they are in fact programming languages, although perhaps
of a slightly peculiar kind. To explain this fact and its importance in our
approach to proving mathematical theorems, we need to take a slight step back.

The beginning of this happy coincidence joining logic and programming started
when, still in the early 20#super[th] century, some mathematicians started
insisting that to consider proven the existence of some mathematical object
satisfying some property, one must actually pinpoint it precisely. In other
words, we need to provide a concrete way to construct it, so that it is not
sufficient to merely show that it is impossible for it not to exist without
saying anything about its shape. In this _intuitionistic_ or _constructive_
school of thought, the idea emerged that to any such intuitionistic proof can
be associated a concrete witness or _realizer_, the so-called
#nm[Brouwer]-#nm[Heyting]-#nm[Kolmogorov] interpretation. Programs turned out
to be quite suitable for expressing such realizers, in particular the
#short.llc put forward by #nm[Church]~#mcite(<Kleene45>)#mcite(dy: 3em, <Kreisel59>),
establishing a link between proofs and programs. The bridge between the these
two worlds is however quite deeper as around that time and onward, a string of
observations have been made. They essentially understood, that with a very
moderate amount of squinting, the linguistic rules of existing formal logical
systems were actually the same as the rules of existing programming languages.
Although not an actual theorem, this has been extrapolated to a guiding
principle, or methodological posture, the #nm[Curry]-#nm[Howard]
correspondence, asserting that logics and proofs on one hand, and programming
languages and programs on the other, are the two sides of the same coin.

This correspondence sparked a particularly fruitful activity in logic and
theoretical computer science, namely taking a concept from one side and looking
at it from the other side. We can now study the behavior of a proof when
executed, compare the computational complexity of two proofs of the same
statement, search for the statement(s) that a given algorithm proves, and much
more! Type theories such as Coq embody this correspondence, so that we are
truly both programming and proving at the same time. I personally believe that
this opens up a radically new perspective both on programming and on
mathematical practice of which I outline three important aspects.

A first aspect, relevant to the programmer, is that of _correct-by-construction_
programming, or type-driven development~#mcite(<Brady17>), whereby a program is
its own proof of correctness. _Types_, akin to syntactic categories, classify
programs and they are the counterpart of the logical _propositions_, or
statements, in the programming world. Most programmers are probably familiar with
some types, such as booleans, byte arrays, functions from some type $A$ to some
type $B$, records, etc. In type theories such as Coq, these types are now able
to express a number of powerful logical constructions. Instead of writing a
program and then tediously proving that it is correct w.r.t. some
specification, we can thus write that specification as a type, write the
program, and then simply typecheck it, i.e., ask the system to check that our
program has the given type, in other words that it verifies the corresponding
specification. This is no magic bullet: if there are non-trivial arguments to
be had as to why the program corresponds to the specification, they will now be
required to be put alongside it. Still, a number of invariants can be pushed into
programs and data structures in this way, so that a host of basic properties
are tracked and enforced effortlessly by the language itself. We use this idiom
extensively throughout our Coq development.

A second aspect is relevant to the mathematician. As we stated earlier,
programmers, with the support of computer science, have become quite good at
organizing code modularly, a necessity to ensure ease of use, maintainability,
extensibility, etc. This experience learned the hard way by managing large
bodies of formal constructs can now be pulled across the #nm[Curry]-#nm[Howard]
correspondence and leveraged to organize mathematical concepts. In some
respect, mathematicians have also been preoccupied by properly organizing
concepts, however, we dare to say that this has been a rather organic task,
mostly left to esthetic judgment and to time. By inflicting upon oneself the
rigor of entirely formal reasoning as is done when using proof assistants,
there is no other way than to rationalize the concepts down to their core. When
programming, nothing can be "left for the reader", the gentleman's agreement
providing an escape hatch for uninteresting and tedious mathematical writing,
on facts which are usually self-evident for trained mathematicians with a good
_mental_ representation of the objects in question. When programming, such
_boilerplate_ or _glue code_, is usually linked it to improper data
representations or abstractions and it is resolved by refactoring.

A third aspect concerns _accessibility_. Programming is quite notable for its
number of self-taught practitioners, sometimes of very young age or otherwise
well outside of the intended public. While we do not pretend to explain this
fact, we believe that two points must be part of the picture. First,
explicitness. Although as semanticists we can regret some imperfections,
programming languages are usually thoroughly documented in plain words, with
large manuals describing every element of the syntax and their meaning. As each
and every program is entirely described by this syntax, one does not need to
know the theoretical background of some algorithm to decipher its atomic
operations. Instead programs can be reverse-engineered, starting from a purely
superficial formal understanding. Although the learning curve may be steep,
extremely little background knowledge is required: most things are built from
the ground up and can be inspected. Second, interactivity. Computers turn
programs into a reality which can be poked at and experimented with simply by
running them and testing their behavior. The process of programming itself is
interactive: at the very least one can always try to execute the program, it
will either run or produce an error, reporting what went wrong. In practice,
advances in code editors and other tooling have made the process of writing
code vastly more supportive. This interactivity enables ingenuous
trial-and-error, and removes the requirement of having a knowledgeable person
around for pointing out errors. All in all, there is no reason to believe that
mathematics and computer science are better or worse than any other academic
discipline with respect to gatekeeping. Yet a large amount of crucial knowledge
is hidden behind unspoken conventions, behind a number of little ambiguities
that the reader is assumed to resolve, or inside a sea of publication that
requires a full time job to navigate. By building upon programming languages,
which are executable and clearly defined, the bar to start understanding and
producing meaningful mathematics can be enormously lowered. In fact, we can
already observe several substancial contributions by students and
non-professional mathematicians, in particular in type theory implementations
such as Agda or #txsc[Lean] whose syntax is quite close to mainstream
programming languages.

Now enough with the historical background and the philosophical statements of
intent, what is this thesis truly about? We still have not left much through
which was not known from the title: there will be operational game semantics
and type theory. Before exposing the plan and jumping to the content, let us
first provide a bit of technical details about operational game semantics.

== A Primer to Operational Game Semantics

== How to Read This Document

/*
#pagebreak()
#pagebreak()

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
*/

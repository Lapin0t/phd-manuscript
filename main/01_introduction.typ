#import "/lib/all.typ": *

= Introduction <ch-intro>

== Interactive Semantics: Context and Motivations

This thesis sets itself in the field of _programming language
semantics_, whose central question, "What is the meaning of this program?", is
an essential premise to any mathematical study of programs and programming
languages. As it happens, most mainstream programming languages are large and
complex beasts, comprising a number of intertwined features and subtle
interactions with their underlying runtime system. Programs are thus far
removed from the more neatly described traditional objects of mathematical
interest such as say numbers or vector spaces. Paradoxically, although programs
are purely formal constructs, this complexity gives to the study of their semantics the
feel of a natural science, where mathematical models are built to capture an
ever increasing level of detail. For sure, a handful of languages do admit
truly exhaustive semantic descriptions, but this arguably only ever happens when they
are designed with this intent (e.g., Standard #nm[Ml]~#mcite(dy: -2.2em, <MilnerHMT97>) or #txsc[WebAssembly]~#mcite(dy: 0.8em, <WebAsm>)).
Even for programming languages strongly rooted in the theoretical
computer science community and routinely used by semanticists, such as proof
assistants like Agda~#mcite(<Agda>) or Coq~#mcite(dy: 1em, <Coq>), a perfect description is
elusive#margin-note(mark: true, dy: 1.8em)[
  To be completely honest, in the case of Coq _kernel_, the
  #txsc[MetaCoq]~#num-cite(<Metacoq>) project is increasingly close to the
  ground truth.
]! Yet, this predicament never stopped anyone from programming, nor
simplified semantics from being useful. The value of a mathematical
model does not reside in its faithfulness to reality with all its gruesome
details, but in its ability to ease reasoning about a particular aspect of
interest.

In this thesis, the focus of attention begins with the following question:
When can two _program fragments_ be considered equivalent? The motivation for
studying program fragments---i.e., code snippets, modules, individual
functions, etc.---is of practical nature. It can be abstractly argued that
approaching large programs is most easily done by cutting them into smaller
parts to be studied independently. But to a greater degree, programs are
_written_ modularly in the first place. Programming languages live and die by
the means they provide to organize abstractions and interfaces. Organizing
bits and pieces is perhaps the primary task of the programmer. As such,
studying equivalence will be our first step towards giving a mathematical meaning to
program fragments. This proves to be
sufficient for a variety of tasks such as justifying correctness by comparison
to a reference implementation, or verifying optimizations and simplifications,
in particular in the context of compilation---the art of translating programs.

The most important definition for equivalence of program fragments is due to
#nm[Morris]~#mcite(<Morris68>): _observational_ (or _contextual_) equivalence. It builds
upon the notion of _context_, that is, an incomplete program with a _hole_, a missing part clearly
marked as such. Primarily, a context can be
combined with a program fragment by replacing the marked hole with the fitting fragment, yielding a complete program. Two program
fragments $a$ and $b$ are then considered _observationally equivalent_, whenever for
any context $C$ they might be combined with, the final results of the
combinations $C[a]$ and $C[b]$ will satisfy exactly the same basic
observations. This assumes given some sensible notion of "basic observation" on program
results. As the name suggests, observational equivalence characterizes program
fragments which cannot be distinguished in any way by programatically interacting with
them. It is in a precise sense the "best" (logically weakest)
such notion. Observational equivalence is the gold standard, but also
notoriously hard to work with directly. Indeed, it is as much of a property on two
program fragments, as a statement on _all_ the contexts they could fit in. As simple as the
programs may be, the intricacy of the possible contexts is without limit. In
consequence, a fruitful area of research has been to develop alternative
characterizations of observational equivalence, more intrinsically related to
the programs at hand, with the hope of being easier to establish in concrete
cases. Among such efforts, _game semantics_ is one particular strand of prime importance
to us.

#[
#let twice = txtt("twice")
#let ff = txtt("f")
#let xx = txtt("x")
#let aa = txtt("a")
#let bb = txtt("b")

A core idea of game semantics is to abstract away the
concrete nature of the observing contexts and instead put the focus on the
ways they would _interact_ with a given program fragment. By keeping the inner
working of the context opaque, we can concentrate on what actually matters,
that is, how it would affect our program fragment. To set things straight, let
us illustrate this idea with a short example: assume our program fragment is
the following function $twice$.

$ twice(ff, xx) := ff(ff(xx)) $

A sample (polite) interaction with an otherwise unknown context might look like this.

#block(inset: (left: 1.5em),
  grid(columns: 2, rows: 1.5em,
    [Program], [~--- You can ask me about $twice$.],
    [Context], [~--- What is the output of $twice(aa, 10)$? You can ask me about $aa$.],
    [Program], [~--- Well, first what is the output of $aa(10)$?],
    [Context], [~--- The output is $5$.],
    [Program], [~--- Still, what is the output of $aa(5)$?],
    [Context], [~--- It is $3$.],
    [Program], [~--- Then the output you asked for is $3$.]
  )
)

Different concrete contexts might generate this interaction with $twice$.
For example, several implementations of $aa$ would fit the bill of mapping $10$ to
$5$ and $5$ to $3$. However, any such context would only learn the same information
about our candidate fragment, namely that when called with such a function $aa$ and the number
$10$, it will output $3$. For the purpose of testing the behavior of $twice$, we do
not loose anything to conflate all these contexts.
The precise rules of such dialogues will be elucidated in due time, but for now
let us return to our exposition.
]

Under the light of interactions, a program fragment can be understood on its own without any
mention of contexts, as a blueprint or _strategy_, describing how to react to
any possible action by the other party. Equivalence of such strategies---reacting the same way to
any action---can then serve as replacement for observational equivalence. Put
more succinctly, game semantics is a family of models in which program fragments
are interpreted as strategies for restricted forms of dialogues between them
and the rest of the program. Although the rules of these dialogues are called "games",
bear in mind that they are only tangentially related to the games studied in
game _theory_, e.g., they are devoid of any notion of reward. This basic idea
is quite flexible and suitable to model a wide range of programming language
features. In fact it originates as part of a wider interpretation not of
programs but of _proofs_, i.e., evidence in logical systems. #nm[Girard]'s
geometry of interaction~#mcite(<Girard89>) has been particularly influential in
this respect, but we will not try to trace the game interpretation of logic
down to its origins, since the connection between logical proofs and
argumentative dialogues is most likely as old as logic itself.

Although it has been motivated as a practical tool for reasoning with
observational equivalence, and although its flexibility has been demonstrated to
apply to a number of advanced programming language features, game semantics has
not yet truly gone out of the hands of the game semanticists and into the
everyday toolkit of the generalist programming language researcher. This can be
contrasted, e.g., with the framework of _logical relations_, also known as
#nm[Tait]'s method of computability~#mcite(<Tait67>), which has
overlapping use cases~#mcite(dy: 3em, <DreyerNB12>) and which enjoys a very large number
of introductory material, tutorials and other proof walk-through. While game
semantics is relatively lively as a research area, it has seen comparably
little activity in digesting existing methods, streamlining proofs and
definitions, and making them technically approachable to a wider community.
This thesis is no tutorial, but we will keep this motivation in the back of the
mind.

More concretely, the goal of this thesis is to reconstruct from the ground up a
particular flavor of dialog models, _operational game semantics_ (OGS), and
prove that equivalence of strategies entails observational equivalence. We do
not build it for a precise programming language, but instead target a generic
construction, readily applicable to several languages. This generality is not
for the sake of it, but practically guided by getting to the core of the
construction and separating it from the technicalities pertaining to the given
language. We do so fully formally, in the mathematical language of _type
theory_ common in computer-assisted proving. Before jumping to the content we
will provide a bit more details on operational game semantics, but for now let
us discuss some of the methodological underpinnings of computer-assisted
proofs.

== Programming Mathematics: How and Why?

For most people, the phrase "computer-assisted proof" usually evokes the idea
of a computer program, checking if some formula or some other kind of
mathematical problem is true or false. This kind of algorithm, known as
_solvers_ are indeed useful in a number of situations, but several landmark
results early in the 20#super[th] century have shown that this can very quickly
become unfeasible. First, #nm[Gödel]~#mcite(<Godel31>) showed that for any
logical system, as soon as some moderate level of expressivity is attained,
there are some statements which are neither provable nor disprovable. Quickly
thereafter, #nm[Church]~#mcite(<Church36>) and #nm[Turing]~#mcite(dy: 3em, <Turing37>)
independently showed that there are some tasks which no program can solve,
i.e., functions that we can specify but not _compute_. Hence, the "computer
assistance" we make use of in this thesis is of another kind. Instead of asking
for a program to come up with the proofs, we write them ourselves in a
purpose designed language. A program understanding this language then helps
us both during the writing, e.g., by providing information about the ongoing
proof, and at the end, when it checks that the proofs we have written are
correct and missing no argument.

There are a number of such systems, but the one we have used in the code
artifact accompanying this thesis is Coq~#mcite(<Coq>) (henceforth the #txsc[Rocq] Prover,
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
sufficient to merely show that it is impossible for it not to exist, without
saying anything about its shape. In this _intuitionistic_ or _constructive_
school of thought, the idea emerged that to any such intuitionistic proof can
be associated a concrete witness or _realizer_, the so-called
#nm[Brouwer]-#nm[Heyting]-#nm[Kolmogorov] interpretation. Programs turned out
to be quite suitable for expressing such realizers, in particular the
#short.llc put forward by #nm[Church]~#mcite(<Kleene45>)#mcite(dy: 3em, <Kreisel59>),
establishing a link between proofs and programs. The bridge between these
two worlds is however quite deeper, as around that time and onward, a string of
observations have been made. They essentially understood, that with a very
moderate amount of squinting, the linguistic rules of existing formal logical
systems were actually the same as the rules of existing programming languages.
Although not an actual theorem, this has been extrapolated to a guiding
principle, or methodological posture, the #nm[Curry]-#nm[Howard]
correspondence, asserting that logical systems and proofs on one hand, and programming
languages and programs on the other, are the two sides of the same coin.

This correspondence sparked a particularly fruitful activity in logic and
theoretical computer science, namely taking a concept from one side and looking
at it from the other side. We can now study the behavior of a proof when
executed, compare the computational complexity of two proofs of the same
statement, search for the statement(s) that a given algorithm proves, and much
more! Type theories such as Rocq embody this correspondence, so that we are
truly both programming and proving at the same time. I personally believe that
this opens up a radically new perspective both on programming and on
mathematical practice of which I outline three important aspects.

A first aspect, relevant to the programmer, is that of _correct-by-construction_
programming, or type-driven development~#mcite(<AltenkirchMM05>)#mcite(dy: 3em, <Brady17>), whereby a program is
its own proof of correctness. _Types_, akin to syntactic categories, classify
programs and they are the counterpart of the logical _propositions_, or
statements, in the programming world. Most programmers are probably familiar with
some types, such as booleans, byte arrays, functions from some type $A$ to some
type $B$, records, etc. In type theories such as Rocq, these types are now able
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
extensively throughout our Rocq development.

A second aspect is relevant to the mathematician. As we stated earlier,
programmers, with the support of computer science, have become quite good at
organizing code modularly, a necessity to ensure ease of use, maintainability,
extensibility, etc. This experience learned the hard way by managing large
bodies of formal constructs can now be pulled across the #nm[Curry]-#nm[Howard]
correspondence and leveraged to organize mathematical concepts. In some
respect, mathematicians have also been preoccupied by properly organizing
concepts, however, we dare to say that this has been a rather organic task,
mostly left to aesthetic judgment and to time. By inflicting upon oneself the
rigor of entirely formal reasoning as is done when using proof assistants,
there is no other way than to rationalize the concepts down to their core. When
programming, nothing can be "left for the reader", which is the gentleman's agreement
providing an escape hatch for uninteresting and tedious mathematical writing.
Such untold details are usually self-evident for trained mathematicians with a
good _mental_ representation of the objects in question, as indeed, the problem
is only _formal_. When programming, the similar phenomenon of "boilerplate" or
"glue code", is usually caused by improper data representations or missing
abstractions and it can be resolved by refactoring. As such, formalization can
encourage mathematicians to question the presentational status quo, and provide
sound criteria for judging the suitability of abstractions.

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
that the reader is assumed to resolve, or inside a sea of publications that
requires a full time job and a dedicated mentor to navigate. By building upon
programming languages, which are executable and clearly specified, the bar to
start understanding and producing meaningful mathematics can be enormously
lowered. In fact, we can already observe several substantial contributions by
students and non-professional mathematicians, in particular using type theory
implementations such as Agda~#mcite(<Agda>) or #txsc[Lean]~#mcite(dy: 1em, <MouraU21>)
whose syntax is quite close to mainstream programming languages.

With the frame of discourse now set, let us jump back to operational game
semantics and provide some technical grounding for the rest of this thesis.
From this point on, we will start assuming some familiarity with the
#short.llc.

== A Primer to Operational Game Semantics <sec-intro-ogs>

To set some intuitions about operational game semantics and to introduce some
design choices that will follow us throughout the thesis, let us start by
describing its rules and the obtained strategies in the case of a very simple
programming language: simply-typed #short.llc with recursive functions and
booleans. We recall its syntax, typing, and operational semantics in @fig-stlc.

=== First Steps

#figure(placement: bottom, caption: [#txsc[Stlc] Syntax and Semantics], box(stroke: 1pt, outset: 0.7em, radius: 0.3em)[
  *Syntax*

  $ & "Value"       && in.rev V, W && ::= x  | stlc.tt | stlc.ff | stlc.lam f,x. P \
    & "Term"        && in.rev P, Q && ::= V | P Q \
    & "Eval. Cont." && in.rev E, F && ::= square | E V | P E $

  *Reduction*

  $ (stlc.lam f,x. P) V quad & ~> quad P[f |-> (stlc.lam f,x. P), x |-> V] \
    E[P]                 quad & ~> quad E[Q] quad quad "whenever " P ~> Q $

  *Typing*

  $ & "Type"        && in.rev A, B && ::= A -> B | stlc.bool \
    & "Scope"       && in.rev Gamma, Delta && ::= epsilon | Gamma, x cl A $

  #mathpar(block: true,
    inferrule($Gamma in.rev x cl A$, $Gamma ⊢ x cl A$),
    inferrule($$, $Gamma ⊢ stlc.tt cl stlc.bool$),
    inferrule($$, $Gamma ⊢ stlc.ff cl stlc.bool$),
    inferrule($Gamma, f cl A -> B, x cl A ⊢ P cl B$, $Gamma ⊢ stlc.lam f,x. P cl A -> B$),
    inferrule(($Gamma ⊢ P cl A -> B$, $Gamma ⊢ Q cl A$), $Gamma ⊢ P Q cl B$),
  )
]) <fig-stlc>

Our presentation will more or less follow #nm[Laird]~#mcite(<Laird07>), keeping
only what is required for our simple example language.
The game goes as follows: the two players, unoriginally named "client" and
"server", exchange function _symbols_ such as $txtt("twice")$ and $txtt("a")$
from the previous example, but whose associated definition they do not disclose
to each other. These symbols are introduced in two possible ways: by _calling_
a previously introduced symbol or by _returning_ a value following a previous
call. When calling, if the argument is a boolean it is passed as-is, but in
case it is a function, a fresh symbol is introduced in its place. Similarly
when returning, booleans are given explicitly but functions are again hidden
and shared as a new symbol. This syntactic category consisting of true, false
and fresh function variables can be recognized as _patterns_. Together with
moves they are defined as follows.

#let ret = txtt("ret")
#let call = txtt("call")

$ & "Pattern" && in.rev Z && ::= x | stlc.tt | stlc.ff \
  & "Move"    && in.rev M && ::= ret(Z) | call(x, Z) $

#remark[
  Assuming some existing symbol $x cl (A -> B) -> C$, the move $call(x, y)$
  should really be understood as _binding_ the symbol $y cl A -> B$ for the
  other player for the rest of the play, which is moreover asserted fresh. It
  is a _location_, while $x$ on the other hand is a _pointer_.

  Note that what we call "symbols" in the context of the game are technically
  plain and simple variables. The name is a reference to the "program symbols"
  as appear in shared library object files.
]

The interpretation of terms as strategies is conceptually very simple. First,
we evaluate the term to its normal form. If this does not terminate, the
strategy never plays. If we find a normal form, it can be of two shapes: either
a value $V$ or a term $E[x th V]$ stuck on a symbol $x$ introduced by the
server. In the first case we play $ret(Z)$ and in the second $call(x, Z)$,
where $Z$ is, depending on the type of $V$, either a fresh function symbol or
the boolean $V$. Upon playing this move, we remember everything that we have
not put into the move, that is, possibly the evaluation context $E$ and the
function associated to the fresh symbol. Then, to react to moves, if the server
plays $ret(Z)$, we find our last stored evaluation context $E$ and restart our
strategy as above with $E[Z]$. If the server instead plays $call(x, Z)$, we
look up the value $V$ associated to $x$ and restart with $V Z$.

To make this more precise we need to know how to represent strategies, and this
is an important specificity distinguishing OGS from a lot of other game semantical
models. In OGS, these are described quite concretely by mean of an _automaton_,
or _transition system_, that is, by giving a set of states and a transition
relation. More precisely, because a strategy needs to both play moves and
respond to server moves, there will be two sets of states and two transition
relations, respectively for _active positions_ and _passive positions_. We adopt
the point of view of the client, so that active positions are the ones where
we need to play a move, while passive positions are the ones in which we are
waiting for the server to play.

#let sact = txtt("act")
#let spas = txtt("pas")
#let abstr = "abstr"
#let coln = cnorm(sym.colon.double)

For our OGS strategy, an active state consists of a term $P$ being evaluated, and
the data that we need to remember: a stack of evaluation contexts $S$ and an
environment of function values $gamma$. Passive states only contain the
evaluation stack and the environment. We write them respectively as $sact(P, S, gamma)$
and $spas(S, gamma)$. Before giving the transitions, let us make precise
the _abstraction_ procedure, which hides function expressions from values. It
takes a type and a value of that type and returns a pattern, together with a
_filling_, i.e., an environment containing the value which may have been
abstracted.

$ & abstr_(S -> T)(V)    && := (x, {x |-> V}) quad #[with $x$ a fresh symbol] \
  & abstr_(stlc.bool)(V) && := (V, {}) $

#let red(x) = math.attach(math.stretch($=>$, size: 4em), t: x)

The transitions are given by relations between states, labeled by the move $M$
which is played or received. The active and passive transitions are given as
follows.

/*$ & sact(P, S, gamma)         && quad red(tau)        quad && sact(Q, S, gamma)               && #[whenever $P ~> Q$] \
  & sact(V, S, gamma)         && quad red(ret(Z))     quad && spas(S, gamma union.plus delta)        && #[with $(Z, delta) := abstr(V)$] \
  & sact(E[x th V], S, gamma) && quad red(call(x, Z)) quad && spas(S cnorm(colon.double) E, gamma union.plus delta) quad && #[with $(Z, delta) := abstr(V)$] \
  & spas(S cnorm(colon.double) E, gamma)       && quad red(ret(Z))     quad && sact(E[Z], S, gamma) && \
  & spas(S, gamma)            && quad red(call(x, Z)) quad && sact(gamma(x) th Z, S, gamma) && $*/

#let xred = $attach(~>, tr: *)$

#block(stroke: 1pt, width: 100%, outset: (y: 0.7em), radius: 0.3em, spacing: 2em)[
  $ & sact(P, S, gamma) && quad red(ret(Z))     quad && spas(S, gamma union.plus delta)
      quad && #block(move(dy: -0.2em, text(size: 0.8em)[whenever $P xred V$ and \ $(Z, delta) := abstr(V)$])) \
    & sact(P, S, gamma) && quad red(call(x, Z)) quad && spas(S cnorm(colon.double) E, gamma union.plus delta)
      quad && #block(move(dy: -0.2em, text(size: 0.8em)[whenever $P xred E[x V]$ and \ $(Z, delta) := abstr(V)$])) \
    & spas(S cnorm(colon.double) E, gamma) && quad red(ret(Z))     quad && sact(E[Z], S, gamma) && \
    & spas(S, gamma)                       && quad red(call(x, Z)) quad && sact(V Z, S, gamma) && quad quad #text(size: 0.8em)[when $(x |-> V) in gamma$] $
]

A term $P$ can now be interpreted as a strategy by embedding it as the initial
active state $sact(P, epsilon, {})$. Then, strategies are considered equivalent
when they are _bisimilar_. As the transition is deterministic, this
essentially means that they have the same set of _traces_, that is, the same
infinite sequences of moves obtained by unfolding any possible transition
starting from the initial state. The primary task to make sure the model is
sensible is to prove that for the above given strategy, when two terms are
bisimilar, then they are observationally equivalent---a statement called
_correctness_, or _soundness_ of OGS w.r.t. observational equivalence.

Although this game seems a priori relatively reasonable, before starting our
formal treatment in this thesis we will make a slight change of perspective.
As a hint, it is slightly bothering that our strategy requires two devices
instead of one for remembering what it needs to: a stack and an environment.
The blocker for putting evaluation contexts into the environment is that they
are not named by a symbol. Instead, they are always referred to implicitly, as
e.g. in $ret(Z)$ which can be read "return $Z$ to the context _at the top
of the stack_", much like $call(x, Z)$ reads "send $Z$ to the function _pointed to by_ $x$".
This change of perspective thus involves naming contexts with symbols, as
functions are, and unify the return and call moves into one: symbol
_observation_.

=== More Symbols and Fewer Moves <sec-intro-cps>

We amend the game as follows. First, the exchanged symbols may now refer either
to functions or to evaluation contexts, which we will sometimes (but not
always) distinguish by writing them $alpha$, $beta$, etc. Next, as now both
move kinds explicit the symbol they are targeting, we will separate it
more clearly from the arguments, writing $alpha dot ret(Z)$ and $x dot call(Z, alpha)$.
Note that function calling now has a second argument $alpha$, binding the
continuation symbol on which this call expects a return. They are precisely
defined as follows.

$ & "Observation"    && in.rev O && ::= ret(Z) | call(Z, alpha) \
  & "Move"           && in.rev M && ::= x dot O $
#margin-note(dy: -3em)[
  The Agda programmer or #short.uuc aficionado will surely be happy to recognize
  "observations" as copatterns and "moves" as postfix copattern applications.
]

#let conf(x, y) = $angle.l #x || #y angle.r$

To adapt the OGS strategy to this new game, we do away with the context stack,
as was our motivation. In compensation, we now need to track explicitly the
"current context symbol". The active states thus comprise a _named_ program
$conf(P, alpha)$, i.e. a pair of a program and a continuation symbol, and an
environment $gamma$ mapping symbols to generalized values, that is, function
symbols to function values and context symbols to _named contexts_ $conf(E,
    alpha)$. The passive states now simply consist of an environment. The
transition system can be rewritten as follows.

#block(stroke: 1pt, width: 100%, outset: (y: 0.7em), radius: 0.3em, spacing: 2em)[
  $ & sact(conf(P, alpha), gamma) && quad red(alpha th dot ret(Z))     quad && spas(gamma union.plus delta)
      quad && #block(move(dy: -0.2em, text(size: 0.8em)[whenever $P xred V$ and \ $(Z, delta) := abstr(V)$])) \
    & sact(conf(P, alpha), gamma) && quad red(x th dot call(Z, beta)) quad && spas(gamma union.plus delta')
      quad && #block(move(dy: 0.2em, text(size: 0.8em)[whenever $P xred E[x V]$, \ $(Z, delta) := abstr(V)$ and \ $delta' := delta union.plus {beta |-> conf(E, alpha)}$])) $
  $ & spas(gamma) && quad red(alpha th dot ret(Z))     quad && sact(conf(E[Z], beta), gamma)
      && quad quad #text(size: 0.8em)[when $(alpha |-> conf(E, beta)) in gamma$] \
    & spas(gamma)                       && quad red(x th dot call(Z, beta)) quad && sact(conf(V Z, beta), gamma)
      && quad quad #text(size: 0.8em)[when $(x |-> V) in gamma$] $
]

To put the final blow, let us fuse the definition of the return and call moves, for
active transitions and passive transitions. For the active transitions, notice that
in essence, what is happening is that the named program is reduced to a named normal
form, which is subsequently split into three parts: the head symbol, an observation
on it with more or less opaque arguments, and a small environment storing the value of
anything that has been hidden. Let us define this splitting as follows, where as
usual we make use of $(Z, gamma) := abstr(V)$.

#let split = "split"
$ & split th conf(V, alpha)         && := (alpha dot ret(Z), gamma) \
  & split th conf(E[x V], alpha) && := (x dot call(Z, beta), gamma union.plus {beta |-> conf(E, alpha)}) $

Our active transition now satisfyingly reads as follows.
$ & sact(conf(P, alpha), gamma) && quad red(x th dot th O) quad && spas(gamma union.plus delta)
      quad && #block(move(dy: -0.2em, text(size: 0.8em)[whenever $P xred N$ and \ $(x dot O, delta) := split th conf(N, alpha)$])) $

To unify the two passive transitions, what we are missing is a generalized
"observation application" operator $dot.circle$, which would subsume both context filling and
function application. Define it as follows.

$ & conf(E, alpha) th && dot.circle th ret(Z) && := conf(E[Z], alpha) \
  & V && dot.circle th call(Z, alpha)      && := conf(V Z, alpha) $

The passive transition can now be recovered quite simply, and we reproduce the whole
transition system one last time in its final form.

#block(stroke: 1pt, width: 100%, outset: (y: 0.7em), radius: 0.3em, spacing: 2em)[
$ & sact(conf(P, alpha), gamma) && quad red(x th dot th O) quad && spas(gamma union.plus delta)
      && quad #block(move(dy: -0.2em, text(size: 0.8em)[when $P xred N$ and \ $(x dot O, delta) := split th conf(N, alpha)$])) \
  & spas(gamma)                 && quad red(x th dot th O) quad && sact(X dot.circle O, gamma)
      && quad #text(size: 0.8em)[when $(x |-> X) in gamma$] $
]

The path to generalize the OGS construction to other languages is now ready: we
will abstract over the notions of named term, generalized values, observations,
normal form splitting and observation application. Notice how both the function call
with explicit continuation as well as the named term
construction $conf(P, alpha)$ are reminiscent of abstract machines based
presentations of a language's operational semantics. In this sense, in our
personal opinion, OGS is first and foremost a construction on an abstract machine, and
not on a "programming language". This point of view will guide us during the
axiomatization, as we will indeed entirely forget about bare terms and
evaluation contexts, keeping only _configurations_ (e.g. named terms) and
generalized values. On top of streamlining the OGS, letting go of
contexts will also greatly simplify the necessary syntactic metatheory, as
these "programs with a hole" are perhaps _fun_, but certainly not
_easy_~#mcite(dy: -8.4em, <AbbottAGM03>)#mcite(dy: -5.4em, <McBride08>)#mcite(dy: -3.4em, <HirschowitzL22>).
Yet as we have just seen, this does not preclude to treating languages
given by more traditional small- or big-step operational semantics.


As it happens, this new game with
explicit return pointers is common in OGS constructions for languages with
first-class continuations~#mcite(dy: -2.2em, <LassenL07>)#mcite(dy: 0.8em, <JaberM21>). However, we stress that even for
languages without such control operators, as in our #short.llc, it is an
important tool to streamline the system.

Let us now expose how this thesis will unfold.

== Contributions

The broad goal of this thesis is to formally implement the OGS model in type
theory, and prove it correct w.r.t. observational equivalence. We do not do so
for a particular concrete language, but instead formalize it on top of an
axiomatization of pure, simply-typed programming languages, for which we provide
several instances. This result, as well as most other constructions in this
thesis have been entirely proven in Rocq. The resulting
code artifact can be found at the following address.

#align(center)[
  #link("https://github.com/lapin0t/ogs")
]
#block()

*Games and Strategies in Type Theory* #sym.space.quad In order to represent dialogue games and
game strategies in type theory, we start off in @ch-game by reviewing a notion
of game by #nm[Levy] and #nm[Staton]~#mcite(<LevyS14>). We then generalize upon the
construction of _interaction trees_~#mcite(dy: 0.6em, <XiaZHHMPZ20>) and
introduce _indexed interaction trees_, to represent game strategies as finely
typed coinductive automata. In order to reason on such strategies, we show
powerful reasoning principles for their strong and weak bisimilarity, inside a
framework for coinduction based on complete
lattices~#mcite(dy: 1.8em, <Pous16>)#mcite(dy: 4em, <SchaferS17>). Further, we
introduce a new notion of _eventually guarded_ systems of recursive equations on
indexed interaction trees, which we prove to have existence and uniqueness of
fixed points w.r.t. strong bisimilarity.

*Theory of Substitution* #sym.space.quad In @ch-subst, we lightly
review the standard tools for modeling intrinsically typed and scoped
syntaxes with substitution~#mcite(<FioreS22>)#mcite(dy: 3em,
<AllaisACMM21>). To fit our needs, we present the lesser known notion of
_substitution module_~#mcite(dy: 6.6em, <HirschowitzM10>) over a substitution monoid,
generalizing upon the theory of renaming. We further introduce a novel notion
of _scope structures_, generalizing upon the traditional #nm[De-Bruijn]
indices. Although relatively superficial, scope structures provide us with much
appreciated flexibility in choosing how variables should look like.

*OGS Construction* #sym.space.quad With all the necessary scaffolding in place,
in @ch-ogs we define a generic OGS game, parametrized only by a notion of
_observation_, inspired by copatterns~#mcite(<AbelPTS13>). We then introduce
_language machines_, axiomatizing languages with open evaluators and derive
from them a strategy for the OGS game, constructing the OGS model. We then
state and discuss the hypotheses for correctness of equivalence in the model
w.r.t. observational equivalence and state the correctness theorem. A notable
finding is the appearance of a hypothesis which was never isolated in previous
OGS correctness proofs, as for most concrete languages it is a simple annoyance
to deal with. The language-generic setting, however, makes the requirement and
its reason clear.

*OGS Correctness* #sym.space.quad We prove the correctness theorem in
@ch-proof. After a standard detour on game strategy composition, we provide a
novel decomposition of the correctness proof into two main high-level
components, isolating the purely technical argument from the rest. First, a
core semantical argument, showing essentially that substitution is a fixed
point of the recursive equations defining composition. This part is relatively
straightforward as it does not involve coinduction but only a series a basic
rewriting steps. Second, we show that the composition equation is eventually
guarded. This second part is the most technical, but provides an isolated
justification for concluding by uniqueness of fixed points.

*Normal Form Bisimulations* #sym.space.quad Normal form (NF) bisimulations are
a notion of program equivalence closely related to the OGS model. Their game
is much more restricted, so that it is typically easier to prove two
concrete programs normal form bisimilar than OGS model equivalent. In
@ch-nf-bisim, we construct the NF game and the NF model parametrized, as OGS, by
observations and a language machine. As a first application of the OGS
correctness theorem, we prove that NF bisimilarity is correct by showing that the OGS
interpretation factors through the NF interpretation.

*Language Machine Instances* #sym.space.quad To demonstrate the viability of
our axiomatization of language machines, in @ch-instance we provide three
examples forming a cross section of what can be expressed. For each of them, we define a language machine and prove
the correctness theorem hypotheses. First, we study Jump-with-Argument, a
minimalistic continuation passing style calculus~#mcite(<Levy04>).
Then, we study #short.uuc with recursive
types~#mcite(dy: 0.8em, <CurienH00>)#sym.zwj#mcite(dy: 3em, <DownenA20>), a very
expressive language with explicit control flow. Similarly to
Call-by-Push-Value~#num-cite(<Levy04>), it has been exhibited as
a fine compilation target, so that this instance also implicitly captures all
the calculi which can be compiled to #short.uuc. Finally, we study a more
traditional calculus, untyped #short.llc under weak head reduction. In this
case, it is known that NF bisimulation specializes to #nm[Levy]-#nm[Longo] tree
equivalence~#mcite(<Lassen99>), thus providing a new proof of their soundness
w.r.t. observational equivalence.

== Metatheory

Before sailing off, there is one last thing we need to do: review
the metatheory in which we will work. As we said earlier, our concrete code
artifact is written using the Rocq proof assistant. However, in order to make
this thesis accessible to a wider community, we have chosen to keep the present
text self-contained and without any Rocq snippet. Our construction are written
quite explicitly in a dependently typed programming style, but using an idealized
type theory. From this point on, we will assume a good understanding of
dependent type theory in general, and familiarity at least with _reading_ code
in either Agda, Rocq or some other type theory (#txsc[Lean], #txsc[Idris], ...).

This type theory can be quite succinctly described as an idealized Rocq kernel
with an Agda syntax. More explicitly, it is an _intensional_ type theory, with a
predicative hierarchy of types $base.Type_i$, an impredicative universe of
propositions $base.Prop$ and _strict_#margin-note(mark: true)[
  Our use of strict propositions is anecdotic, so do not worry if your favorite
  proof assistant does not support it. On the other hand, having an
  impredicative sort is crucial for our lattice theoretic treatment of coinduction.
] propositions $base.sProp$. We rely on typical ambiguity and cumulativity to entirely disregard
the universe levels of types. We moreover assume propositional unicity of
identity proofs in the form of #nm[Streicher]'s axiom K for
pattern matching~#mcite(dy: 2em, <Cockx17>), as well as definitional #sym.eta\-law on
records and functions (in particular for the empty record type
$base.unit$). We further assume the ability to define inductive data types and
coinductive record types.

More superficially, we adopt Agda like syntax. Let us go through all the
constructions. Keywords are highlighted in $ckw("orange")$, definitions in
$de("blue")$, data type constructors in $cs("green")$, record projections
in $pr("pink")$ and identifier and some primitive type formers in black.

*Function Types* #sym.space Given $A cl base.Type$ and $B cl A -> base.Type$, the dependent function type
is written $(a cl A) -> B th a$, or possibly $forall th a -> B th a$, when $A$ can be
inferred from the context. We additionally make use of implicit argument,
written in braces like ${a cl A} -> B th a$ or $forall th {a} -> B th a$. We
adopt the Rocq convention of writing some argument binders left of the typing
colon, simply separated by spaces. For example, we may declare the polymorphic
identity function as $de("id") th {A} cl A -> A$, instead of $de("id") cl
forall th {A} -> A -> A$. When readability is at stake, we will even entirely
drop implicit binders, but we will try to use this sparingly. Any
dangling seemingly free identifier should be considered implicitly universally
quantified.

#remark[
  For Rocq programmers confused by the Agda-like $forall$ symbol: just parse the rest of the
  type as you do in Rocq when left of the typing colon. Any appearance of $->$
  switches back the rest to the usual parsing.
]

As we will use type families quite heavily, we introduce the notation
$base.Type^(X_1, ..., X_n)$ to denote $X_1 -> ... -> X_n -> base.Type$.

*(Inductive) Data Types* #sym.space Data types identifier are declared preceded by the
keyword $kw.dat$ and we give their constructors as inference rules. When the
rules are self-referential, the type is always an inductive type. For extremely
simple finite types, such as booleans, or the empty type, we write the following.

#mathpar(block: true,
  $kw.dat th base.bool cl base.Type := base.btrue th | th base.bfalse$,
  $kw.dat th base.empty cl base.Type := #hide($|$)$
)

We declare so called _mixfix_ identifiers with the symbol $ar$ as a placeholder
for arguments in the identifier. As such, the disjoint sum $A base.sum B$ is declared as
$kw.dat th nar""cnorm(base.sum)nar cl base.Type -> base.Type -> base.Type$. Its constructors
are given as follows.

#mathpar(block: true,
  inferrule($a cl A$, $base.inj1 th a cl A base.sum B$),
  inferrule($b cl B$, $base.inj2 th b cl A base.sum B$),
)

To avoid heavy notations, we may sometimes simply write $base.sum$, or
$(base.sum)$, when referring to infix combinators such the disjoint sum which
should normally be identified by $nar""cnorm(base.sum)nar$. The propositional equality
type is declared as $kw.dat th nar""cnorm(base.eq)nar th {A} cl A -> A -> base.Prop$,
with the following constructor.
#v(-1em)
#mathpar(block: true, inset: 0em,
  inferrule("", $base.refl cl x base.eq x$)
)

Pattern matching functions are written by listing their _clauses_.
Pattern matching is dependent and we do not write absurd clauses, as the $base.inj2$
case in $de("foo")$ below.

#mathpar(block: true,
  $de("foo") th {A} cl A base.sum base.empty -> A \
   de("foo") th (base.inj1 th a) := a \ #v(0.2em) $,
  box[
   $de("swap") th {A th B} cl A base.sum B -> B base.sum A$
   #v(0em)
   $&de("swap") th (base.inj1 th a) && := base.inj2 th a \
    &de("swap") th (base.inj2 th b) && := base.inj1 th b$
  ]
)

Sometimes, we use the $kw.case$ keyword, to pattern match on an expression. For
example, we could have alternatively defined $de("swap")$ as follows.

$ de("swap") th {A th B} cl A base.sum B -> B base.sum A \
  de("swap") th x := kw.case th x \
  pat(base.inj1 th a & := base.inj2 th a,
      base.inj2 th b & := base.inj1 th b) $
#margin-note(dy: -7em)[
  The leftist programmer~#mcite(dy: 7em, <McBrideM04>) unsettled by this $kw.case$
  construction should note that we use it very sparingly. In fact, we will
  only use it in head position, as a $ckw("with")$ construction in disguise.
]

*(Coinductive) Record Types* #sym.space Record types are introduced by the
keyword $kw.rec$ and by listing the type of their projections. When the
declaration is self-referential, record types are always coinductive. The
sigma type is technically declared as below, but we write it $(a cl A)
base.prod B th a$, mimicking the dependent function
type.

$ kw.rec th de("sigma") th (A cl base.Type) th (B cl A -> base.Type) cl base.Type := \
  pat(
    base.fst & cl A,
    base.snd & cl B th base.fst
  ) $

We write projections in postfix notation and define record elements by
so-called record expressions, giving the value of each projection, such as
follows.

$ de("flip") th {A th B} cl A base.prod B -> B base.prod A \
  de("flip") th p :=
  pat(
    base.fst & := p .base.snd,
    base.snd & := p .base.fst,
  ) $

We sometimes introduce constructors for record elements. In particular,
for the sigma type we define the constructor $nar""cm""nar$ allowing us to
write pairs as the usual $(a cm b)$, and destruct them by pattern matching. We
additionally define the unit type as the empty record $kw.rec th base.unit cl base.Type
:= []$, with the constructor $base.tt$.

*Induction and Coinduction* #sym.space.quad We have not described which kind
of inductive or coinductive functions we should be allowed to write. This is
quite a tricky subject, as we use self-referential definitions instead of
eliminators (and coeliminators). As such we will here only mostly say that "it
works like in Rocq". Slightly more precisely, we will allow ourselves mutually
recursive definitions with calls on structurally smaller arguments, and
similarly only corecursive calls below record projections.

*Typeclasses* #sym.space.quad To structure our development, we will make use of
typeclasses, which are simply records introduced by the keyword $kw.cls$ and
whose projections are written free standing, i.e., with the record element left
implicit. We use the keyword $kw.ext$, to denote the fact that a given
typeclass declaration depends an instance of a previously declared one. As an
example, we could define magmas and unital magmas as follows.

#mathpar(block: true, spacing: 1fr,
  $kw.cls de("Magma") th (X cl base.Type) := \
  pat(nar""pr(cnorm(bullet))nar cl X -> X -> X) \ #v(1.5em)$,
  $kw.cls de("UnitalMagma") th (X cl base.Type) := \
    pat(
      kw.ext th de("Magma") th X,
      pr("id") cl X,
      pr("id-"cnorm(bullet)) th {x} cl pr("id") pr(bullet) x base.eq x,
      pr(cnorm(bullet)"-id") th {x} cl x pr(bullet) pr("id") base.eq x,
    )$
)

*Extensional Equality* #sym.space.quad Although we pride ourselves in being
very precise and explicit in all of our constructions, there will be a small
technical informality (see @ch-ccl for a mea culpa). Because we work with
coinductive objects in intensional type theory, propositional equality is
too strong for several statements. As such, we use _extensional_ equality
in several places, written $a approx b$. The problem is that the definition of
extensional equality depends on the type we are considering, so that this
should be essentially considered as a kind of typeclass giving the extensional
equality equivalence relation at any given type. We try to be explicit
around its use. For types $A$ and $B$, $A approx B$ denotes an isomorphism.

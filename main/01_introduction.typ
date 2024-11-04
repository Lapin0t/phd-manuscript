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
are designed with this intent (e.g., #nm[Lisp] or #txsc[WebAssembly] #peio[ref]). In
fact, even for programming languages strongly rooted in the theoretical
computer science community and routinely used by semanticists, such as proof
assistants like Agda~#mcite(<Agda>) or Coq~#mcite(dy: 1em, <Coq>), a perfect description is still
elusive#margin-note(mark: true, dy: 2em)[To completely be honest, in the case of Coq _kernel_, the
#txsc[MetaCoq]~#num-cite(<Metacoq>) project is increasingly close to the ground
truth.]! Yet, this predicament never stopped anyone from programming and
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
studying equivalence is our first step towards a meaning, and it is already
sufficient for a variety of tasks such as justifying correctness by comparison
to a reference implementation, or verifying optimisations and simplifications,
in particular in the context of compilation---the art of translating programs.

The most important definition for equivalence of program fragments is due to
#nm[Morris]~#mcite(<Morris68>): _observational_ (or _contextual_) equivalence. It builds
upon the notion of _context_, that is, a program with a hole, which can be
combined with a program fragment to yield a complete program. Then, two program
fragments $a$ and $b$ are considered observationally equivalent, whenever for
any context $C$ they might be combined with, the final result of the
combinations $C[a]$ and $C[b]$ will satisfy exactly the same basic
observations, for some sensible notion of "basic observation" on program
results. As the name suggests, observational equivalence characterizes program
fragments which cannot be distinguished by programatically interacting with
them in any way, and it is in a precise sense the "best" (logically weakest)
such notion. Observational equivalence is the gold standard, but it is also
quite hard to work with directly, as it is as much of a property on two
programs, as a statement on _all_ the contexts they could fit in. As simple as the
programs may be, the intricacy of the possible contexts is without limit. In
consequence, a fruitful area of research has been to develop alternative
characterisations of observational equivalence, more intrinsically related to
the programs at hand, with the hope of being easier to establish in concrete
cases. Among such efforts, one particular strand of prime importance for us is
dubbed _game semantics_.

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
any possible action by the other party. Equivalence of such strategies---reacting the same way to
any action---can then serve as replacement for observational equivalence. Put
more succintly, game semantics is a family of models in which program fragments
are interpreted as strategies for restricted forms of dialogues between them
and the rest of the program. Although the rules of these dialogues are called "games",
bear in mind that they are only tangentially related to games as studied in
game _theory_, e.g., they are devoid of any notion of reward. This basic idea
is quite flexible and suitable to model a wide range of programming language
features. In fact it originates as part of a wider interpretation not of
programs but of _proofs_, i.e., evidences, in logical systems. Game semantics
in this wider acception is sometimes known as _dialogical logic_, but we will
not try to trace it down to its origins since the connection between logical
proofs and argumentative dialogues is most likely as old as logic itself.

Although it has been motivated as a practical tool for reasoning with
observational equivalence, and that its flexibility has been demonstrated to
apply to a number of advanced programming language features, game semantics has
not yet truly gone out of the hands of the game semanticists and into the
everyday toolkit of the generalist programming language researcher. This can be
contrasted e.g. with the framework of _logical relations_, also known as
#nm[Tait]'s method of computability~#mcite(<Tait67>), which has
intersecting usecases~#mcite(dy: 3em, <DreyerNB12>) and which enjoys a very large number
of introductory material, tutorials and other proof walk-throughs. While game
semantics is relatively lively as a research area, it has seen comparably
little activity in digesting existing methods, streamlining proofs and
definitions, and making them technically approachable to a wider community.
This thesis is no tutorial, but we will keep this motivation in the back of the
mind.

More concretely, the goal of this thesis is to reconstruct from the ground up a
particular flavour of dialog models, _operational game semantics_ (OGS), and
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
artifact accompagning this thesis is Coq~#mcite(<Coq>) (or the #txsc[Rocq] Prover,
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
programming, nothing can be "left for the reader", which is the gentleman's agreement
providing an escape hatch for uninteresting and tedious mathematical writing,
on facts which are usually self-evident for trained mathematicians with a good
_mental_ representation of the objects in question. When programming, such
"boilerplate" or "glue code", is usually caused improper data representations
or missing abstractions and it can be resolved by refactoring. As such,
formalization can encourage mathematicians to question the presentational
status quo, and provide sound criteria for judging the suitability of
abstractions.

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
lowered. In fact, we can already observe several substancial contributions by
students and non-professional mathematicians, in particular using type theory
implementations such as Agda~#mcite(<Agda>) or #txsc[Lean]~#mcite(dy: 1em, <MouraU21>)
whose syntax is quite close to mainstream programming languages.

With the frame of discourse now set, let us jump back to operational game
semantics and provide some technical grounding for the rest of this thesis.
From this point on, we will start assuming some familiarity with the
#short.llc.

== A Primer to Operational Game Semantics

To set some intuitions about operational game semantics and to introduce some
design choices that will follow us throughout the thesis, let us start by
describing its rules and the obtained strategies in the case of a very simple
programming language: simply-typed #short.llc with recursive functions and
booleans. We recall its syntax, typing, and operational semantics in @fig-stlc
#peio[todo numbering].

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

The game goes as follows: the two players, unoriginally named "client" and
"server", exchange function _symbols_ such as $txtt("twice")$ and $txtt("a")$
from the previous example, but whose associated definition they do not disclose
to each other. These symbols are introduced in two possible ways: by _calling_
a previously introduced symbol or by _returning_ a value following a previous
call. When calling, if the argument is a boolean it is passed as-is, but in
case it is a function, a fresh symbol is introduced in its place. Similarly
when returning, booleans are given explicitely but functions are again hidden
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
is an important specificity distinguishing OGS from more usual game semantics
models. In OGS, these are described quite concretely by mean of an _automaton_,
or _transition system_, that is, by giving a set of states and a transition
relation. More precisely, because a strategy needs to both play moves and
respond to server moves, there will be two sets of states and two transition
relations, respectively for _active positions_ and _passive positions_.

#let sact = txtt("act")
#let spas = txtt("pas")
#let abstr = "abstr"
#let coln = cnorm(sym.colon.double)

For our OGS strategy, an active state consists of a term $P$ being evaluated, and
the data that we need to remember: a stack of evaluation contexts $S$ and an
environment of function values $gamma$. Passive states only contains the
evaluation stack and the environment. We write them respectively as $sact(P, S, gamma)$
and $spas(S, gamma)$. Before giving the transitions, let us precise
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

A term $P$ can now be interpreted as a strategy by embeding it as the initial
active state $sact(P, epsilon, {})$. Then, strategies are considered equivalent
when they are _bisimilar_, which in this case essentially means that they have
the same set of _traces_, that is, the infinite sequences of moves obtained by
unfolding any possible transition starting from the initial state. The primary task to
make sure the model is sensible is to prove that for the above given strategy,
when two terms are bisimilar, then they are observationally equivalent---a
statement called _soundness_ of OGS w.r.t. observational equivalence.
#peio[un mot sur la preuve de soundness/adequacy/composition, et sur CIU?]

Although this game seems a priori relatively reasonable, before starting our
formal treatement in this thesis we will make a slight change of perspective.
As a hint, it is slightly bothering that our strategy requires two devices
instead of one for remembering what it needs to: a stack and an environment.
The blocker for putting evaluation contexts into the environment is that they
are not named by a symbol. Instead, they are always referred to implicitely, as
e.g. in $ret(Z)$ which can be read "return $Z$ to the context at the _top
of the stack_", much like $call(x, Z)$ reads "send $Z$ to the function $x$".
This change of perspective thus involves naming contexts with symbols, as
functions are, and unify the return and call moves into one: symbol
_observation_.

=== More Symbols and Less Moves

We amend the game as follows. First, the exchanged symbols may now refer either
to functions or to evaluation contexts, which we will sometimes (but not
always) distinguish by writing them $alpha$, $beta$, etc. Next, as now both
move kinds explicit the symbol they are targetting, we will separate it
more clearly from the arguments, writing $alpha dot ret(Z)$ and $x dot call(Z, alpha)$.
Note that function calling now has a second argument $alpha$, binding the
continuation symbol on which this call expects a return. They are precisely
defined as follows.

$ & "Observation"    && in.rev O && ::= ret(Z) | call(Z, alpha) \
  & "Move"           && in.rev M && ::= x dot O $
#margin-note(dy: -3em)[
  The Agda programmer or #short.uuc afficionado will surely be happy to recognize
  "observations" as copatterns and "moves" as postfix copattern applications. #peio[ref]
]

#let conf(x, y) = $angle.l #x || #y angle.r$

To adapt the OGS strategy to this new game, we do away with the context stack,
as was our motivation. In compensation, we now need to track explicitely the
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

To put the final blow, let us fuse the definition of the return and call transitions, for
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
normal form splitting and observation application. Notice how both the
explicit threading of evaluation contexts as well as the named term
construction $conf(P, alpha)$ are reminescent of abstract machines based
presentations of a language's operational semantics. In this sense, in our
opinion, OGS is first and foremost a construction on an abstract machine, and
not on a "programming language". This point of view will guide us during the
axiomatization, as we will indeed entirely forget about bare terms and
evaluation contexts, keeping only _configurations_ (e.g. named terms) and
generalized values. On top of streamlining the OGS, letting go of evaluation
contexts will also greatly simplify the necessary syntactic metatheory, as
these "programs with a hole" are perhaps _fun_, but certainly not
_easy_~#mcite(<AbbottAGM03>)#mcite(dy: 4em, <McBride08>).
Yet as we have seen, this does not preclude to treating languages
given by more traditional small- or big-step operational semantics, or even
with syntactic denotational semantics into some computational metalanguage.



As it happens, this new game with
explicit return pointers is common in OGS constructions for languages with
first-class continuations~#mcite(<LassenL07>)#mcite(dy: 3em, <Laird07>)#mcite(dy: 5em, <JaberM21>). However, we stress that even for
languages without such control operators, as in our #short.llc, it is an
important tool to streamline the system.

Let us now expose how this thesis will unfold.

== How to Read This Thesis

WIP

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

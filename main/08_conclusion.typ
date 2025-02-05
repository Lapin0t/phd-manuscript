#import "/lib/all.typ": *

= Perspectives <ch-ccl>

I hope that this thesis has somewhat demystified operational game semantics to
the type theorist. Let us review some of the most important steps we have taken.

- We started off in @ch-game by presenting a new data structure
  for coinductively representing automata in type theory. This puts a new item in the
  already large bag of constructions based on polynomial functors. But
  perhaps most importantly, we demonstrated that with a small twist,
  namely splitting these polynomials in halves, we can obtain
  well-behaved game descriptions. Thanks to this, finely typed
  automata prove quite suitable to represent strategies for dialog
  games inside type theory.

- Next, in @ch-subst, we introduced a small proof pearl: scope
  structures. They untie the intrinsically scoped and typed theory of
  substitution from the (too) concrete #nm[De-Bruijn] indices. This
  brings a bit more flexibility in the practical formalization of
  syntactic objects. Subset scopes in particular were of great use in the OGS
  instances we have shown (@ch-instance), although it mostly smoothed the
  work behind the scene, so you may have to take my word for it#margin-note(mark: true)[
    As I recall, when I stopped working with the "wrong" notion of variable
    and introduced subset scopes, I cut the size of the Rocq code for
    the polarized #short.uuc instance by roughly a third.
  ].

- In @ch-ogs we arrived at operational game semantics. We constructed a generic
  OGS model, proposing an axiomatization of languages with an evaluator for open programs.
  This axiomatization is inspired by abstract machines, taking a computational approach
  to operational semantics. Most notably, it leaves the syntax entirely opaque and
  devoid of any inductive nature, to be contrasted, e.g., with structural
  operational semantics~#mcite(<Plotkin04a>). Yet this is enough to construct an
  OGS model, and to prove it correct w.r.t. an observational equivalence
  under suitable hypotheses (@ch-proof). This underlines that much like
  denotational semantics, operational semantics can also beneficially manage to
  push the clutter and technicalities of syntax out of sight.

- Finally, we reaped some rewards from all of these constructions. First we
  generically defined normal form bisimilarity, proving it correct by going
  through OGS strategy bisimilarity (@ch-nf-bisim). Then, we instantiated our
  language axiomatization with three standard calculi (@ch-instance). 

As always,
there is the feeling that we have barely started scratching the
surface. Formally proving this correctness theorem turned out to be a
long and narrow track. Along the way we zoomed past many opportunities
for more in-depth study. Furthermore, although we already capture a
number of languages, the level of generality of our OGS model could be
improved. Indeed, we neither handle effectful languages (apart from
partiality), nor polymorphic type systems, two features for which OGS
models have already been demonstrated~#mcite(dy: 0em,
<Laird07>)#mcite(dy: 2em, <LassenL08>)#mcite(dy: 5em, <JaberT18>).
Let us discuss in more details what we managed to glimpse from a
couple of these windows into the unknown.

*Games and Open Composition* #sym.space.quad Although category theory
concepts are structuring our development behind the scenes, we have
made the choice to minimize their amount. Besides making the
manuscript slightly more accessible, it is a pragmatic implementation
choice, as category theory mechanization in intensional type theory is
notoriously a can of worms. However, #nm[Levy] and #nm[Staton]'s games
and strategies, presented in @ch-game, enjoy a rich categorical
theory, which we have mostly skipped over. As a consequence, we did
not say anything about the properties of OGS as a game, beyond the
trivial fact that it is symmetric.

First of all, games are regularly used as models for (parts of) linear logic.
It would be interesting to see how our notion of games fare in this respect. In
fact our OGS game is strongly reminiscent of "bang" games in typical such
interpretations. In both cases, the game position is a list (or scope) of
possible game copies to choose from, and moving _spawns_ new possible positions
(by concatenation on this list).

But linear logic is not the sole provider of structure on games, as #nm[Conway]
also studied quite similar objects. Slightly more precisely, it is not too
difficult to see the following definition (which we saw in passing in
@sec-game-example) as creating a variant of the #nm[Conway] sum of two games.

#[
#show math.equation: set block(breakable: false)
$ ar de(+_h) ar cl game.hg th I th I -> game.hg th J th J -> game.hg th (I base.prod J) th (I base.prod J) \
  A de(+_h) B :=
    pat(
      game.mv th & (i, j) & := A .game.client"".game.mv th i base.sum B .game.client"".game.mv th j,
      game.nx th &(i, j) th (base.inj1 th m) & := (A.game.client"".game.nx th m, j),
      game.nx th &(i, i) th (base.inj2 th m) & := (i, B .game.client"".game.nx th m),
    ) \ \
  ar de(+) ar cl game.g th I th I -> game.g th J th J -> game.g th (I base.prod J) th (I base.prod J) \
  A de(+) B :=
  pat(
    game.client := A .game.client de(+_h) B .game.client,
    game.server := A .game.server de(+_h) B .game.server,
  ) $
]

Then, we conjecture that $ogs.g de(+) ogs.g approx ogs.g$, where $approx$
denotes a _game bisimulation_, i.e., an isomorphism between their respective
sets of moves, mediated by a suitable relation between their respective
sets of positions. We have preliminary results in this direction, but using
a slightly different formulation of $ogs.g$, taking the cleaner _absolute_
point of view on the naive version presented in @sec-ogs-game
(@def-ogs-g-naive, see @rem-ogs-g-abs-vs-rel).

Like the linear logic $game.xpar$ connective, this #nm[Conway] sum
provides a candidate for game exponentials, as $A de(=>) B :=
A^game.opp de(+) B$. This combinator enjoys a corresponding
composition operation, taking a strategy on $A^game.opp de(+) B$ and
one on $B^game.opp de(+) C$ to a strategy on $A^game.opp de(+) C$.
This could shed new light on our slightly ad-hoc treatment of OGS game
strategy composition. Our hope is that we will then have the necessary
scaffolding to define an _open_ composition which does not merely
return some final observation, but a whole OGS strategy. We conjecture
that at this point, by ditching this cumbersome final scope, we will
be able to slightly strengthen the adequacy theorem. This would yield
a stronger conclusion than correctness, namely that OGS model
equivalence is closed under substitution (i.e., substitutive).

*NF Strategies as a Language Machine* #sym.space.quad We conjecture that with a
slight tweak and a suitable definition of morphisms, NF strategies can be
exhibited as the _terminal_ language machine. Let us unpack this! Define the
family of configurations of this machine as active NF strategies and the family
of values as the "unary" passive NF strategies presented in @rem-nf-unary. For
this machine, the $ogs.eval$ map
simply seeks the first $itree.retF$ or $itree.visF$ move of the given active NF
strategy. The observation application map $ogs.apply$ is more problematic, but
here comes the tweak. Recall from @rem-langm-apply-alt that there were two possible
variants for the design of the application map. In our development we chose the
_flex_ one, which additionally takes a filling as argument. We now switch
to the tighter one, which assumes the filling is given by fresh variables and
thus simply extends the scope of the returned configuration. In this second
version, the application map for our NF strategies machine is just function
application! A promising candidate for the terminal arrow is then given by the
NF interpretation $nfinterpA(ar)$.

A happy benefit of this construction, is that although the NF language machine
does not support substitutions, we conjecture it has a pointed renaming
structure (extending @def-nf-ren). As such, the OGS machine strategy
construction can apply, and it should computes exactly the $nf.nf2ogs$
embedding (@def-nf-to-ogs).

Taking a step back, we conjecture that what is happening, is that our
axiomatization of language machines is exceedingly close to the definition of
a big-step system over the NF game. Since big-step systems consist essentially
in a coalgebra on a functor associated to the game, it should not come as a
surprise that NF strategies---the final such coalgebra---are indeed the
terminal language machine. This suggests taking a closer look at the various
coalgebra presentations of game strategies (small-step systems and big-step
systems). Although they are usually heavier to manipulate than their
coinductive counterpart, their more intensional nature can be at times useful.

*A Logic for Strategies* #sym.space.quad Besides correctness w.r.t.
observational equivalence, a common property to investigate is the reverse
implication, i.e., completeness. When both correctness and completeness are true,
the model is said to be _fully abstract_. Following game semantical insights, it is
largely expected that our OGS model of effect-free languages can only hope to
be complete when restricted to _innocent_ strategies. Innocence is a property
of a strategy, essentially meaning that it plays the same moves in any two
observationally equivalent situations. Logically, it is a _safety property_, in the sense
that it can be expressed as the inability to play certain moves, solely based
on the past history: no bad moves are ever played.

More generally, other similarly structured predicates are of interest in game
semantics, such as _well-bracketedness_ (following a stack discipline for
answering questions) or _visibility_ (only observing variables which are in the
causal past). As such it would be useful to design a logic for strategy
properties, with temporal features.

Such a logic on the traces arising from coinductive automata has already been
proposed in the case of non-indexed interaction
trees~#mcite(<SilverZ21>)#mcite(dy: 4em, <YoonZZ22>). There are even very
expressive frameworks for reasoning with arbitrary monadic
computations~#mcite(dy: 5.7em, <MaillardAAMHRT19>). We conjecture that it is
possible to follow their lead and adapt these techniques to the indexed
setting.

Indexing, however, unlocks even more possibilities by building upon
the theory of _ornaments_~#mcite(dy: 3.7em, <McBride11a>)#mcite(dy: 5.8em, <Dagand17>).
Indeed, it is not too hard to enrich the positions of any game to keep track of
the history of what has been played. Then, any safety predicate on strategies
over a game can be backed into a _safe_ game, by requiring any move to be played
to be paired with a witness that it is safe with respect to the current
history. Ordinary strategies for this _safe_ game may then be proven equivalent to the
subset of strategies of the original game for which the safety property holds: the
fundamental theorem of correct-by-construction programming. Although ornaments
are still only known to some circles, the unreasonable effectiveness of
correct-by-construction programming in type theory is well established. We
believe that adapting this toolkit to our indexed trees could provide novel
reformulations and proof techniques for more advanced game semantical questions
in type theory.

*Effectful Language Machines* #sym.space.quad How do we scale our constructions
and proofs to effectful languages? This is the big question, as these languages
are the ones where OGS shine the most. The natural starting point is
to weaken the codomain of the evaluation map to

$ ogs.eval cl C th Gamma -> M th (ctx.norm_O th Gamma) $

for some arbitrary monad $M$, suitably modelling the language's effects. We can
play this game of replacing every instance of $delay.t$ with $M$ throughout our
development. What we shall obtain, is that disregarding indexing for simplicity, our
interaction tree monad has become the following _coinductive resumption
monad_~#mcite(<PirogG14>).
$ de("Res")_(M,Sigma) th X := nu A. th M th (X + Sigma th A) $

Notice that in the above situation, we do not have any $itree.tauF$ node
anymore, only $itree.retF$ and $itree.visF$. Instead, to recover unguarded
recursion we require that $M$ is (completely) #nm[Elgot]~#mcite(<PirogG14>),
intuitively that it behaves as $delay.t$. But partiality is ubiquitous when
manipulating coinductive game strategies, as for example it is entirely
expected that under some circumstances, composition of two _total_ strategies
may fail to be total. It is a sometimes overlooked practical insight
contributed by interaction trees, that for a whole lot of applications,
partiality should be built into the notion of automata. We thus conjecture that
it would be more fruitful to keep partiality under our control by reinstating
the #itree.tauF nodes and avoid depending on some particular language's monad
$M$ for evaluation effects. We should then study the following generalization
of interaction trees, where $M$ is an arbitrary (of course strictly positive)
monad.

$ de("itreeT")_(M,Sigma) th X := nu A. th M th (X + A + Sigma th A) $

We conjecture that with a suitable notion of weak bisimilarity, this
can be precised to form the initial #nm[Elgot] monad with a monad
morphism from $M$ and a natural transformation from $Sigma$. The hard part however, starts
even before proving any property: a good notion of _weak_ bisimilarity
remains elusive! In other words, given a _relator_ on $M$, we have
some trouble defining a good relator on $de("itreeT")_(M,Sigma)$ for
weak bisimilarity.

We could go on for quite some time, but perhaps this is already enough
open questions! Let us finish with more down-to-earth comments on our
code artifact.

*Proof Engineering* #sym.space.quad Throughout this thesis we have
said very little of the accompanying code artifact, but it leaves a
lot to be desired as it is nowhere near a reusable software library.
As one would imagine, a number of design mistakes have been made
during the development and partially patched out, so that it would
greatly benefit from a thorough re-architecturing. In fact,
because we tried to remain faithful to the actual code, some of these
oddities can at times be felt in the present manuscript.

A particularly central point is the absence of any definition of
_setoid_. Reasoning up-to some equivalence relation is central
throughout this thesis, but it has been worked out on a case-by-case
basis (mostly for value assignments and for interaction trees). As
such the artifact is left with some definitions which are too strict
for some use cases (substitution structures and language machines). We
have tried to make up for this in the manuscript by appealing to a
slightly nebulous "extensional equality" written $approx$, akin to a
fictive type class. The clean solution is quite simple: truly
parametrize by setoids and setoid families instead of types everywhere
it is relevant.

Milder points include spinning off our theory of substitution into a more
complete and separate library. Indeed Coq currently lacks such a library
implementing a modern take on intrinsically typed and scoped syntax.

Please do not hesitate to check the online
repository#margin-note(mark:
true)[#link("https://github.com/lapin0t/ogs")]: who knows, maybe by
the time you are reading these lines my compulsive tendency to shuffle
code around will have made everything tidier! On a more general note,
do not hesitate to reach out to me if any of the above ideas spark
your curiosity.

/*
improvements:
- game combinators, more categories
- denotational game semantics
- OGS is NF exponential
- clean setoids everywhere
- open composition, substitutivity of bisimulation, semantic characterization
  of substitutive equivalence
- better engineering the artifact
- NF bisim is the terminal language machine

- a logic for itrees, predicates on strategies (innocence, well-bracketedness)
- OGS for effectfull languages, mtrees
- semantics for FFI, interoperability
- instances with explicit substitutions, aka environments and closures

ccl:
- concrete, computational, automata-based pov on dialog models is nice
- propose a succint axiomatization of language with evaluator, based on the
  idea of an abstract machine
  - no syntax, only opaque states!
- a couple generically applicable tools: indexed itrees, scope structures
- L&S games are awesome

*/

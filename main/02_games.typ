#import "/lib/all.typ": *

= Coinductive Game Strategies

As we have seen, Operational Game Semantics, and more generally interactive
semantics, rest upon a dialogue following particular rules, a so-called two
player game. The main task in this chapter is be to properly define what is
meant by a "game", "strategy", "transition system", and to provide basic
building blocks for manipulating them. This chapter thus takes a step back and
temporarly puts on hold our concerns about programming language semantics, in
order to introduce the tools required to concretely represent games and
strategies in type theory. These tools are in part novel, but consist mostly of
natural extensions of pre-existing devices.

== A Matter of Computation

At heart, a strategy for a given two player game is an automaton of some kind,
in the loose sense that it has some internal states tracking information
required to choose moves, and alternates between two kinds of transitions.
Whenever it is their turn, i.e., in an active state, a strategy must choose a
move to play and transition to a passive state. And in a passive state, the
strategy must accept any possible move made by a hypothetic opponent and
transition to an active state.

In the classical literature on automata, these transitions would typically be
represented by a _relation_ between input states, moves and output states. On
the other hand, in game semantics the traditional approach is more extensional.
There, a strategy is represented by a subset of traces (finite or infinite
sequences of moves), i.e., by a formal language, subject to additional
conditions. While perfectly valid in a classical logic or set-theoretic
meta-theory, when translated directly to type theory, both of these
representations eschew the computational content of strategies.

Our basis for an idiomatic type theoretical encoding of automata follows the
notion of _interaction tree_ introduced by Li-yao Xia _et
al._~#mcite(<XiaZHHMPZ20>), originally motivated by representing executable
denotational semantics of programs with general recursion. Interaction trees
are a coinductive data structure encoding possibly non-terminating
computations, interacting with their environment by mean of uninterpreted
event. Recognizing "programs" as Player strategies, "environment" as yet
unknown Opponent strategies and "uninterpreted events" as move exchanges, we
are quite close to our setting of alternating two player games. However, there
are two remaining obstactles in order to apply interaction trees to our
usecase.

- *Duality.* We would like strategies and counter-strategies to have similar
  representations, intuitively simply by swapping the sets of moves allowed for
  each player. This is not directly possible with interaction trees, as the two
  kinds of moves do not have the same status. In interaction trees, the events are
  organized into a set of _queries_ $Q cl base.Set$, and for each query a set of
  _responses_ $R cl Q -> base.Set$. As such one cannot just swap queries and
  responses as they are not of the same sort.
- *Indexing.* In an interaction tree, while the set of allowed responses
  depends on the previous query, queries themselves do not dependend on anything.
  As such, all queries are allowed at any point where it is Player's turn to
  play. In the context of two player games, this is a strong restriction on
  expressivity, which forbids us to represent games where some Player moves are
  allowed at certain points of the game but not at others, dependending on what
  has been played before.

Happily, both of these points can be resolved by swapping interaction tree's
notion of event with the notion of game introduced by Paul Levy and Sam
Staton~#mcite(<LevyS14>). The rest of the chapter is organized as follows.

- In @sec-levy-staton I reconstruct Paul Levy and Sam Staton's notion of
  game and of coalgebraic transition system.
- In @sec-itree I introduce _indexed interaction trees_, a novel generalization of
  interaction trees adapted to the above notion of games. I introduce the
  definition of their bisimilarity and their general theory, lifted from the
  non-indexed setting.
- In @sec-iter I develop upon the theory of iteration operators, providing a
  novel _eventually guarded iteration_, applicable to the delay
  monad~#mcite(<Capretta05>), but also to indexed and non-indexed interaction
  trees.

== Levy & Staton Games <sec-levy-staton>

=== An Intuitive Reconstruction

The definition of game obtained by Levy & Staton in
#mcite(<LevyS14>) arises quite naturally from what is intuitively understood by
a "game". Let's build it up first hand.

In the common sense of the word, a game is described by the moves allowed at any
point of the play, together with winning conditions and their associated
rewards. As I am here only interested in games insofar as they provide a
framework for structured interactions, usual notions from classical game theory
such as "winning", "reward" or "optimal play" will be completely absent.
Moreover, I will restrict my attention to games where two agents play in
alternating fashion. As such, for my purpose, games will just consist of the
description of allowed moves.#margin-note[Games in such a retricted view---two
player, alternating, no notion of winning---are similar to combinatorial
games and might perhaps be more appropriately named _protocols_, as
typically arises in the field of computer networks.]

Starting from the idea that a game is described by the moves allowed for each
player, arguably the simplest formal translation is to say that a game consists
of a pair of two sets $(M^+, M^-)$, encoding the set of moves allowed for each
player. For example taking $M^+$ and $M^-$ to be both equal to the set of UTF-8
character strings, we can think of this as the "game of chatting" where the two
players are to alternatively exchange text messages. This definition readily
encodes simple kinds of interactions: at a coarse level we could argue that a
lot of low-level protocols consist in two players alternatively exchanging byte
sequences. However, games-as-set-pairs are very restrictive in the sense that
any move from say $M^+$ is valid at any point where it is the first player's
turn. As such, games-as-set-pairs are missing a shared game state, a game
_position_, something enabling the set of allowed moves to evolve over the
course of the dialogue. In particular, our game of interest, Operational Game
Semantics, makes use of such evolution of moves: since players introduce
variables while playing, moves mentioning some variable $x$ should only be
allowed after $x$ has been introduced.

Still, this definition has the quality of being quite symmetric: swapping the
two sets we get an involution $(M^+, M^-) |-> (M^-, M^+)$ exchanging the roles of
both players. There are two lessons to be learnt from this naive definition:

- A game should be described by a pair of two objects of the same sort, each
  describing what moves one player can do.
- For describing moves, mere sets can be a first approximation, but a bit too
  coarse for our purpose.

Back to the drawing board, let's refine this notion of games-as-set-pairs. As
we were missing game _positions_, on which moves could then depend, it is but
natural to assume a set of such positions. More precisely, we will assume two
sets of game positions $I^+$ and $I^-$, where it is respectively the first
player and the second player's turn to play. Then, instead of describing moves
by mere sets, we can describe them by two families $M^+ cl I^+ -> base.Set$ and
$M^- cl I^- -> base.Set$, mapping to each position the set of currently allowed
moves. Finally, we must describe how the position evolves after a move has been
played. This can be encoded by two maps $"next"^+ cl forall i^+, th M^+ th i^+ ->
I^-$ and $"next"^- cl forall i^-, th M^- th i^- -> I^+$. This leads us to the
following definitions.

#definition[Half-Game][
  Given $I, J cl base.Set$ a _half-game with input positions $I$
  and output positions $J$_ is given by the following record.
  $ & kw.rec th game.hg th I th J th kw.whr \
    & quad game.mv cl I -> base.Set \
    & quad game.nx th {i} cl game.mv th i -> J $
] <def-hg>

#definition[Game][
  #margin-note[This definition is called _discrete game_ by Levy &
    Staton~#num-cite(<LevyS14>).]
  Given $I^+, I^- cl base.Set$ a _game with active positions $I^+$
  and passive positions $I^-$_ is given by the following record.
  $ & kw.rec th game.g th I^+ th I^- th kw.whr \
    & quad game.client cl game.hg th I^+ th I^- \
    & quad game.server cl game.hg th I^- th I^+ $
] <def-g>

=== Example Games

Let us introduce a couple example games, to get a feel for their expressivity.

*Conway Games* #sym.space Conway games are an important tool in the study of
_combinatorial games_~#mcite(<Conway76>) and may in fact be considered their prime
definition. I will explain how they are an instance of our notion. The
definition of Conway games is exceedingly simple: a conway game $G cl
de("Conway")$ is given by two subsets of Conway games $G_L, G_R subset.eq
de("Conway")$. This self-referential definition should be interpreted as a
coinductive one. The left subset $G_L$ is to be thought of as the set of games
reachable by the left player in one move, and symmetrically for $G_R$.

#margin-note[For a more in-depth discussion of the two notions of subsets in
    type theory, see #text-cite(<HancockH06>, supplement: [pp. 194--198])]
In order to translate this definition into type theory, the only
question is how to represent subsets.
The most familiar one is the powerset construction, adopting the point-of-view
of subsets as predicates:

$ subs.Pow cl base.Set -> base.Set \
  subs.Pow th X kw.whr X -> base.Prop $

However there is another one, more intensional, viewing subsets as families:

$ kw.rec subs.Fam (X cl base.Set) cl base.Set kw.whr \
  quad subs.dom cl base.Set \
  quad subs.idx cl subs.dom -> X $

Because we want to easily manipulate the support of the two subsets $G_L$ and $G_R$,
i.e., the set of left moves and right moves, we adopt the second representation.

#let conway = (
  t: de("Conway"),
  lft: pr("left"),
  rgt: pr("right"),
  ls: de("LS-Conway"),
)

#definition[Conway Game][
    The set of _Conway games_ is given by the following record.

    $ kw.rec conway.t cl base.Set kw.whr \
      quad conway.lft cl subs.Fam th conway.t \
      quad conway.rgt cl subs.Fam th conway.t $
]

We can now give the Levy & Staton game of Conway games. As in a Conway game one
does not known whose turn it is to play, the sets of active and passive positions
will be the same. Moreover, the current position is in fact given by the current
Conway game.

#example[L&S Game of Conway Games][
  Notice that $I -> subs.Fam th J$ is just a reshuffling of $game.hg th I th J$:

  $ de("fam-to-hg") cl (I -> subs.Fam th J) -> game.hg th I th J \
    (de("fam-to-hg") th F) .game.mv th i := (F th i) .subs.dom \
    (de("fam-to-hg") th F) .game.nx th {i} th d := (F th i).subs.idx th d $

  Then, the Levy & Staton game of Conway games can be given as follows.

  $ conway.ls cl game.g th conway.t th conway.t \
    conway.ls .game.client := de("fam-to-hg") th conway.lft \
    conway.ls .game.server := de("fam-to-hg") th conway.rgt $
]

#wip[inj LS $=>$ Conway]

=== Coalgebraic Strategies

Following Levy & Staton we now define transition systems over a given game.

#definition[Half-Game Functors][
  Given a half-game $G cl game.hg th I th J$, we define as follows the
  _active interpretation_ and _passive interpretation of $G$_ as two functors
  $base.Set^J -> base.Set^I$, written $G game.extA -$ and $G game.extP -$.

  $ (G game.extA X) th i := (m cl G.game.mv th i) times X th (G.game.nx th m) \
    (G game.extP X) th i := (m cl G.game.mv th i) -> X th (G.game.nx th m) $
]

/*
#definition[Action Functor][
  Given a half-game $G cl game.hg th I th J$, and a family $R cl base.Set^I$,
  we define $game.actF_G^R cl base.Set^J -> base.Set^I$ the _action functor
  of $G$ with output $R$_ by the following data type.

  $ kw.dat game.actF_G^R th X th i cl base.Set kw.whr \
    quad game.retF cl R th i -> game.actF_G^R th X th i \
    quad game.tauF cl X th i -> game.actF_G^R th X th i \
    quad game.visF (m cl G.game.mv th i) cl X th (G.game.nx th m) -> game.actF_G^R th X th i $

#margin-note(dy: -7em)[
  Note that $game.actF_G^R th X$ is a notational shorthand for the coproduct in families $R
  + X + (G game.extA X)$.
]
]
*/

#definition[Coalgebraic Strategy][
  Given a game $G cl game.g th I^+ th I^-$ and an output family $R cl I^+ -> base.Set$,
  a _coalgebraic strategy over $G$ with output $R$_ is given by the following record.

  $ kw.rec strat.t th G th R kw.whr \
    quad strat.stp cl I^+ -> base.Set \
    quad strat.stn cl I^- -> base.Set \
    quad strat.play cl strat.stp => (R + strat.stp + G.game.client game.extA strat.stn) \
    quad strat.play cl strat.stn => (G.game.server game.extP strat.stp) $

  Where $X => Y := forall th {i}, th X i -> Y i$ denotes the morphism of families.
]

== Indexed Interaction Trees <sec-itree>

=== Definition

=== Bisimilarity

==== Coinduction with Complete Lattices

==== Strong Bisimilarity

==== Weak Bisimilarity

=== Monad Structure

=== Interpretation

== Iteration Operators <sec-iter>

=== Fixpoints of Equations

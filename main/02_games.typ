#import "/lib/all.typ": *

= Coinductive Game Strategies <ch-game>

As we have seen, operational game semantics, and more generally interactive
semantics, rest upon a dialogue following particular rules, a so-called two
player game. The main task in this chapter is to properly define what is
meant by "game", "strategy", and "transition system", and to provide basic
building blocks for manipulating them. This chapter thus takes a step back and
temporarily puts on hold our concerns about programming language semantics, in
order to introduce the tools required to concretely represent games and
strategies in type theory. These tools are in part novel, but consist mostly of
natural extensions of preexisting devices.

== A Matter of Computation

At heart, a strategy for a given two player game is an automaton of some kind,
in the loose sense that it has some internal states tracking information
required to choose moves, and alternates between two kinds of transitions.
Whenever it is its turn, i.e., in an active state, a strategy must choose a
move to play and transition to a passive state. And in a passive state, the
strategy must accept any possible move made by a hypothetical opponent and
transition to an active state.

In the classical literature on automata, these transitions would typically be
represented by a _relation_ between input states, moves and output states. On
the other hand, in game semantics, the traditional approach is more extensional.
There, a strategy is represented by a subset of traces (finite or infinite
sequences of moves), i.e., by a formal language, subject to additional
conditions. While perfectly valid in a classical logic or set-theoretic
metatheory, when translated directly to type theory, both of these
representations eschew the computational content of strategies.

Our basis for an idiomatic type theoretical encoding of automata follows the
notion of _interaction tree_ introduced by #nm[Xia] et
al.~#mcite(<XiaZHHMPZ20>), originally motivated by representing executable
denotational semantics of programs with general recursion. Interaction trees
are a coinductive data structure encoding possibly non-terminating
computation, interacting with its environment by means of uninterpreted
events. Recognizing "programs" as Player strategies, "environments" as yet
unknown Opponent strategies and "uninterpreted events" as move exchanges, we
are quite close to our setting of alternating two player games. However, there
are two remaining obstacles in order to apply interaction trees to our
use case.

- *Duality.* We would like strategies and counter-strategies to have similar
  representations, intuitively simply by swapping the sets of moves allowed for
  each player. This is not directly possible with interaction trees, as the two
  kinds of moves do not have the same status. In interaction trees, the events are
  organized into a set of _queries_ $Q cl base.Type$, and for each query a set of
  _responses_ $R cl Q -> base.Type$. As such one cannot just swap queries and
  responses as they are not of the same sort.
- *Indexing.* In an interaction tree, while the set of allowed responses
  depends on the previous query, queries themselves do not depend on anything.
  As such, all queries are allowed at any point where it is Player's turn to
  play. In the context of two player games, this is a strong restriction on
  expressivity, which forbids us to represent games where some Player moves are
  allowed at certain points of the game but not at others, depending on what
  has been played before.

Luckily, both of these points can be resolved by swapping the notion
of event from interaction trees, with the notion of game introduced by
#nm[Levy] & #nm[Staton]~#mcite(<LevyS14>). The rest of the chapter is
organized as follows.

- In @sec-levy-staton, we reconstruct #nm[Levy] & #nm[Staton]'s notion of
  game and of coalgebraic transition system.
- In @sec-itree, we introduce _indexed interaction trees_, a novel generalization of
  interaction trees adapted to the above notion of games.
- In @sec-bisim, we define their bisimilarity together with powerful reasoning
  principles based on a lattice-theoretic fixed point construction.
- In @sec-itree-monad, we give a little bit of structure to indexed interaction
  tree, mostly lifted from the non-indexed setting.
- In @sec-iter we develop upon the theory of iteration operators, providing a
  novel _eventually guarded iteration_, applicable to indexed interaction trees
  but also to the delay monad~#mcite(<Capretta05>) and to non-indexed interaction
  trees.

== #nm[Levy] & #nm[Staton] Games <sec-levy-staton>

=== An Intuitive Reconstruction

The definition of game obtained by #nm[Levy] & #nm[Staton] in
#mcite(<LevyS14>) arises quite naturally from what is intuitively understood by
a "game". Let's build it up first hand.

In the common sense of the word, a game is described by the moves
allowed at any point of the play, together with winning conditions and
their associated rewards. As we are here only interested in games
insofar as they provide a framework for structured interactions, usual
notions from classical game theory such as "winning", "reward" or
"optimal play" will be completely absent. Moreover, we will restrict our
attention to games where two agents play in alternating turns. Thus,
for my purpose, games will just consist of the description of allowed
moves.#margin-note[Games in such a restricted view---two-player,
alternating, no notion of winning---are similar to combinatorial games
and might perhaps be more appropriately named _protocols_, as
typically arises in the field of computer networks.]

Starting from the idea that a game is described by the moves allowed for each
player, arguably the simplest formalization is to say that a game consists
of a pair $(M^+, M^-)$ of sets, encoding the set of moves allowed for each
player. For example, taking $M^+$ and $M^-$ to be both equal to the set of #txsc[utf-8]
character strings, we can think of this as the "game of chatting" where the two
players are to alternatively exchange text messages. This definition readily
encodes simple kinds of interactions: at a coarse level we could argue that a
lot of low-level protocols consist in two players alternatively exchanging byte
sequences. However, games-as-set-pairs are very restrictive in the sense that
any move from, say, $M^+$ is valid at any point where it is the first player's
turn. Thus, games-as-set-pairs are missing a shared game state, a game
_position_, something enabling the set of allowed moves to evolve over the
course of the dialogue. In particular, our game of interest in OGS, makes use
of such evolution of moves: since players introduce variables while playing,
moves mentioning some variable $x$ should only be allowed after $x$ has been
introduced. 

Still, this definition has the advantage of being quite symmetric: swapping the
two sets, we get an involution $(M^+, M^-) |-> (M^-, M^+)$ exchanging the roles of
both players. There are two lessons to be learnt from this naive definition:

- A game should be described by a pair of two objects of the same sort, each
  describing what moves one player can do. 
- For describing moves, mere sets can be a first approximation, but are a bit too
  coarse for our purpose.

Back to the drawing board, let's refine this notion of games-as-set-pairs. As
we were missing game _positions_, on which moves could then depend, it is but
natural to assume a set of such positions. More precisely, we will assume two
sets of game positions $I^+$ and $I^-$, where it is respectively the first
player and the second player's turn to play. Then, instead of describing moves
by mere sets, we can describe them by two families $M^+ cl I^+ -> base.Type$ and
$M^- cl I^- -> base.Type$, mapping to each position the set of currently allowed
moves. Finally, we must describe how the position evolves after a move has been
played. This can be encoded by two maps $"next"^+ cl forall th {i^+} -> th M^+ th i^+ ->
I^-$ and $"next"^- cl forall th {i^-} -> th M^- th i^- -> I^+$. This leads us to the
following definitions.

#definition[Half-Game][
  Given $I, J cl base.Type$ a _half-game with input positions $I$
  and output positions $J$_ is given by a record of the following type.

  $ kw.rec th game.hg th I th J th kw.whr \
    pat(game.mv cl I -> base.Type,
        game.nx th {i} cl game.mv th i -> J) $
] <def-hg>

#definition[Game][
  #margin-note[This is called _discrete game_ by #nm[Levy] & #nm[Staton]~#num-cite(<LevyS14>).]
  Given $I^+, I^- cl base.Type$ a _game with active positions $I^+$
  and passive positions $I^-$_ is given by a record of the following type.

  $ kw.rec th game.g th I^+ th I^- th kw.whr \
    pat(game.client cl game.hg th I^+ th I^-,
        game.server cl game.hg th I^- th I^+) $
] <def-g>

=== Categorical Structure

In order to make (half-)games into a proper category, we will define their
morphisms. As games are parametrized over sets of positions, game morphisms
could be naturally defined as parametrized over position morphisms, in the
displayed style of #nm[Ahrens] and #nm[Lumsdaine]~#mcite(<AhrensL19>).
Yet we will resist the urge to dive too
deeply into the structure of games and leave most of it for further work to
expose. Indeed, we will require none of it for our main goal of proving
correctness of OGS. Moreover, as already noted by #nm[Dagand] and
#nm[McBride]~#mcite(<DagandM13>, supplement: "Sec. 1.3") in the similar setting
of indexed containers, describing the extremely rich structures at play requires
advanced concepts, such as framed bicategories and two-sided fibrations.

#definition[Half-Game Simulation][
  Given two half-games $A, B cl game.hg th I th J$, a _half-game simulation
  from $A$ to $B$_ is given by a record of the following type.

  $ kw.rec game.hsim th {I th J} th (A th B cl game.hg th I th J) kw.whr \
    pat(game.hstr {i} cl A .game.mv th i -> B .game.mv th i,
        game.hscoh {i} th (m cl A .game.mv th i) cl B .game.nx th (game.hstr th m) = A .game.nx th m) $
]


#definition[Simulation][
  Given two games $A, B cl game.g th I^+ th I^-$, a _game simulation from $A$
  to $B$_ is given by a record of the following type.

  $ kw.rec game.sim th {I^+ th I^-} th (A th B cl game.g th I^+ th I^-) kw.whr \
    pat(game.scli cl game.hsim th A .game.client th B .game.client,
        game.ssrv cl game.hsim th B .game.server th A .game.server) $
]

#remark[
The identity and composition of half-game simulations are given as follows.

$ "id" th {I th J} th (A cl game.hg th I th J) cl game.hsim th A th A \
  "id" :=
  pat(
    game.hstr th m & := m,
    game.hscoh th m & := base.refl,
  ) $

$ nar""compose""nar th {I th J} th {A th B th C cl game.hg th I th J} cl game.hsim th B th C -> game.hsim th A th B -> game.hsim th A th C \
  F compose G :=
  pat(
    game.hstr th m & := F .game.hstr th (G .game.hstr th m),
    game.hscoh th m & := ...
  ) $

The identity and composition of game simulations are then easily derived.

After defining the proper extensional equality on simulations (namely pointwise
equality of the $game.hstr$ projection), we could prove that the above
structure on half-games verifies the laws of a category, and easily deduce the
same fact on games. For the reasons explained above, we leave this sketching as it is.

]

#remark[
  $game.hg$ extends to a strict functor $"Set"^"op" times "Set" -> "Cat"$ as witnessed
  by the following action on morphisms, which we write curried and in infix style.

  $ ar game.reixl ar game.reixr ar cl (I_2 -> I_1) -> game.hg th I_1 th J_1 -> (J_1 -> J_2) -> game.hg th I_2 th J_2 \
    f game.reixl A game.reixr g :=
    pat(game.mv th i & := A .game.mv th (f th i),
        game.nx th m & := g th (A .game.nx th m)) $

  The identity and composition laws of this functor hold _definitionally_.
]


=== Example Games <sec-game-example>

Let us introduce a couple example games, to get a feel for their expressivity.

*Dual Game* #sym.space Perhaps the simplest combinator on games that we can
devise is _dualization_. This allows us to swap the roles of the client and
the server. It is defined as follows.

$ nar^game.opp th {I^+ th I^-} cl game.g th I^+ th I^- -> game.g th I^- th I^+ \
  G^game.opp := pat(
    game.client & := G .game.server,
    game.server & := G .game.client,
  ) $

Remark that dualization is _strictly_ involutive, i.e., $nar^game.opp compose
nar^game.opp$ is definitionally equal to the identity function.

*Nim* #sym.space.quad The game of Nim is typically played with
matchsticks. A number of matchsticks are on the playing board, grouped in several
_heaps_. The two players must in turn take at least one matchstick away from one
heap. They might take as many matchsticks as they wish, so as long as they all
belong to the same heap. Implicitly, one looses when it is not possible to play, i.e.,
when there are no matchsticks left.

Let us first encode the Nim game with a single heap. It is a symmetric game,
where both active and passive positions are given by a natural number $n$, the
number of available matchsticks in the only heap. A move is then an natural
number no smaller than one and no greater than $n$. Equivalently, we can say
that it is $1 + i$, where $i$ is any natural number strictly smaller than $n$.
Conveniently, the encoding in type theory of naturals strictly smaller than a
given one are a well-known inductive family, the canonical _finite sets_
$kw.dat th base.fin cl base.nat -> base.Type$ with constructors given as
follows.

#mathpar(block: true,
  inferrule("", $base.fze cl base.fin th (base.su th n)$),
  inferrule($i cl base.fin th n$, $base.fsu th i cl base.fin th (base.su th n)$),
)

Given $n cl base.nat$ and $i cl base.fin th n$, the substraction $n - (1 + i)$ is
easily expressed.

#let nsubf = de($"sub"_f$)
#let nsubfi = de(cbin($-_f$))
#let nim1h = de($"Nim"^"half"_1$)
#let nim1g = de($"Nim"_1$)
#let nim3g = de($"Nim"_3$)

$ nar""cnorm(nsubfi)nar cl (n cl base.nat) -> base.fin th n -> base.nat $
#v(-0.8em)
$ & base.su th n nsubfi && base.fze && := n \
  & base.su th n nsubfi && base.fsu th i && := n nsubfi i $

We thus obtain the single-heap Nim game as follows.

#mathpar(block: true, spacing: 1fr,
  $nim1h cl game.hg th base.nat th base.nat \
   nim1h := pat(
    game.mv th n & := base.fin th n,
    game.nx th {n} th i & := n nsubfi i,
  )$,
  $nim1g cl game.g th base.nat th base.nat \
   nim1g := pat(
     game.client := nim1h,
     game.server := nim1h,
   )$
)

We could obtain the many-heap Nim game by a similar construction. We would define
the positions as lists of natural numbers, the moves as first selecting a heap and
then choosing a number of matchsticks to take away, etc. Let us seek a more structured
approach. Intuitively, the multi-heap Nim game is just a some fixed number of
copies of the single-heap game played simultaneously, in _parallel_. In case
of two copies, the game positions consists of pairs of single-heap Nim
positions. A move is then defined as choosing either a single-heap move on the
first position or on the second. Let us define this as a generic binary
combinator on games.

#let csumh = $de(+^"half")$
#let csumg = $de(+^"G")$

$ nar""cnorm(csumh)nar th {I th J} cl game.hg th I th I -> game.hg th J th J -> game.hg th (I base.prod J) th (I base.prod J) \
  A csumh B := pat(
    game.mv th (i, j) & := A .game.mv th i base.sum B .game.mv th j,
    game.nx th (i, j) th (base.inj1 th m) & := (A .game.nx th m, j),
    game.nx th (i, j) th (base.inj2 th m) & := (i, B .game.nx th m),
  ) $

$ nar""cnorm(csumg)nar th {I th J} cl game.g th I th I -> game.g th J th J -> game.g th (I base.prod J) th (I base.prod J) \
  A csumg B := pat(
    game.client & := A .game.client csumh B .game.client,
    game.server & := A .game.server csumh B .game.server,
  ) $

A many-heap Nim game, say with three heaps can then be simply be given as the following sum.

$ nim3g cl game.g th (base.nat base.prod base.nat base.prod base.nat) th (base.nat base.prod base.nat base.prod base.nat) \
  nim3g := nim1g csumg nim1g csumg nim1g $

#remark[
  Note that in the above binary sum of games, we constrained the games to have
  only a single set of positions. Indeed, it is crucial in Nim that one can
  play two times in a row in the same heap, while the opponent played in an
  other one. This only makes sense when the active and passive positions are
  the same.

  For the curious reader, in case the active and passive positions differ, we can
  devise the following "parallel" sum $de(⅋^"G")$, where the server is restricted to respond
  in the game that the client chose.

  #let psumh = $de(cbin(⅋^"h"))$
  #let xsumh = $de(cbin(times.circle^"h"))$
  #let psumg = $de(cbin(⅋^"G"))$

  $ nar""cnorm(psumh)nar cl game.hg th I_1 th J_1 -> game.hg th I_2 th J_2 \
    quad quad quad -> game.hg th (I_1 base.prod I_2) th ((J_1 base.prod I_2) base.sum (I_1 base.prod J_2)) \
    A psumh B := pat(
      game.mv th & (i_1, i_2) & := A .game.mv th i_1 base.sum B .game.mv th i_2,
      game.nx th & {i_1, i_2} th (base.inj1 th m) & := base.inj1 th (A .game.nx th m, i_2),
      game.nx th & {i_1, i_2} th (base.inj2 th m) & := base.inj2 th (i_1, B .game.nx th m),
    ) $

  $ nar""cnorm(xsumh)nar cl game.hg th I_1 th J_1 -> game.hg th I_2 th J_2 \
    quad quad quad -> game.hg th ((I_1 base.prod J_2) base.sum (J_1 base.prod I_2)) th (J_1 base.prod J_2)  \
    A xsumh B := pat(
      game.mv th & (base.inj1 th (i_1, j_2)) & := A .game.mv th i_1,
      game.mv th & (base.inj2 th (j_1, i_2)) & := B .game.mv th i_2,
      game.nx th & {base.inj1 th (i_1, j_2)} th m & := (A .game.nx th m , j_2),
      game.nx th & {base.inj2 th (j_1, i_2)} th m & := (j_1, B .game.nx th m),
    ) $

  $ nar""cnorm(psumg)nar th {I th J} cl game.g th I th I -> game.g th J th J \
    quad quad quad -> game.g th (I_1 base.prod I_2) th ((J_1 base.prod I_2) base.sum (I_1 base.prod J_2)) \
    A psumg B := pat(
      game.client & := A .game.client psumh B .game.client,
      game.server & := A .game.server xsumh B .game.server,
    ) $

  This game, or rather its #nm[De Morgan] dual $A de(times.circle^"G") B := (A^game.opp psumg
  B^game.opp)^game.opp$ has been used by #nm[Levy] & #nm[Staton]~#mcite(<LevyS14>) in their
  study of game strategy composition.
]

#let conway = (
  t: de(txsc("Conway")),
  lft: pr("left"),
  rgt: pr("right"),
  ls: de("G-" + txsc("Conway")),
)

*#nm[Conway] Games* #sym.space.quad #nm[Conway] games are an important tool in the
study of _combinatorial games_~#mcite(<Conway76>) and may in fact be considered
their prime definition. We sketch here how they are an instance of our notion.
They admit the following exceedingly simple definition: a #nm[Conway] game $G cl
conway.t$ is given by two subsets of #nm[Conway] games $G_L, G_R subset.eq
conway.t$. The left subset $G_L$ is to be thought of as the set of games
reachable by the left player in one move, and symmetrically for $G_R$.
Depending on whether this self-referential definition is interpreted inductively
or coinductively, one obtains respectively the usual finite #nm[Conway] games, or
their infinite variant, sometimes called _hypergame_.
For more background, see #nm[Honsell] & #nm[Lenisa]~#mcite(<HonselL11>), as well
as #nm[Joyal]~#mcite(dy: 3em, <Joyal77>).

In order to translate this definition into type theory, the only
question is how to represent subsets.
The most familiar one is the powerset construction, adopting the point of view
of subsets as (proof-relevant) predicates:

$ subs.Pow cl base.Type -> base.Type \
  subs.Pow th X kw.whr X -> base.Type $

However there is a different, more intensional one, viewing subsets as
families#margin-note(mark: true)[
  For a more in-depth discussion of the two notions of subsets in type theory,
  see #text-cite(<HancockH06>, supplement: [pp. 194--198])
]. In
this view, a subset is given by a type which encodes its _domain_, or _support_,
or _total space_, and by a decoding function from this domain to the original set.

$ kw.rec subs.Fam th (X cl base.Type) cl base.Type kw.whr \
  pat(subs.dom cl base.Type,
      subs.idx cl subs.dom -> X) $

We can go back and forth between the two representations, but only at the cost
of a bump in universe levels. As such, to avoid universe issues and keep the manipulation
tractable, it is important to choose the side which is most practical for the
task at hand. Because we want to easily manipulate _elements_ of the two
subsets $G_L$ and $G_R$, i.e., in this context the actual left moves and right
moves, it is best to have we have them readily available by adopting the second
representation. More pragmatically, the following definition would not
go through when using $subs.Pow$, as it is not a _strictly positive_ operator on
types.

#definition[#nm[Conway] Game][
  The set of potentially infinite _#nm[Conway] games_ is given by elements of the following
  coinductive record.

  $ kw.rec conway.t cl base.Type kw.whr \
    pat(conway.lft & cl subs.Fam th conway.t,
        conway.rgt & cl subs.Fam th conway.t) $
]

We can now give a #nm[Levy] & #nm[Staton] game of #nm[Conway] games. As in a
#nm[Conway] game it is ambiguous whose turn it is to play, the sets of
active and passive positions will be the same. Moreover, the current position
is in fact given by the current Conway game.

#example[Game of #nm[Conway] Games][
  We start by noticing that $I -> subs.Fam th J$
  is just a shuffling of $game.hg th I th J$:

  $ de("fam-to-hg") th {I th J} cl (I -> subs.Fam th J) -> game.hg th I th J \
    de("fam-to-hg") th F :=
      pat(game.mv th i & := (F th i) .subs.dom,
          game.nx th {i} th m & := (F th i).subs.idx th m) $

Then, the _game of #nm[Conway] games_ can be given as follows.

  $ conway.ls cl game.g th conway.t th conway.t \
    conway.ls :=
      pat(game.client := de("fam-to-hg") th conway.lft,
          game.server := de("fam-to-hg") th conway.rgt) $
]

To make this example more solid, we should relate the notion strategy in the
sense of #nm[Conway] to the strategies on #conway.ls in the sense of
#nm[Levy] & #nm[Staton]. But let's not get ahead of ourselves, as the latter
are only introduced in the next section. We will leave this little sketch as
it is.

=== Strategies as Transition Systems

Following #nm[Levy] & #nm[Staton]~#num-cite(<LevyS14>), we now define client
strategies as transition systems over a given game. We will only define
_client_ strategies, since _server_ strategies can be simply derived from
client strategies on the dual game---the prime benefit of our symmetric notion
of game. We first need to define two interpretations of half-games as functors.


#definition[Half-Game Functors][
  Given a half-game $G cl game.hg th I th J$, we define the
  _active interpretation_ and _passive interpretation of $G$_ as functors
  $base.Type^J -> base.Type^I$, written $G game.extA ar$ and $G game.extP ar$ and defined as follows.

  $ & (G game.extA X) && th i := (m cl G.game.mv th i) #h(0.4em) times  && X th (G.game.nx th m) \
    & (G game.extP X) && th i := (m cl G.game.mv th i) -> && X th (G.game.nx th m) $
] <def-hg-ext>

#definition[Transition System][
  Given a game $G cl game.g th I^+ th I^-$ and a family $X cl base.Type^(I^+)$,
  a _transition system over $G$ with output $X$_ is given by records of the following type.
  #margin-note(dy: -2.7em)[
    In #nm[Levy] & #nm[Staton]~#num-cite(<LevyS14>), the output parameter $X$ is not present and this is
    called a _small-step system over $G$_. We can recover their
    definition by setting $X th i := base.bot$.
  ]

  $ kw.rec strat.t_G th X kw.whr \
    pat(strat.stp cl I^+ -> base.Type,
        strat.stn cl I^- -> base.Type,
        strat.play cl strat.stp ctx.arr X base.sum strat.stp base.sum G.game.client game.extA strat.stn,
        strat.coplay cl strat.stn ctx.arr G.game.server game.extP strat.stp) $
] <def-tsys>
#remark[
  In the above, $X ctx.arr Y := forall th {i} -> X th i -> Y th i$ denotes a
  morphism of families. Moreover, we have slightly abused the $base.sum$
  notation, silently using its pointwise lifting to families $(X base.sum Y) th i
  := X th i base.sum Y th i$.

  More generally, given $n$-ary families $X, Y cl base.Type^(I_1,.., I_n)$, the notation
  $X ctx.arr th Y$ will mean the following implicitly $n$-ary indexed function space.
  $ forall th {i_1 th .. th i_n} -> X th i_1 th .. th i_n -> Y th i_1 th .. th i_n $

  We will regularly implicitly lift constructions pointwise to families, although
  we try to say it every time we encounter a new one.
]


There is a lot to unpack here. First the states: instead of a mere set, as is
usual in a classical transition system, they here consist of two families
#strat.stp, #strat.stn _over_ respectively the active and passive game
positions. It is important not to confuse _positions_ and _states_. The former
consists of the information used to determine which moves are allowed to be
played. The latter consists of the information used by a given strategy to
determine how to play. Their relationship is similar to that of types to terms.

The $strat.play$ function takes as inputs an active position $i cl I^+$, an
active state  $s cl strat.stp th i$  over $i$ and returns one of three things:

$X th i$ ~~ _"return move"_
#block(inset: (x: 1.5em, bottom: 1em), spacing: 0.8em)[
  This case was not present in #nm[Levy] & #nm[Staton]~#num-cite(<LevyS14>), but
  it allows a strategy to end the game, provided it exhibits an output. As we
  will see with interaction trees in @sec-itree, this allows to equip transition
  systems with a monad structure, an important tool for compositional manipulation.
]

$strat.stp th i$ ~~ _"silent move"_
#block(inset: (x: 1.5em, bottom: 1em), spacing: 0.8em)[
  In this case, the strategy postpones progression in the game. This case
  allows for strategies to be _partial_ in the same sense as #nm[Capretta]'s
  #delay.t monad~#mcite(<Capretta05>). _Total strategies_ without this case would
  make perfect sense, but we are interested in arbitrary, hence partial, computations.
]

$(G.game.client game.extA strat.stn) th i$ ~~ _"client move"_
#block(inset: (x: 1.5em, bottom: 1em), spacing: 0.8em)[
  By @def-hg-ext, this data consists of a client move valid at the current position $i$

  $ m cl G .game.client"".game.mv th i, $

  together with a passive state over the next position

  $ x cl strat.stn th (G .game.client"".game.nx th m). $

  This case is the one which actually _chooses_ a move and sends it to a hypothetical opponent.
]

The #strat.coplay function is simpler. By @def-hg-ext, it takes a passive
position, a passive state over it, and a currently valid _"server move"_, and must
then return an active state over the next position.

#remark[
  It might seem as if the hypothetical opponent must be pure, as return and
  silent moves appear in #strat.play but not in #strat.coplay, but this is not the case.
  Recall that we are working
  with an alternating game. The intent is that the transition system specifies
  the behavior of a strategy when the client is in control of the game. When a
  hypothetical opponent plays a return move or silent move, they do not give the
  control back to the client. As such the client does not have anything to do in
  these cases, and is in fact unaware of these kinds of moves played by the server.
]

== Strategies as Indexed Interaction Trees <sec-itree>

In @def-tsys, we have defined strategies similarly to #nm[Levy] and
#nm[Staton]~#mcite(<LevyS14>), that is, by a state-and-transition-function
presentation of automata. This representation is theoretically satisfying,
however most of the time it is painful to work with formally. As an example,
let's assume we want to define a binary combinator, taking two transition systems as
arguments and returning a third one. Each of the two inputs is a dependent record with
four fields, so that we have to work with eight input components to define the
resulting transition systems, itself consisting of two families of states, and
then, depending on these new states, two suitable transition functions. This is
a lot to manage!

This unwieldiness is well known: while useful, writing state-machine-like code
explicitly is closely linked to the dreaded _spaghetti code_ and _callback hell_. It is
perhaps the prime reason why widely used programming languages have started
organizing it more soundly with syntactic facilities like the #txtt("yield") keyword of python's
_generators_#margin-note[
  For enlightening background on Python's generator syntax, see for example the Motivation
  section of the #link("https://peps.python.org/pep-0255/")[PEP 255].
] or the #txtt("await") keyword for sequencing asynchronous _promises_ (or _awaitables_),
now common in event-driven programming. Both of these concepts are automata in
disguise. Their associated syntactic constructs allow one to write automata
featuring bespoke state transitions (producing a sequence element,
sleeping in wait of a network response) as if they were normal code. As the precise
definition of the state space is left implicit and for the language implementation to
work out, it can no longer be manipulated by the programmer. What is left is an
_opaque_ notion of automaton (e.g., generators or awaitable objects), for which the only possible
operation is _stepping_, i.e., running until the next transition.

These syntactic features have two benefits. First, we can program automata
mostly as we do for normal functions, only sprinkling some automata-specific
primitives where required. Second, automata are now black boxes, in a sense
much like functions. This makes them quite a bit easier to pass around as their
internal implementation details are tightly sealed away. In this section we
will apply the same methodology to the definition of transition systems over
games and this will bring us to our first contribution: _indexed interaction
trees_.

=== From Games to Containers

Notice that given $G$ and $R$, @def-tsys is exactly the definition of a coalgebra for the
following endofunctor on $base.Type^(I^+) times base.Type^(I^-)$.

$ (A^+, A^-) #h(0.4em) |-> #h(0.4em) (#h(0.2em) X base.sum A^+ base.sum G.game.client game.extA A^- #h(0.2em) , #h(0.4em) G.game.server game.extP A^+ #h(0.2em)) $

Then, as by definition any coalgebra maps uniquely into the final coalgebra, it
is sufficient to work with this final coalgebra, whose states intuitively
consist of infinite coinductive trees, extensionally describing the traces of
any possible transition system over $G$. This "universal" state space---the
state space of the final coalgebra---will be our core notion of automata.

However, we will not construct this final coalgebra directly, but start by
simplifying the setting slightly. Our motivation is the following. We insisted
on having a clearly symmetric notion of game, in order to easily swap the
point of view from client to server, a crucial concept in two player games.
Strategies however, are inherently biased to one side. There is "our" side,
by convention the side of the client, on which we _emit_ moves, and the
side of the server, on which we _receive_ moves. Moreover, as we explained,
a transition system only specifies what can happen when the client is in control
of the game, i.e., in active positions. As such it is more
annoying than anything else to have our constructions like the above
endofunctor take place in a product category, forcing upon us _two_ kinds of
positions, _two_ kinds of states and _two_ kinds of transitions.

The trick to make the whole passive side disappear is to group in one atomic
unit the act of sending and then receiving a move. In other words, we can
consider a compound transition, where, starting from an active position, a
strategy emits a move, waits for an opponent move, and attains a new active
position. This exhibits strategies as coalgebras for the following functor.

$ A |-> X base.sum A base.sum G.game.client game.extA (G.game.server game.extP A) $

We can apply this "fusing" trick not only to strategies but also to games.
Quite satisfyingly, when forgetting about the passive positions games will morph into the well-known notion of
indexed polynomial functors, or more precisely their type-theoretic incarnation
as _indexed containers_~#mcite(dy: -0.7em, <AltenkirchGHMM15>). As such, our
notion of strategy will not directly be parametrized by a game, but more
generally by a biased representation derived from it: an indexed container. Let
us introduce indexed containers and their relationship to games.

#definition[Indexed Container][
  Given $I cl base.Type$, an _indexed container with positions $I$_ is given
  by records of the following type.

  $ kw.rec icont.t I cl base.Type kw.whr \
    pat(icont.qry cl I -> base.Type,
        icont.rsp th {i} cl icont.qry th i -> base.Type,
        icont.nxt th {i} th {q cl icont.qry th i} cl icont.rsp th q -> I) $
]

#definition[Game to Container][
  There is a functor from games to containers defined on object as follows.

  $ g2c(ar) cl game.g th I^+ th I^- -> icont.t th I^+ \
    g2c(A) :=
      pat(icont.qry th i & := A .game.client"".game.mv th i,
          icont.rsp th q & := A .game.server"".game.mv th (A .game.client"".game.nx th q),
          icont.nxt th r & := A .game.server"".game.nx th r) $
]

Like games, containers can be interpreted as functors.

#definition[Extension of a Container][
  Given an indexed container $Sigma cl icont.t th I$, we define its _extension_
  $icext(Sigma) cl base.Type^I -> base.Type^I$ as the following functor.

  $ icext(Sigma) th X th i :=
      (q cl Sigma .icont.qry th i)
      times ((r cl Sigma .icont.rsp th q) -> X th (Sigma .icont.nxt th r)) $
]

Notice that the mapping from games to containers preserves the functor interpretation,
in the sense that for all $A cl game.g th I^+ th I^-$, the functor
$A.game.client game.extA (A.game.server game.extP ar))$ is definitionally equal
to $icext(g2c(A))$. As such, our compound transition function can be recast as a
coalgebra for the following functor.

$ A |-> X base.sum A base.sum icext(g2c(G)) th A $

#remark[
  As a matter of fact, as hinted at the beginning of this chapter, I went through this
  journey backwards. Starting from notions of strategies such as interaction
  trees~#mcite(dy: -7em, <XiaZHHMPZ20>) or interaction structures~#mcite(dy: -2em, <HancockH06>)
  where "games" are understood as polynomial functors, I had trouble obtaining
  a sensible notion of dual game. With the realization that such polynomials
  can be "cut in halves", I arrived at #nm[Levy] & #nm[Staton]'s more symmetric
  notion of game.
]

#remark[
  Although games include information about passive positions which containers
  do not, we can guess an over approximation of this information and embed
  containers into games as follows.

  $ de(ceil.l) ar de(ceil.r) cl (Sigma cl icont.t th I) -> game.g th I th ((i cl I) times Sigma .icont.qry th i) \
    de(ceil.l) Sigma de(ceil.r) :=
      pat(game.client & := pat(game.mv th i & := Sigma .icont.qry th i,
                               game.nx th {i} th m & := (i , m)),
          game.server & := pat(game.mv th "(" i "," m ")" & := Sigma .icont.rsp th m,
                               game.nx th m & := Sigma .icont.nxt th m)) $

  We observe in passing that $g2c(ar) compose de(ceil.l) ar de(ceil.r)$ is
  _definitionally_ equal to the identity function on containers.

  This embedding suggests that although our symmetric notion of game is more
  _precise_ than indexed containers, it is equally _expressive_. Indeed, we
  conjecture that $de(ceil.l)ar de(ceil.r)$ and $g2c(ar)$ exhibit indexed
  containers as a reflective subcategory of games, but we have not introduced
  enough categorical structure to make this statement precise.
]

=== Indexed Interaction Trees

Now that have seen how indexed containers provide us with a biased, but more
succinct description of games, we can temporarily forget about games to
focus on indexed containers. Recall that we observed transition systems as
coalgebras and that our goal was to define opaque _strategies_ as elements
of the final coalgebra. In our simplified setting, given a container $Sigma$
and an output family $X$, this amounts to constructing the following
coinductive family, of _indexed interaction trees_.

$ nu A. th X base.sum A base.sum icext(Sigma) th A $

Our definition of this family proceeds in two steps. First we define the
_action_ functor

$ F th X := X base.sum A base.sum icext(Sigma) th A, $

and only then, we form the coinductive fixed point $nu F$. Although seemingly
innocuous, this separation has its importance. Because the head type former of
$F$ is the disjoint union $base.sum$, it would seem natural to implement this definition as
a coinductive _data_ type with three constructors. However, for metatheoretical
reasons, it is largely proscribed to pattern-match on coinductive
objects#margin-note(dy: -3em, mark: true)[
  Although Rocq allows it, it is folklore knowledge that this breaks subject
  reduction. See #text-cite(<McBride09>)
]. As such, we first define the action functor as a data type, and then define
its final coalgebra as a coinductive _record_ type with a single projection.

#definition[Action Functor][
  Given a signature $Sigma cl icont.t th I$ and an output $X cl
  base.Type^I$, the _action on $Sigma$ with output $X$_,
  $kw.dat itree.F_Sigma th X cl base.Type^I -> base.Type^I$ is given by
  the following constructors.

  #mathpar(block: true,
    inferrule($x cl X th i$, $itree.retF th r cl itree.F_Sigma th X th A th i$),
    inferrule($t cl A th i$, $itree.tauF th t cl itree.F_Sigma th X th A th i$),
    inferrule(
      ($q cl Sigma .icont.qry th i$,
       $k cl (r cl Sigma .icont.rsp th q) -> A th (Sigma .icont.nxt th r)$),
      $itree.visF th q th k cl itree.F_Sigma th X th A th i$
    ),
  )

  $itree.F$'s action on morphisms is without surprise, in fact it is functorial in
  both arguments. We give it by overloading the name $itree.F_Sigma$.

  $ itree.F_Sigma cl (X_1 ctx.arr X_2) -> (A_1 ctx.arr A_2) \
    quad quad -> itree.F_Sigma th X_1 th A_1 ctx.arr itree.F_Sigma th X_2 th A_2 $
  #v(-0.8em)
  $ & itree.F_Sigma th f th g th (itree.retF th x) && := itree.retF th (f th x) \
    & itree.F_Sigma th f th g th (itree.tauF th t) && := itree.retF th (g th t) \
    & itree.F_Sigma th f th g th (itree.visF th q th k) && := itree.visF th q th (kw.fun th r |-> g th (k th r)) \
  $
]

Being itself an indexed polynomial functor, $itree.F_Sigma th R$ has a
thoroughly understood theory of fixed points~#mcite(<AltenkirchGHMM15>) and we can
form its final coalgebra as a coinductive family which is accepted by most
proof assistants.

#definition[Indexed Interaction Tree][
  Given a signature $Sigma cl
  icont.t th I$ and an output $X cl base.Type^I$, the family of
  _indexed interaction trees on $Sigma$ with output $X$_, denoted by
  $itree.t_Sigma th X cl base.Type^I$, is given by coinductive records of the following
  type.

  $ kw.rec itree.t_Sigma th X th i cl base.Type kw.whr \
    pat1(itree.obs cl itree.F_Sigma th X th (itree.t_Sigma th X) th i) $

  Furthermore, define the following shorthands:

  $ & itree.ret th x      & := & pat1(itree.obs := itree.retF th x) \
    & itree.tau th t      & := & pat1(itree.obs := itree.tauF th t) \
    & itree.vis th q th k & := & pat1(itree.obs := itree.visF th q th k) $
] <def-itree>

#remark[
  Note that in accordance with Agda and Rocq, our type theory does not assume the
  #sym.eta\-law on coinductive records. As such, the above definition
  technically only constructs a _weakly_ final coalgebra. Doing otherwise
  would require switching to a slightly more extensional type theory, such as
  observational type theory~#mcite(<McBride09>).
]

The above definition is to interaction trees~#mcite(<XiaZHHMPZ20>)
what inductive families are to inductive data types. As we will discover
in the remainder of this chapter, all of the monadic theory of interaction
trees lifts neatly to this newly indexed setting.

Before moving on to define bisimilarity and other useful structure, let us
first link this definition to transition systems over games. First, as indexed
interaction trees are parametrized over containers, let us start by defining
_game_ strategies.

#definition[Strategies][
  Given a game $G cl game.g th I^+ th I^-$ and output $X cl base.Type^(I^+)$,
  the active and passive _strategies over $G$ with output $R$_ are defined as follows.

  #mathpar(block: true, spacing: 1fr,
    $game.stratA_G th X cl I^+ -> base.Type \
     game.stratA_G th X := itree.t_floor(G) th X$,
    $game.stratP_G th X cl I^- -> base.Type \
     game.stratP_G th X := G.game.server game.extP game.stratA_G th X$)
] <def-strat>

#definition[Strategy System][
  Given a game $G cl game.g th I^+ th I^-$ and output $X cl base.Type^(I^+)$,
  active and passive strategies are the states of a small step system over $G$
  with output $X$ defined as follows.

  $ game.strat_G th X cl strat.t_G th X \
    game.strat_G th X := \
    pat(
      strat.stp := game.stratA_G th X,
      strat.stn := game.stratP_G th X,
      strat.play th s := kw.case th s .itree.obs \
        pat(
          itree.retF th x & := base.xinj1 th x,
          itree.tauF th t & := base.xinj2 th t,
          itree.visF th q th k & := base.xinj3 th (q, k)
        ),
      strat.coplay th k th m := k th m,
    ) $

  $base.xinj1$, $base.xinj2$ and $base.xinj3$ denote the obvious injections
  into the ternary disjoint union.
]

#definition[System Unrolling][
  For any system $S cl strat.t_G th X$, the active and passive states can be
  respectively _unrolled_ to active and passive strategies. The mapping is
  given by the following two mutually coinductive definitions.

  $ itree.unrollA cl S .strat.stp ctx.arr game.stratA_G th X \
    itree.unrollA th s := \
    pat(itree.obs := kw.case th S .strat.play th s \
    pat(
            base.xinj1 th x      & := itree.retF th x,
            base.xinj2 th s      & := itree.tauF th (itree.unrollA th s),
            base.xinj3 th (m, s) & := itree.visF th m th (itree.unrollP th s))) \
    \

    itree.unrollP cl S .strat.stn ctx.arr game.stratP_G th X \
    itree.unrollP th s th m := itree.unrollA th (S .strat.coplay th s th m)
    $
] <def-unroll>
#remark[
  The above unrolling functions can be shown to be the computational part of
  the unique coalgebra morphism between a transition system $S$ and the
  strategy system $game.strat_G th X$. We do not prove it formally, as it
  would require properly defining transition system morphisms and their
  extensional equivalence.
]

#remark[
  The above notion of strategy is quite different to the one given by #nm[Levy]
  & #nm[Staton]~#mcite(<LevyS14>) (Def. 2). At a high level it serves a
  similar purpose, namely obtaining an opaque representation for
  transition systems, which forgets about implementation details. In line
  with the traditional set-theoretic presentation of game semantics, they
  define strategies as subsets of finite _traces_. These intuitively consist in
  the set of all the finite approximations of all the possible paths through
  a strategy tree (discounting silent steps). Technically, such as set must
  verify some conditions to be considered well-formed, mainly a prefix
  closure condition (to be considered a valid set of finite approximations),
  as well as a determinism condition on client moves. We provide a couple
  comments but leave a more formal comparison for future work.

  By virtue of representing a strategy as a set of valid traces, their notion of
  strategy equivalence is a _trace equivalence_. Yet because the considered
  strategies are deterministic, bisimulation and trace equivalence are known
  to coincide. We conjecture that this can be shown in type theory, in other
  words, constructively, the final coalgebra of $itree.F_Sigma th X$ _embeds_
  into strategies defined as some predicates on traces.

  Although #nm[Levy] & #nm[Staton] do not prove it, we conjecture that in
  classical set theory, one should be able to show that our notion and
  theirs are isomorphic, in other words, that strategies as traces are indeed
  a final coalgebra. There is however no hope of such result in type theory
  without further axioms, for two reasons. First, the determinism condition
  restricts valid plays to be extended by a unique client move. We conjecture
  that deducing a constructive function computing the next move would amount to
  a form of unique choice principle. Second, partiality of strategies is
  handled simply by not requiring that every finite valid trace in the
  strategy is extended by a client move. Instead, our representation uses
  concrete silent $itree.tauF$ steps which might be played indefinitely. We
  conjecture that going from the former to the latter would amount to a form
  of excluded middle.

  All in all, our coinductive encoding of strategies as a final coalgebra can
  be seen as slightly more intensional than #nm[Levy] & #nm[Staton]'s. We believe
  that it provides a more idiomatic computational account of strategies.
]

=== Delay and Big-Step Transition Systems

Before heading to definition of bisimilarity of strategies, we introduce one
last notion, half-way between transition systems and strategies: _big-step
transition systems_. It is sometimes more convenient to work with a transition
system, but where the silent steps have been "grouped together". In other words,
we wish to remove the silent steps from the transition _function_, and instead
work with a _partial_ transition function returning either an output step or a
visible step.

To do so, the prime choice is to use #nm[Capretta]'s delay
monad~#mcite(<Capretta05>). Recall that it is defined abstractly as the
following final coalgebra.

$ delay.t th X := nu A. th X base.sum A $

Instead of directly constructing this coinductive type, it can be observed that
it is readily an instance of our interaction trees. Defining it as an interaction
tree means that all of the forthcoming theory on interaction trees will effortlessly
be available on the delay monad.

#definition[Delay Monad][
  Define the trivially indexed _void container_ as follows.

  $ icont.null cl icont.t th base.unit \
    icont.null := pat(
      icont.qry & th i := base.empty,
      icont.rsp & th i th (),
      icont.nxt & th i th (),
    ) $

  Then, define the delay monad as follows.

  $ delay.t cl base.Type -> base.Type \
    delay.t th X := itree.t_(icont.null th base.unit) th (kw.fun th i |-> X) th base.tt $
]

#remark[
  Because the delay monad is not indexed, it is given by a _trivially_
  indexed interaction tree. This choice is rather debatable in our concrete
  code artifact, as Rocq's inability to provide an #sym.eta\-law on the empty
  record $base.unit$ makes it rather painful to work with trivially indexed
  interaction trees. We gloss over these issues and assume the #sym.eta\-law
  on $base.unit$. This makes every element of $base.unit$ _definitionally_ equal
  to $base.tt$, and more importantly, every function $base.unit -> X$
  definitionally constant.
]

#definition[Big-Step Transition System][
  Given a game $G cl game.g th I^+ th I^-$ and a family $X cl base.Type^(I^+)$,
  a _big-step transition system over $G$ with output $X$_ is given by records of
  the following type.

  $ kw.rec strat.bs_G th X kw.whr \
    pat(strat.stp & cl I^+ -> base.Type,
        strat.stn & cl I^- -> base.Type,
        strat.play & cl strat.stp ctx.arr delay.t th (X base.sum G.game.client game.extA strat.stn),
        strat.coplay & cl strat.stn ctx.arr G.game.server game.extP strat.stp) $

  Note that we have implicitly lifted the delay monad pointwise to families by
  $delay.t th X th i := delay.t th (X th i)$.
] <def-big-tsys>

#remark[
  #nm[Levy] & #nm[Staton] define a similar notion of big-step transition
  system~#mcite(<LevyS14>) (Def. 4). The sole difference is that they model
  partiality using the $de("Option") th X := base.unit base.sum X$ monad.
  Once again, in a classical metatheory, this is isomorphic to our definition
  (when the #delay.t monad is quotiented by weak bisimilarity).
  Constructively however, $de("Option")$ is quite far from a suitable model of
  partiality in the sense of #nm[Turing]-complete computation, as it trivially
  allows one to _compute_ whether the "partial computation" is undefined or
  returns an output.
]

Like transition systems, big-step transition systems can be unrolled into
strategies. This should not come as a surprise as a standard calculation on
fixed points shows the following isomorphism.

$ & nu A. th X base.sum A base.sum G.game.client game.extA G.game.server game.extP A \
  approx quad & nu A. th nu B. th (X base.sum G.game.client game.extA G.game.server game.extP A) base.sum B $

#definition[Big-Step System Unrolling][
  For any big-step system $S cl strat.bs_G th X$, the active and passive states can be
  respectively _unrolled_ to active and passive strategies. The mapping is
  given by the following three mutually coinductive definitions.

  $
    de("unroll-aux") cl delay.t th (X base.sum G.game.client game.extA strat.stn) ctx.arr game.stratA_G th X \
    de("unroll-aux") th t := \
    pat(itree.obs := kw.case th t .itree.obs \
      pat(
        itree.retF th (base.inj1 th x) & := itree.retF th x,
        itree.retF th (base.inj2 th (m, s)) & := itree.visF th m th (itree.unrollP th s),
        itree.tauF th t & := itree.tauF th (de("unroll-aux") th t),
      )
    ) \
    \
    itree.unrollA cl S .strat.stp ctx.arr game.stratA_G th X \
    itree.unrollA th s := de("unroll-aux") th (S .strat.play th s) \
    \
    itree.unrollP cl S .strat.stn ctx.arr game.stratP_G th X \
    itree.unrollP th s th m := itree.unrollA th (S .strat.coplay th s th m)
    $
]

Note that we have overloaded $itree.unrollA$ and $itree.unrollP$ for both
small- and big-step transition systems. In fact for the rest of this thesis we
will be entirely concerned with either strategies or big-step transition
systems. With all representation variants of strategies now defined, let us
now define their notions of equivalence.

== Bisimilarity <sec-bisim>

The natural notion of equality on automata is the notion of bisimilarity.
Intuitively, a bisimulation between two automata consists of a relation between
their respective states, which is preserved by the transition functions. Two
automata are then said to be _bisimilar_ when one can exhibit a bisimulation
relation between them. Another way to phrase this is that two automata are
bisimilar whenever they are related by the greatest bisimulation relation,
_bisimilarity_, again a coinductive notion. As our strategies feature _silent
moves_ (the #itree.tauF nodes of the action functor), we will need to consider
two variants, _strong_ and _weak_ bisimilarity. Strong bisimilarity requires
that both strategy trees match at each step, fully synchronized. Weak
bisimilarity, on the other hand, allows both strategies to differ by a finite
amount of #itree.tauF nodes in between any two synchronization points.

Before translating these ideas into type theory, we will need a bit of
preliminary tools. Most implementations of type theory provide some form of
support for coinductive records (such as @def-itree) and for
coinductive definitions (such as @def-unroll). However, these features---in
particular coinductive definitions---are at times brittle, because type theory typically relies on a
syntactic _guardedness_ criterion to decide
whether a given definition should be accepted. For simple definitions---in fact
more precisely for computationally relevant definitions---I will indulge the
whims of syntactic guardedness. But for complex bisimilarity proofs such as
those which will appear later in this thesis, being at the mercy of a syntactic
implementation detail is a recipe for failure.

To tackle this problem, Agda provides more robust capabilities in the form of
_sized types_, for which the well-formedness criterion is based on typing.
However they are not available in Rocq, the language in which this thesis has
been formalized. Moreover, in Agda's experimental tradition, while sized types
are of practical help when used as intended, their precise semantics are still
not fully clear~#mcite(<AbelP16>).

We will take an entirely different route, building coinduction for ourselves,
_inside_ type theory. Indeed, as demonstrated by #nm[Pous]'s coq-coinduction
software library~#mcite(<Pous16>, supplement:
    [https://github.com/damien-pous/coinduction]) on which our artifact is
based, powerful coinductive constructions and reasoning principles are
derivable in the presence of an impredicative sort of propositions.

=== Coinduction with Complete Lattices

The basis of coq-coinduction is the observation that with impredicativity,
#base.Prop forms a complete lattice ordered by implication. In fact, not only
#base.Prop, but also predicates $X -> base.Prop$ or relations $X -> Y ->
base.Prop$, our case of interest for bisimilarity. By the
#nm[Knaster]-#nm[Tarski] theorem~#mcite(<Tarski55>) one can obtain the greatest
fixed point $nu f := or.big { x | x lt.tilde f th x }$ of any monotone endo-map
$f$ on a complete lattice. Henceforth, we will use $lt.tilde$ for the ordering
relation of any lattice, and $approx$ for the derived equivalence relation.

This is only the first part of the story. Indeed this will provide us with the
greatest fixed point $nu f$, in our case, bisimilarity, but the reasoning
principles will be cumbersome. At first sight, the only principle available is the
following one.

#centering(inferrule(
  ($x lt.tilde y$, $y lt.tilde f th y$),
  ($x lt.tilde nu f$)
))

Programming solely with this principle is painful, much in the same way as
manipulating inductive types solely using eliminators, instead of using
pattern-matching and recursive functions. Thankfully, in the context of
bisimulations, a line of work has been devoted to a theory of _enhanced_
bisimulations, in which the premise is weakened to $x lt.tilde f th (g th
x)$--- bisimulation _up-to $g$_---for some other monotone map $g$. We say
that $g$ is a _valid up-to principle_ for $f$ whenever this enhanced property
is derivable.

#centering(inferrule(
  ($x lt.tilde y$, $y lt.tilde f th (g th y)$),
  [$x lt.tilde nu f$]
))

The map $g$ will typically enlarge or its argument $y$, or otherwise tweak it,
making $g$-enhanced bisimulations $y$ easier to exhibit than proper bisimulations.
As an example on relations, reasoning up-to transitivity means working with
such a principle for $g th R := R ; R$. Because valid up-to principles are not
closed under composition, several well-behaved sufficient conditions have
been studied, such as _compatibility_ where $g$ must verify $g compose f
lt.tilde f compose g$ w.r.t. the pointwise order on monotone maps.
Satisfyingly, the least upper bound of all compatible maps is still compatible.
It is called the _companion_~#mcite(<Pous16>) of $f$ written $t_f$.
This enables working with the following _up-to companion_ generalized principle.

#centering(inferrule(
  [$x lt.tilde f th (t_f th x)$],
  [$x lt.tilde nu f$]
))

Thanks to the fact that $x lt.tilde t_f th x$ and $t_f th (t_f th x) lt.tilde
t_f th x$, one can delay until actually required in the proof the choice and
use of any particular valid up-to principle $g lt.tilde t_f$. This theory based on the
companion is the one used in the Rocq formalization of this thesis. However,
since I started writing the formalization, an even more practical solution,
#nm[Schäfer] and #nm[Smolka]'s _tower induction_~#mcite(<SchaferS17>), has been
merged into coq-coinduction. I did not have the time to port my Rocq
development to the new version of coq-coinduction, but I will nonetheless
present it here and use tower induction as the basis for defining bisimilarity.
We thus leave both the #nm[Knaster]-#nm[Tarski] construction as well as the
companion behind and now focus solely on tower induction.

Tower induction rests upon the inductive definition of the _tower predicate_
$tower.t_f$, whose elements can be understood as the transfinite iterations
of $f$ starting from the greatest element $top$. In other words, $tower.t_f$
characterizes the transfinite approximants of the greatest fixed point of $f$.
We will refer to these elements of the tower as _candidates_.

For more easily working with predicates, we introduce some notations. For any
predicate $P cl base.Prop^X$ we write $x in P$ instead of $P th x$ and $forall th x in P
-> ..$ instead of $forall th {x} -> P th x -> ..$. Moreover, given two predicates
$P, Q cl base.Prop^X$, we write $P subset.eq Q$ to denote $forall th x in P -> x in Q$.

#definition[Tower][
  Given a complete lattice $X$ and a monotone endo-map $f cl X -> X$, the
  _$f$-Tower_ is an inductive predicate $kw.dat th tower.t_f cl base.Prop^X$ defined
  by the following constructors.

  #mathpar(block: true,
    inferrule(
      $t cl x in tower.t_f$,
      $tower.tb th t cl f th x in tower.t_f$
    ),
    inferrule(
      $s cl F subset.eq tower.t_f$,
      $tower.tinf th s cl and.big F in tower.t_f$
    ),
  )
] <def-tower>

#theorem[Tower Induction][
  Given a complete lattice $X$, a monotone endo-map $f cl X -> X$ and an inf-closed
  predicate $P cl base.Prop^X$, the following _tower induction principle_ is true.

  #inferrule(
    [$forall th x in tower.t_f -> x in P -> f th x in P$],
    [$tower.t_f subset.eq P$],
    suppl: tower.tind
  )
] <thm-tower-ind>
#proof[
  Assuming that $P$ is inf-closed i.e.,

  $ K cl forall th {F} -> F subset.eq P -> and.big F in P, $

  and assuming the hypothesis

  $ H cl forall th x in tower.t_f -> x in P -> f th x in P, $

  define $tower.tind cl tower.t_f subset.eq P$ by induction as follows.

  $ tower.tind th {x} cl tower.t_f th x -> P th x $
  #v(-0.5em)
  $ & tower.tind th (tower.tb t)   && := H th t th (tower.tind th t) \
    & tower.tind th (tower.tinf s) && := K th (kw.fun th p |-> tower.tind th (s th p)) $
  #v(-2em)
]

#remark[
  Note that tower induction is only a small rewording of a non-dependent
  induction principle (called _minimality_ in Rocq) on membership proofs of
  the tower predicate. The sole difference is that the minimality principle
  does not require full inf-closedness, but only inf-closedness for families
  below the tower, i.e., the weaker $F subset.eq tower.t_f -> F subset.eq P -> and.big F in P$.
  However, inf-closedness is quite a common property, so that it can be automatically
  derived in full for every properties of interest.
]

#lemma[Tower Properties][
  Given a complete lattice $X$ and a monotone endo-map $f cl X -> X$,
  for all candidate $x in tower.t_f$ the following statements are true.

  1. $f th x lt.tilde x$
  2. $forall th y -> y lt.tilde f th y -> y lt.tilde x$ 
] <lem-tower-props>
#proof[
  Both statements are proven by direct tower induction on the statement, with
  simple calculations proving the hypotheses. Let us detail the first statement
  to showcase the proof method.

  Pose $P th x := f th x lt.tilde x$. Let us show the tower induction
  hypotheses.
  - Assume $F subset.eq P$. Let us show that $and.big th F in P$. By definition of the
    infimum, it suffices to show that for any $x in
    F$ we have $f th (and.big th F) lt.tilde x$. By definition of the infimum and monotonicity $f th (and.big
    th F) lt.tilde f th x$. Conclude using the assumption $F subset.eq P$.
  - Assume $x in tower.t_f$ such that $x in P$, let us show that $f th x in P$.
    By assumption we know that $f th x lt.tilde x$, thus by monotonicity,
    $f th (f th x) lt.tilde f th x$, which concludes.
  #v(-2em)
]

#theorem[Greatest Fixed Point][
  Given a complete lattice $X$ and a monotone endo-map $f cl X -> X$, pose
  $ tower.nu f := and.big tower.t_f. $
  The following statements are true.
  1. $tower.nu f in tower.t_f$
  2. $tower.nu f approx f th (tower.nu f)$
  3. $forall th x -> x lt.tilde f th x -> x lt.tilde tower.nu f$
] <lem-tower-fix>
#proof[
  1. By $tower.tinf th (kw.fun th t |-> th t)$.
  2. By antisymmetry.
     - $tower.nu f lt.tilde f th (tower.nu f)$ #sym.space.quad By $tower.tb$ and (1), we
       have $f th (tower.nu f) in tower.t_f$. Conclude by definition of $tower.nu$ as
       an infimum.
     - $f th (tower.nu f) lt.tilde tower.nu f$ #sym.space.quad By (1) we and @lem-tower-props (1).
  3. By (1) and @lem-tower-props (2).
  #v(-2em)
]

In @lem-tower-fix, (2) and (3) are pretty clear: together they prove that $tower.nu f$
is indeed the greatest fixed point of $f$. On the other hand, (1) might seem
like a technical lemma but it is just as important, if not more. Indeed,
knowing that $tower.nu f$ is part of the tower---i.e., that it is itself a
transfinite approximation of the greatest fixed point---enables to directly
apply tower induction (@thm-tower-ind) to prove properties about $tower.nu f$.
Although tower induction also proves properties about any candidate (elements of the tower),
it will be our prime reasoning principle for proving properties and the greatest
fixed point. As we will see shortly, lemmas about arbitrary candidates (also
proven by tower induction) will provide us with a practical alternative to more
usual valid up-to principles.

And this is it! I really want to stress the fact that this is the entirety of the
core mathematical content of this theory of coinduction, and yet it
provides an exceedingly versatile and easy-to-use theorem. It is easily shown
to subsume the principles provided by the companion construction and by other
frameworks such as _parametrized coinduction_~#mcite(<HurNDV13>).
Despite its great utility, the coq-coinduction library is extremely
small. Besides some applications and generic theorems, its only additional
content consist in several helpers e.g., for deriving inf-closedness of
predicates, the definition of the most useful instances of complete lattices
and some generic duality and symmetry arguments. The article by #nm[Schäfer] and
#nm[Smolka]~#mcite(dy: -0.5em, <SchaferS17>) is similarly short, providing the whole theory
in merely three pages, including the proofs and the derivation of the
companion. As such, if you need to work with coinduction and are happy with
an impredicative universe of propositions, I heartily recommend you to try
out tower induction.

=== Strong Bisimilarity

Equipped with this new construction for greatest fixed points we are ready to
define bisimilarity. As our strategies feature silent transitions, there are two
variants of interest: _strong bisimilarity_ which considers silent transitions
as any other "normal" transition, and _weak bisimilarity_, which allows to skip
over any finite number of silent steps. We start by describing the strong
bisimilarity, which embodies the natural notion of extensional equality for
strategies, but the construction of weak bisimilarity will proceed very
similarly.

Bisimulations and simulations for coalgebraic presentations of automata have
been well studied, with the general blueprint outlined by
#nm[Levy]~#mcite(<Levy11>). Succinctly, bisimulations for $F$-coalgebras can be
expressed given an analogue to the functor $F$, but operating
on _relations_ instead of sets. More precisely, this operator is called a
_relator_~#num-cite(<Levy11>)#sym.zwj#mcite(<LagoGL17>) and takes relations $X rel.rar Y$ to relations $F X rel.rar F
Y$, subject to several conditions. Then, given a relator $Gamma$ and two
coalgebras $phi cl X -> F X$ and $psi cl Y -> F Y$, we can derive
a monotone endo-map which takes a relation $R cl X rel.rar Y$ to the re-indexed
relation $phi angle.r Gamma R angle.l psi cl X rel.rar Y$. This resulting
relation can be understood in plain words: after one unfolding on both sides,
the coalgebra states are related by $R$ under $Gamma$. In a sense, $Gamma$ decides
when two steps should be considered matching or _synchronized_, provided we give it
a relation on states. Bisimilarity is then obtained by the greatest fixed point
of this monotone map, while bisimulations are its pre-fixed points.

We will largely follow this blueprint, only concerned with the final coalgebras
given by interaction trees, with perhaps the slight technicality that we are
working not with sets and relations, but (indexed) set families and relation
families. But to better fit our setting, we adopt a small twist. Recall
that $itree.F_Sigma$ is functorial with respect to both the output parameter
$X$ as well as the second "coalgebra" parameter. Indeed we intend to show that
strategies form a monad, so that in particular they are functorial with
respect to this output $X$. Hence, our goal is not to construct a single
relation between strategies, but rather devise an operator taking a relation
family on two output families

$ X^rel.r cl forall th {i} -> X^1 th i -> X^2 th i -> base.Prop, $

to the strong bisimilarity on strategies with the respective outputs

$ ar cnorm(iteq(X^rel.r)) ar cl
  forall th {i} -> itree.t_Sigma th X^1 th i
                -> itree.t_Sigma th X^2 th i
                -> base.Prop. $

This is quite reminiscent of a relator on $itree.t_Sigma$! And indeed, pushing
the output parameter inside our monotone map will not fundamentally change the
construction. Instead of working in the complete lattice of relation families,
we will adopt the complete lattice of $itree.t_Sigma$ relators.

Let us start with some preliminary notation for our indexed relations.

#definition[Family Relation][
  Given $I cl base.Type$ and two families $X, Y cl base.Type^I$, the type of
  _family relations between $X$ and $Y$_ is defined as follows.

  $ rel.irel th X th Y := forall th {i} -> X th i -> Y th i -> base.Prop $

  We denote by $lt.tilde$ (in infix notation) the standard ordering on family
  relations, defined by

  $ R lt.tilde S := forall th {i} th (x cl X th i) th (y cl Y th i) -> R th x th y -> S th x th y, $

  for any $R,S : rel.irel th X th Y$.  

  We define the standard operators of diagonal, converse, and sequential
  composition and re-indexing on family relations, as follows.

  #mathpar(spacing: 2em, block: false, inset: 0.5em,
    [$ & rel.diagS cl rel.irel th X th X \
       & rel.diagS th a th b := a = b $],
    [$ & ar^rel.revS cl rel.irel th X th Y -> rel.irel th Y th X \
       & R^rel.revS th a th b := R th b th a $],
    [$ & ar cnorm(rel.seqS) ar cl rel.irel th X th Y -> rel.irel th Y th Z -> rel.irel th X th Z \
       & (R rel.seqS S) th a th c := exists th b, R th a th b and S th b th c $],
    [$ & nar""cnorm(de(angle.r))nar""cnorm(de(angle.l))""nar cl (X_2 ctx.arr X_1) -> rel.irel th X_1 th Y_1 -> (Y_2 ctx.arr Y_1) -> rel.irel th X_2 th Y_2 \
       & (f relix(R) g) th a th b := R th (f th a) th (g th b) $]
  )
]

#definition[Family Equivalence][
  Given $R cl rel.irel th X th X$, we say that
  - _$R$ is reflexive_ whenever $rel.diagS lt.tilde R$;
  - _$R$ is symmetric_ whenever $R^rel.revS lt.tilde R$;
  - _$R$ is transitive_ whenever $R rel.seqS R lt.tilde R$; and
  - _$R$ is an equivalence_ whenever it is reflexive, symmetric, and transitive.
]

We can now define the relational counterpart to $itree.F_Sigma$.

#definition[Action Relator][
Given $Sigma cl icont.t th I$, an output relation $X^rel.r cl rel.irel th X^1 th
  X^2$, and a parameter relation $A^rel.r cl rel.irel th A^1 th A^2$, the
  _action relator over $Sigma$_ of signature

  $ kw.dat itree.RS th X^rel.r th A^rel.r
      cl rel.irel th (itree.F_Sigma th X^1 th A^1) th (itree.F_Sigma th X^1 th A^2) $

  is defined by the following constructors.

  #mathpar(block: true,
    inferrule(
      $x^rel.r cl X^rel.r th x^1 th x^2$,
      $itree.retR th x^rel.r cl itree.RS th X^rel.r th A^rel.r th (itree.retF th x^1) th (itree.retF th x^2)$
    ),
    inferrule(
      $t^rel.r cl A^rel.r th t^1 th t^2$,
      $itree.tauR th t^rel.r cl itree.RS th X^rel.r th A^rel.r th (itree.tauF th t^1) th (itree.tauF th t^2)$
    ),
    inferrule(
      ($q cl Sigma .icont.qry th i$, $k^rel.r cl (r cl Sigma .icont.rsp th q) -> A^rel.r th (k^1 th r) th (k^2 th r)$),
      $itree.visR th q th k^rel.r cl itree.RS th X^rel.r th A^rel.r th (itree.visF th q th k^1) th (itree.visF th q th k^2)$
    ),
  )
]

#remark[
  The above definition of $itree.RS$ is quite a mouthful, yet it should be noted that its
  derivation is entirely straightforward. Categorically, it is the canonical
  lifting of $itree.F_Sigma$ to relations, which can be obtained in type
  theory by a relational, or _parametricity_ interpretation~#mcite(<BernardyJP12>).
]

#lemma[
  $itree.RS$ is monotone in both arguments, i.e.

  $ X^rel.r_1 lt.tilde X^rel.r_2 -> A^rel.r_1 lt.tilde A^rel.r_2 -> itree.RS th X^rel.r_1 th A^rel.r_1 lt.tilde itree.RS th X^rel.r_2 th A^rel.r_2 $

  Moreover the following statements hold (understood as universally quantified).

  #let xx = [$X^rel.r$]
  #let yy = [$A^rel.r$]

  $ rel.diagS
      & lt.tilde itree.RS th rel.diagS th rel.diagS \
    (itree.RS th xx th yy)^rel.revS 
      & lt.tilde itree.RS th xx^rel.revS th yy^rel.revS \
    itree.RS th X^rel.r_1 th A^rel.r_1 rel.seqS itree.RS th X^rel.r_2 th A^rel.r_2
      & lt.tilde itree.RS th (X^rel.r_1 rel.seqS X^rel.r_2) th (A^rel.r_1 rel.seqS A^rel.r_2) \
      de("too-long")
      & lt.tilde itree.RS th (f_1 relix(X^rel.r) f_2) th (g_1 relix(A^rel.r) f_2)
    $

  with $de("too-long") := itree.F_Sigma th f_1 th g_1 relix(itree.RS th X^rel.r th A^rel.r) itree.F_Sigma th f_2 th g_2$.
] <lem-actrel-props>
#proof[All by direct case analysis.]

#remark[
  Although we never formally provide a definition of relators, their list of
  conditions be inferred from the above definition, which exhibits $itree.RS_Sigma$ as a relator
  in two arguments. More precisely, the statement related to the converse
  operator is not always required and defines a lax _conversive_
  relator~#mcite(<Levy11>). Note that although all the reverse inequality
  also hold, we will not make use of them.

  Intuitively, the relator conditions are heterogeneous generalizations
  (strengthenings) of the facts that a relator sends reflexive relations to
  reflexive relations, symmetric relations to symmetric relations, etc.
]

#definition[Pre-Relator Lattice][
  Given $Sigma cl icont.t th I$, we define the interaction _pre-relator
  lattice over $Sigma$_ as follows.

  $ rel.lat_Sigma := forall th {X^1 th X^2} -> rel.irel th X^1 th X^2 -> rel.irel th (itree.t_Sigma th X^1) th (itree.t_Sigma th X^2)) $

  It is ultimately a set of dependent functions into $base.Prop$, as such it
  forms a complete lattice by pointwise lifting of the structure on $base.Prop$.
] <def-interaction-lattice>

#remark[
  The name "pre-relator" comes from the fact that the elements of this lattice
  have the same type as $itree.t_Sigma$ relators, but they are not constrained
  by any condition.
]

#let cF = $cal(F)$

#definition[Strong Bisimilarity][
  Given $Sigma cl icont.t th I$, we define the _strong bisimulation map over
  $Sigma$_ as the following monotone endo-map on the pre-relator lattice over $Sigma$.

  $ itree.sb_Sigma cl rel.lat_Sigma -> rel.lat_Sigma \
    itree.sb_Sigma th cF th X^rel.r :=
      itree.obs relix(itree.RS th X^rel.r th (cF th X^rel.r)) itree.obs $

  For any given family relation $X^r : rel.irel th X^1 th X^2$, we define
  heterogeneous and homogeneous _strong bisimilarity_ over $X^r$, denoted by
  $iteq(X^rel.r)$, as follows.

  $ &a iteq(X^rel.r) b &&  := tower.nu th itree.sb_Sigma th X^rel.r th a th b \
    &a de(approx.eq) b &&  := a iteq(rel.diagS) b $
]

#lemma[
  Given $Sigma cl icont.t th I$, for all strong bisimulation candidates $cF in
  tower.t_(itree.sb_Sigma)$, the following statements are true.

  #let xx = [$X^rel.r$]

  $ X^rel.r_1 lt.tilde X^rel.r_2 -> cF th X^rel.r_1 & lt.tilde cF th X^rel.r_2 \
    rel.diagS & lt.tilde cF th rel.diagS \
    (cF th X^rel.r)^rel.revS & lt.tilde cF th xx^rel.revS \
    cF th X^rel.r_1 rel.seqS cF th X^rel.r_2 & lt.tilde cF th (X^rel.r_1 rel.seqS X^rel.r_2) $

  As a consequence, when $X^rel.r cl rel.irel th X th X$ is an equivalence
  relation, $cF th X^rel.r$ is an equivalence relation.
  As a particularly important consequence,
  recalling that $tower.nu th itree.sb_Sigma in tower.t_(itree.sb_Sigma)$, all
  the above statements are true for strong bisimilarity, and thus $de(approx.eq)$ is an equivalence relation.
] <lem-sbisim-props>

#proof[
  All statements are proven by direct tower induction, applying the
  corresponding statement from @lem-actrel-props.

  For example for the first one, pose $P th x$ to be the goal, i.e.,

  $ P th cF := & forall th {X^1 th X^2} th {X^rel.r_1 th X^rel.r_2 cl rel.irel th X^1 th X^2} \
              & -> X^rel.r_1 lt.tilde X^rel.r_2 -> cF th X^rel.r_1 lt.tilde cF th X^rel.r_2. $ 

  $P$ is inf-closed. Moreover, the premise of tower induction requires that

  $ P th cF -> P th (itree.sb_Sigma th cF), $

  i.e., introducing all arguments of the implication we need to prove
  #inferrule(
    (
      [$forall th {X^1 th X^2} th {X^rel.r_1 th X^rel.r_2 cl rel.irel th ..}
        -> X^rel.r_1 lt.tilde X^rel.r_2
        -> cF th X^rel.r_1 lt.tilde cF th X^rel.r_2$],
      [$X^rel.r_1 lt.tilde X^rel.r_2$],
      [$itree.RS th X^rel.r_1 th (cF th X^rel.r_1) th (t_1 .itree.obs) th (t_2 .itree.obs)$]
    ),
    [$itree.RS th X^rel.r_2 th (cF th X^rel.r_2) th (t_1 .itree.obs) th (t_2 .itree.obs)$],
    suppl: ","
  )

  which follows by direct application of the fact that #itree.RS is monotone in
  both arguments (@lem-actrel-props).
]

#remark[
  In @lem-sbisim-props, a statement similar to the one concerned with the
  functorial re-indexing which we had in @lem-actrel-props is missing. It is
  simply because we have not yet defined the action of $itree.t_Sigma$ on
  morphisms, but we will prove it in due time.
]

This completes the basic theory of strong bisimilarity: we have defined it and
proved its most important properties in @lem-sbisim-props, namely that when
the relation on outputs is well-behaved, not only strong bisimilarity is an equivalence
relation, but _every bisimulation candidate_ is an equivalence relation. As a
consequence, during any tower induction proof, by definition featuring such a
bisimulation candidate, one can use these properties. In a sense, strong
bisimulation proofs can work up-to reflexivity, symmetry and transitivity.

=== Weak Bisimilarity

As  previously hinted at, we wish to characterize a second notion of
bisimilarity, which would gloss over the precise number of silent #itree.tauF
moves of the two considered interaction trees. While strong bisimilarity will
play the role of (extensional) equality between trees, that is, a technical
tool, weak bisimilarity will play the role of a semantic equivalence.

To define weak bisimilarity, we follow a similar route to strong bisimilarity, 
reusing the action relator but defining a new monotone endo-map on the pre-relator
lattice. To build this monotone map, we will sequence the action relator on the left and on
the right with a small gadget, allowing to skip over a finite number
of silent moves before landing in the action relator. This gadget, the _eating_
relation $itree.eatlr$, can be understood as a form of reduction relation on
interaction trees, with $t itree.eatlr t'$ stating that $t$ starts with some
amount of silent steps and finally arrives at $t'$.

For readability, let us start by defining a shorthand for trees where the top layer of
actions has been exposed.

#definition[Exposed Interaction trees][
  Given $Sigma cl icont.t th I$ and $X cl base.Type^I$, define _exposed_ interaction
  trees with output $X$ as the following shorthand.

$ itree.tp_Sigma th X := itree.F_Sigma th X th (itree.t_Sigma th X) $
]



#definition[Eating Relation][
  Given $Sigma cl icont.t th I$ and $X cl base.Type^I$, define the inductive _eating relation_
  $kw.dat itree.eat_Sigma^X cl rel.irel th (itree.tp_Sigma th X) th (itree.tp_Sigma th X)$ by
  the following constructors.

  #mathpar(block: true,
    inferrule(
        "",
        $itree.eatR cl itree.eat_Sigma^X th t th t$
    ),
    inferrule(
        $e cl itree.eat_Sigma^X th (t_1 .itree.obs) th t_2$,
        $itree.eatS th e cl itree.eat_Sigma^X th (itree.tauF th t_1) th t_2$
    ),
  )

  We define the following shorthands:

  #let xx = $itree.eat_Sigma^X$
  #mathpar(block: true,
    $nar""cnorm(itree.eatlr)nar th := xx$,
    $nar""cnorm(itree.eatrl)nar th := xx^rel.revS$,
  )
]

#lemma[
  For all $Sigma$ and $R$, the eating relation $itree.eat_Sigma^R$ is reflexive and
  transitive.
]
#proof[By direct induction.]

#definition[Weak Bisimilarity][
  Given $Sigma cl icont.t th I$, we define the
  _weak bisimulation map over $Sigma$_ as the following monotone endo-map on the
  pre-relator lattice over $Sigma$ (@def-interaction-lattice). 

  #let xx = [$itree.eat_Sigma^X$]

  $ itree.wb_Sigma cl rel.lat_Sigma -> rel.lat_Sigma \
    itree.wb_Sigma th cF th X^rel.r :=
      itree.obs relix(cnorm(itree.eatlr) rel.seqS itree.RS th X^rel.r th (cF th X^rel.r)
            rel.seqS cnorm(itree.eatrl)) itree.obs $

  We define heterogeneous and homogeneous _weak bisimilarity_ as follows.

  $ & a itweq(X^rel.r) b && := tower.nu th itree.wb_Sigma th X^rel.r th a th b \
    & a de(approx) b     && := a itweq(rel.diagS) b $
]

#remark[
  The weak bisimulation map can be understood quite simply. Given a pre-relator $cF$ over
  $Sigma$ and a relation on outputs, it relates interaction trees which both "reduce" to
  some smaller trees, peeling away some number of silent steps, then both emit "synchronized" moves,
  as constrained by $itree.RS$, and finally are related by $cF$.
]

We can now give a first batch of easy properties on weak bisimilarity and weak bisimulation
candidates.

#lemma[
  Given $Sigma cl icont.t th I$, for all candidate weak bisimulations $cF in
  tower.t_(itree.wb_Sigma)$, the following statements hold.

  #let xx = [$X^rel.r$]

  $ X^rel.r_1 lt.tilde X^rel.r_2 -> cF th X^rel.r_1 & lt.tilde cF th X^rel.r_2 \
    rel.diagS & lt.tilde cF th rel.diagS \
    (cF th X^rel.r)^rel.revS & lt.tilde cF th xx^rel.revS $

  Recalling again that $tower.nu th itree.wb_Sigma in tower.t_(itree.wb_Sigma)$,
  these statements apply to weak bisimilarity, and in particular the homogeneous weak
  bisimilarity $de(approx)$ is reflexive and symmetric.
] <lem-wbisim-props>
#proof[
  All by direct tower induction, as for @lem-sbisim-props.
]

Notice that in the above lemma, compared to @lem-sbisim-props, we have
left out the statement regarding sequential composition of relations which
generalizes the fact that any weak bisimulation candidates sends transitive
relations to transitive relations. Indeed it is well-known that weak
bisimulation up-to transitivity is not a valid proof
technique~#mcite(<PousS11>). As such, there is no hope that the corresponding
statement on weak bisimulations candidates holds. However, we would still like
to prove that weak bisimilarity is transitive! The proof is slightly more involved
and will involve a lot of shuffling around the eating gadget.

Once again, to make the notations more compact and less overwhelming, we need
to introduce several helpers for working with one-step unfolded bisimulation relations.

#definition[Exposed Bisimulations][
  Given $Sigma cl icont.t th I$, $cF cl rel.lat_Sigma$ and $X^rel.r cl rel.irel th X^1 th X^2$,
  define the following shorthands for _strong bisimulation unfolding_

  $ xsb(cF) cl rel.irel th (itree.tp_Sigma th X^1) th (itree.tp_Sigma th X^2) \
    xsb(cF) := itree.RS th X^rel.r th (cF th X^rel.r) $

  and _weak bisimulation unfolding_

  $ xwb(cF) cl rel.irel th (itree.tp_Sigma th X^1) th (itree.tp_Sigma th X^2) \
    xwb(cF) := cnorm(itree.eatlr) rel.seqS itree.RS th X^rel.r th (cF th X^rel.r) rel.seqS cnorm(itree.eatrl) $
]

We can now prove generalized transitivity of weak bisimilarity.

#lemma[
  Given $Sigma cl icont.t th I$, $X^rel.r_1 cl rel.irel th X_1 th X_2$, and
  $X^rel.r_2 cl rel.irel th X_2 th X_3$, the following holds.

  $ cnorm(itweq(X^rel.r_1) rel.seqS itweq(X^rel.r_2)) quad lt.tilde quad cnorm(itweq(X^rel.r_1 rel.seqS X^rel.r_2)) $
]

#proof[
  Pose the following shorthands, respectively for "one step
  synchronization then weak bisimilarity" and for one-step unfolding of weak
  bisimilarity.

  #let sync = crel(xsb(itree.weq))
  #let weak = crel(xwb(itree.weq))
  #let eat = itree.eatlr
  #let eatr = itree.eatrl

  Let us recall our new notations as applied to weak bisimilarity. Note that
  the output relation $X^rel.r$ will be hidden away, implicitly
  instantiated either as $X^rel.r_1$, $X^rel.r_2$ or $X^rel.r_1 rel.seqS X^rel.r_2$.

  $ cnorm(sync)"" & := itree.RS th X^rel.r th (itweq(X^rel.r)) \
    cnorm(weak)"" & := cnorm(eat) rel.seqS cnorm(sync) rel.seqS cnorm(eatr) $

  We prove the following statements by direct induction on the eating relation
  for all $a, b, c$.

  1. $a eat itree.tauF th b sync c -> a sync c$
  2. $ a sync itree.tauF th b eatr c -> a sync c$

  We then observe that the following statements are true by case analysis.

  3. $itree.tauF th a weak b -> a .itree.obs weak b$
  4. $a weak itree.tauF b -> a weak b .itree.obs$

  Using 3. and 4. and transitivity of the eating relation, prove the following statements by induction.

  5. $a crel((weak rel.seqS eat)) itree.retF th r -> a crel((eat rel.seqS sync)) itree.retF r$
  6. $a crel((weak rel.seqS eat)) itree.visF th q th k -> a crel((eat rel.seqS sync)) itree.visF th q th k$
  7. $itree.retF th r crel((eatr rel.seqS weak)) b -> itree.retF th r crel((sync rel.seqS eatr)) b$
  8. $itree.visF th q th k crel((eatr rel.seqS weak)) b -> itree.visF th q th k crel((sync rel.seqS eatr)) b$

  Finally, note that the following is true by (nested) induction.

  9. $a crel((eatr rel.seqS eat)) b -> a eat b or a eatr b$

  Finally, we prove the theorem statement by tower induction on

  $ P th cF := cnorm(itweq(X^rel.r_1)) rel.seqS cnorm(itweq(X^rel.r_2)) lt.tilde cF th (X^rel.r_1 rel.seqS X^rel.r_2). $

  $P$ is inf-closed. Assuming $P th cF$, let us prove $P th (itree.wb_Sigma th cF)$, i.e.,

  $ cnorm(itweq(X^rel.r_1)) rel.seqS cnorm(itweq(X^rel.r_2)) th th lt.tilde th th itree.wb_Sigma th cF th (X^rel.r_1 rel.seqS X^rel.r_2) $

  By one step unfolding, it suffices to prove the following.

  $ cnorm(weak) rel.seqS cnorm(weak)
    th th lt.tilde th th
    xwb(cF) $
    //cnorm(eat) rel.seqS itree.RS th X^rel.r th (cF th X^rel.r) rel.seqS cnorm(eatr) $

  Introducing and decomposing the hypotheses, we obtain the following:

  $ a eat x_1 sync x_2 eatr b eat y_1 sync y_2 eatr c $

  Apply 9. between $x_2$ and $y_1$. Assume w.l.o.g. that the left case is true
  i.e., $x_2 eat y_1$ (the right case is symmetric). By case on $y_1$.

  - When $y_1 := itree.retF th r$,

    $ & a & eat x_1 & sync x_2 &          & eat itree.retF th r & sync y_2 eatr c & \
    & a & eat x_1 & sync x_2 & eatr x_2 & eat itree.retF th r & sync y_2 eatr c & quad "by refl." \
    & a &         & weak     &      x_2 & eat itree.retF th r & sync y_2 eatr c & quad "by def." \
    & a &         & eat      &      x_3 & sync itree.retF th r & sync y_2 eatr c & quad "by 5." \
  $

    By concatenation (@lem-actrel-props) between $x_3$ and $y_2$, we obtain 

    $ itree.RS th (X^rel.r_1 rel.seqS X^rel.r_2) th (cnorm(itweq(X^rel.r_1)) rel.seqS
    cnorm(itweq(X^rel.r_2))) th x_3 th y_2. $

    By coinduction
    hypothesis $cnorm(itweq(X^rel.r_1)) rel.seqS cnorm(itweq(X^rel.r_1)) lt.tilde cF th (X^rel.r_1 rel.seqS X^rel.r_2)$.
    As such, by monotonicity
    (@lem-actrel-props) we obtain

    $ itree.RS th (X^rel.r_1 rel.seqS X^rel.r_2) th (cF th (X^rel.r_1 rel.seqS X^rel.r_2)) th x_3 th y_2 $

    and finally conclude $xwb(cF) th a th b$.

  - When $y_1 := itree.visF th q th k$, the reasoning is the same as for $y_1
    := itree.retF r$, swapping lemma 5. with lemma 6.
  - When $y_1 := itree.tauF th t$,

    $ & a & eat x_1 & sync x_2 & eat itree.tauF th t & sync y_2 eatr c & \
      & a & eat x_1 & sync x_2 &                     & sync y_2 eatr c & quad "by 1." \
    $

    By @lem-actrel-props, using concatenation between $x_2$ and $y_2$, we obtain 

    $ itree.RS th (X^rel.r_1 rel.seqS X^rel.r_2) th (cnorm(itweq(X^rel.r_1)) rel.seqS
      cnorm(itweq(X^rel.r_2))) th x_3 th y_2, $

    we then conclude as before by monotonicity applied to the coinduction hypotheses.

  This concludes our tower induction, proving that for all weak bisimulation candidate
  $cF in itree.t_(itree.wb_Sigma)$, we have
  $cnorm(itweq(X^rel.r_1)) rel.seqS cnorm(itweq(X^rel.r_2)) lt.tilde cF th (X^rel.r_1 rel.seqS X^rel.r_2)$.
  As in particular weak bisimilarity is a bisimulation candidate, we finally conclude
  our generalized transitivity property
  $ cnorm(itweq(X^rel.r_1)) rel.seqS cnorm(itweq(X^rel.r_2)) quad lt.tilde quad cnorm(itweq(X^rel.r_1 rel.seqS X^rel.r_2)). $
  #v(-2em)
]

After transitivity, we would like another reasoning principle such that during
any weak bisimulation proof, we can freely rewrite by any strong bisimilarity
proof.

#lemma[Up-to Strong Bisimilarity][
  Given $Sigma cl icont.t th I$, $X^rel.r_1 cl rel.irel th X_1 th X_2$,
  $X^rel.r_2 cl rel.irel th X_2 th X_3$ and $X^rel.r_3 cl rel.irel th X_3 th X_4$,
  the following holds. for any weak bisimulation candidates $cF in
  tower.t_(itree.wb_Sigma)$,

  $ cnorm(iteq(X^rel.r_1)) rel.seqS cF th X^rel.r_2 rel.seqS cnorm(iteq(X^rel.r_3))
    lt.tilde cF th (X^rel.r_1 rel.seqS X^rel.r_2 rel.seqS X^rel.r_3). $
] <lem-up2strong>
#proof[
  Let us define the following shorthand.

  //#let strong = de(crel(math.attach(sym.approx.eq, tr: "s")))
  #let strong = crel(xsb(itree.eq))
  #let sync = $crel(xsb(cF))$
  #let weak = $crel(xwb(cF))$
  #let eat = itree.eatlr
  #let eatr = itree.eatrl

  Recall again the definition of our compact notations. Note that we will use
  both $sync$ and $weak$ in infix style. As before, the output relation $X^rel.r$
  will be hidden and instantiated variously.

  $ "" strong "" & := itree.RS th X^rel.r th iteq(X^rel.r) \
    "" sync "" & := itree.RS th X^rel.r th (cF th X^rel.r) \
    "" weak "" & := cnorm(eat) rel.seqS cnorm(sync) rel.seqS cnorm(eatr) $

  Prove the following statements by direct induction.

  1. $a crel((strong rel.seqS eat)) b -> a crel((eat rel.seqS strong)) b $
  2. $a crel((eatr rel.seqS strong)) b -> a crel((strong rel.seqS eatr)) b $

  Then, let us prove the goal by tower induction on

  $ P th cF := cnorm(iteq(X^rel.r_1)) rel.seqS cF th X^rel.r_2 rel.seqS cnorm(iteq(X^rel.r_3))
    lt.tilde cF th (X^rel.r_1 rel.seqS X^rel.r_2 rel.seqS X^rel.r_3). $

  $P$ is inf-closed. Assuming $P th cF$, let us prove $P th (itree.wb_Sigma th cF)$, i.e.,

  $ cnorm(iteq(X^rel.r_1)) rel.seqS itree.wb_Sigma th cF th X^rel.r_2 rel.seqS cnorm(iteq(X^rel.r_3))
    lt.tilde itree.wb_Sigma th cF th (X^rel.r_1 rel.seqS X^rel.r_2 rel.seqS X^rel.r_3). $

  By one-step unfolding it suffices to prove the following.

  $ cnorm(strong) rel.seqS cnorm(weak) rel.seqS cnorm(strong) lt.tilde cnorm(weak) $

  Introducing and destructing the hypotheses we proceed as follows.

  $ a & strong & b #h(0.6em) & eat    x_1 & sync x_2 & eatr  &  c #h(0.6em) & strong & d & \
    a & eat    & y_1  & strong x_1 & sync x_2 & strong&  y_2 & eatr   & d & quad "by 1. and 2." $

  By concatenation (@lem-actrel-props) between $y_1$ and $y_2$, we obtain 

  $ itree.RS th (X^rel.r_1 rel.seqS X^rel.r_2 rel.seqS X^rel.r_3)
      th (cnorm(iteq(X^rel.r_1)) rel.seqS cF th X^rel.r_2 rel.seqS cnorm(iteq(X^rel.r_3)))
      th y_1 th y_2. $

  By coinduction hypothesis $P th cF$ and monotonicity (@lem-actrel-props)
  we deduce $y_1 crel(xsb(cF)) y_2$ and finally conclude $a weak b$
]

Let us reap some benefits from the very general lemmas we have proven
until now and deduce that strong bisimilarity is included in weak bisimilarity.
Technically the proof is so simple that we would never really use it, as we
would instead "prove" it on-the-fly by applying one of the more powerful
principles. This is particularly true in Rocq, where the
#txtt("setoid_rewrite") mechanism~#mcite(<Sozeau09>) can be hooked up to all of
our monotonicity statements and relation inclusions. This is quite appreciable
as there is a myriad of precise cases where we would like to "rewrite" by
a known bisimilarity proof. Justifying them requires tedious chains of
applications of structural lemmas regarding reflexivity, symmetry and
transitivity such as we just proved. In the following chapters we will not
justify them as thoroughly, but for now let us see how this inclusion property
goes.

#lemma[Strong To Weak][
  Given $Sigma cl icont.t th I$ and $X^rel.r cl rel.irel th X^1 th X^2$, the
  following inclusion holds.

  $ cnorm(iteq(X^rel.r)) lt.tilde cnorm(itweq(X^rel.r)). $
]
#proof[
  Of course the direct proof by tower induction is quite trivial, but as motivated above,
  let us prove it solely by using already proven properties.

  $ cnorm(iteq(X^rel.r))
      & lt.tilde cnorm(iteq(X^rel.r)) rel.seqS rel.diagS rel.seqS rel.diagS & #[diagonal concatenation] \
      & lt.tilde cnorm(iteq(X^rel.r)) rel.seqS cnorm(itweq(rel.diagS)) rel.seqS cnorm(iteq(rel.diagS)) quad quad quad  & #[@lem-wbisim-props and #ref(<lem-sbisim-props>, supplement: "")] \
      & lt.tilde cnorm(itweq(X^rel.r rel.seqS rel.diagS rel.seqS rel.diagS)) & #[@lem-up2strong] \
      & lt.tilde cnorm(itweq(X^rel.r))  & #[@lem-wbisim-props] $

  The only important step is the call to @lem-up2strong, all the rest is simply a matter of
  filling "missing arguments" by reflexivity and refolding them in the conclusion by
  monotonicity.
]

This sequence of juggling concludes our core properties for weak bisimilarity:
we know that for well-behaved $X^rel.r$ it is an equivalence relation and that
it supports coinductive proofs up-to reflexivity, up-to symmetry and up-to
strong bisimilarity.

== Monad Structure <sec-itree-monad>

An important structure available on interaction trees is that they form a monad.
Indeed, as they are parametrized by an _output_ family $X$, a strategy with
output $X$ can be considered as an impure computation returning some $X$.  Its
_effects_ will be to perform game moves and wait for an answer. While at first
sight---considering only the goal of representing game strategies---such an
output might seem unnecessary, the compositionality offered by monads, that is,
sequential composition, is tremendously useful to construct and reason on
strategies piece wise.

The monad structure on interaction trees takes place in the family category
$base.Type^I$ and its laws hold both w.r.t. strong bisimilarity and weak
bisimilarity. One way to view this is to say that we will define _two_ monads,
respectively defined by quotienting the resulting trees by strong or weak
bisimilarity.
However, in line with our choice of using intensional type theory, we will first
define a _pre-monad_ structure, containing only the computationally relevant
operation and then provide two sets of laws.

In fact, in @def-itree, we have already defined the "return" operator,
$itree.ret$, which can be typed as follows.

$ itree.ret th {X} cl X ctx.arr itree.t_Sigma th X $

Let us define the _fmap_ operator and the _bind_ operator, which works by tree grafting.

#definition[Interaction Tree Fmap][
  For any $Sigma cl icont.t th I$, _interaction tree fmap_ operator is given by
  the following coinductive definition.

  $ nar""cnorm(itree.fmap)nar th {X th Y} cl (X ctx.arr Y) -> itree.t_Sigma th X ctx.arr itree.t_Sigma th Y \
    f itree.fmap t :=
    pat(itree.obs := kw.case t .itree.obs \
      pat(itree.retF th x & := itree.retF th (f th x),
          itree.tauF th t & := itree.tauF th (f itree.fmap t),
          itree.visF th q th k & := itree.visF th q th (kw.fun th r |-> th f itree.fmap k th r))) $
]

#definition[Interaction Tree Bind][ 
  Let $Sigma cl icont.t th I$. For any given $X, Y cl base.Type^I$ and $f cl X ctx.arr
  itree.t_Sigma th Y$, first define _interaction tree substitution_ as follows.

  $ itree.subst_f cl itree.t_Sigma th X ctx.arr itree.t_Sigma th Y \
    itree.subst_f th t :=
    pat(itree.obs := kw.case t .itree.obs \
      pat(itree.retF th x & := (f th x) .itree.obs,
          itree.tauF th t & := itree.tauF th (itree.subst_f th t),
          itree.visF th q th k & := itree.visF th q th (kw.fun th r |-> th itree.subst_f th (k th r)))) $
  #margin-note(dy: -8.5em)[
    Note that defining $itree.subst_f$ _with $f$ fixed_ is not a
    mere stylistic consideration.  Indeed, what it achieves, is to pull the
    binder for $f$ out of the coinductive definition. This enables the syntactic
    guardedness checker to more easily understand subsequent coinductive
    definitions making use of the bind operator. To the best of my knowledge,
    this trick was first used in the #txsc[InteractionTree]
    library~#num-cite(<XiaZHHMPZ20>). In general, it is always fruitful to take
    as many binders as possible out of a coinductive definition.
  ]

  Then, define the _interaction tree bind_ operator as

  $ ar""cnorm(itree.bind)ar th {X th Y th i} cl itree.t_Sigma th X th i -> (X ctx.arr itree.t_Sigma th Y) -> itree.t_Sigma th Y th i \
    t itree.bind f := itree.subst_f th t $

  and the _kleisli composition_ as

  $ ar""cnorm(itree.kbind)ar th {X th Y th Z} cl (X ctx.arr itree.t_Sigma th Y) -> (Y ctx.arr itree.t_Sigma th Z) \
    #h(6.1em) -> (X ctx.arr itree.t_Sigma th Z) \
    (f itree.kbind g) th x := f th x itree.bind g. $
]

#remark[
  The above presentation of the bind operator can be recognized as the
  _daemonic bind_ of #nm[McBride]~#mcite(<McBride11>), who studied monads on
  type families of the exact same kind as we do. The indexing provides us
  with the _starting_ position of the computation (in our case, strategy), but we do
  not know the _ending_ position at which a $itree.retF$ might appear. In
  face of this uncertainty, which they called _daemonic_, the continuation
  must be able to treat _any_ possible position.

  #nm[McBride] further shows how we can generically derive a doubly-indexed
  _parametrized monad_~#mcite(<Atkey09>) this time operating on sets and not
  families, which can be represented as follows.

  $ M cl base.Type -> I -> I -> base.Type $

  This second representation supports a corresponding _angelic_ bind
  operator, where the end position of the head computation is known, such that
  the continuation need only to handle that one. It is typed as follows.

  $ nar""cnorm(itree.bind)nar cl M th X th i th j -> (X -> M th Y th j th k) -> M th X th i th k $

  The trick is to define the following predicate _at-key_ essentially encoding
  the fibers of a constant function $(kw.fun th x |-> i) cl X -> I$.

  #let atkey = $de(cbin(@))$
  #mathpar(block: true,
    $kw.dat nar""cnorm(atkey)nar cl base.Type -> I -> I -> base.Type \ #v(0.5em)$,
    $inferrule(x cl X, cs("ok") th x cl (X atkey i) th i)$
  )

  This enables to type a hybrid _angelic_ bind on interaction trees as follows.

  $ nar""cnorm(itree.bind)nar cl itree.t_Sigma th (X atkey j) th i -> (X -> itree.t_Sigma th Y th j) -> itree.t_Sigma th Y th i $

  Sadly this thesis we make very little use of such new tricks that can be
  pulled in indexed settings. We will only need to study the operators
  and properties lifted from the non-indexed setting, which are thus always
  quite unoriginal w.r.t. indexing.
]

Before proving the monad laws, we will first prove that our operators respect
both strong and weak bisimilarity, in other words that they are monotone. For
strong bisimilarity and $itree.ret$, the statement is the following.

$ forall th {X^rel.r cl rel.irel th X^1 th X^2} th {i cl I} th {x_1 cl X^1 th i} th {x_2 cl X^1 th i} \
  quad -> X^rel.r th x_1 th x_2 -> itree.ret th x_1 iteq(X^rel.r) itree.ret th x_2 $

This is quite heavy, and many more complex monotonicity statements will appear
in the thesis. Thus, from now on, we will extensively use relational
combinators. To simplify reading such complex relations, we will write $a
xrel(R) b$ for $R th a th b$. Our final goal is to replace the above verbose
statement with the following.

$ forall th {X^rel.r} -> itree.ret xrel(X^rel.r rel.iarr cnorm(iteq(X^rel.r))) itree.ret $

To achieve this, we define the following combinators.

$ ar rel.arr ar cl rel.rel th X_1 th X_2 -> rel.rel th Y_1 th Y_2 -> rel.rel th (X_1 -> Y_1) th (X_2 -> Y_2) \
  (R rel.arr S) th f th g := forall th {x_1 x_2} -> R th x_1 th x_2 -> S th (f th x_1) th (g th x_2) $

$ ar rel.iarr ar cl rel.irel th X_1 th X_2 -> rel.irel th Y_1 th Y_2 -> rel.irel th (X_1 ctx.arr Y_1) th (X_2 ctx.arr Y_2) $
#v(-0.5em)
$ (R rel.iarr S) th f th g := forall th {i th x_1 th x_2}
 -> R th {i} th x_1 th x_2 -> S th {i} th (f th x_1) th (g th x_2) $

$ rel.forall cl rel.irel th X_1 th X_2 -> rel.rel th (forall th {i} -> X_1 th i) th (forall th {i} -> X_2 th i) \
  rel.forall R th f th g := forall th {i} -> R th (f th {i}) th (g th {i}) $

Moreover, we will write $rel.forall A$ for $rel.forall (kw.fun th {i} |-> th A)$, with a very
weak parsing precedence.

#lemma[ITree Monad Monotonicity][
  Given $Sigma cl icont.t th I$, for any
  $X^rel.r$ and $Y^rel.r$ and for any strong or weak bisimulation candidate $cF in
itree.sb_Sigma$ or $cF in itree.wb_Sigma$, the following holds.

  1. $itree.ret xrel(rel.forall X^rel.r rel.carr cF th X^rel.r) itree.ret$
  2. $(ar""cnorm(itree.fmap)ar) xrel((rel.forall X^rel.r rel.carr Y^rel.r) rel.arr (rel.forall cF th X^rel.r rel.carr cF th Y^rel.r)) (ar""cnorm(itree.fmap)ar)$
  3. $(nar""cnorm(itree.bind)ar) xrel(rel.forall th cF th X^rel.r rel.arr (rel.forall X^rel.r rel.iarr cF th Y^rel.r) rel.arr cF th Y^rel.r) (ar""cnorm(itree.bind)ar)$

  As direct consequences, return, fmap, and bind respect both strong and weak bisimilarity:
  4. $itree.ret xrel(rel.forall X^rel.r rel.carr cnorm(iteq(X^rel.r))) itree.ret$
  5. $itree.ret xrel(rel.forall X^rel.r rel.carr cnorm(itweq(X^rel.r))) itree.ret$
  6. $(ar""cnorm(itree.fmap)ar) xrel((rel.forall X^rel.r rel.carr Y^rel.r) rel.arr (rel.forall cnorm(iteq(X^rel.r)) rel.carr cnorm(iteq(Y^rel.r)))) (ar""cnorm(itree.fmap)ar)$
  7. $(ar""cnorm(itree.fmap)ar) xrel((rel.forall X^rel.r rel.carr Y^rel.r) rel.arr (rel.forall cnorm(itweq(X^rel.r)) rel.carr cnorm(iteq(Y^rel.r)))) (ar""cnorm(itree.fmap)ar)$
  8. $(ar""cnorm(itree.bind)ar) xrel(rel.forall th cnorm(iteq(X^rel.r)) rel.arr (rel.forall X^rel.r rel.iarr cnorm(iteq(Y^rel.r))) rel.arr cnorm(iteq(Y^rel.r))) (ar""cnorm(itree.bind)ar)$
  9. $(ar""cnorm(itree.bind)ar) xrel(rel.forall th cnorm(itweq(X^rel.r)) rel.arr (rel.forall X^rel.r rel.iarr cnorm(itweq(Y^rel.r))) rel.arr cnorm(itweq(Y^rel.r))) (ar""cnorm(itree.bind)ar)$
] <lem-up2bind>

#proof[

  1. For $cF in itree.sb_Sigma$, assuming $X^rel.r th x_1 th x_2$, $itree.retR$ proves $ itree.sb_Sigma th cF th X^rel.r
    th (itree.ret th x_1) th (itree.ret th x_2), $ which by @lem-tower-props
    entails $cF th X^rel.r th (itree.ret th x_1) th (itree.ret th x_2)$. The
    proof for $cF in itree.wb_Sigma$ is similar, using reflexivity of
    $itree.eat_Sigma$.
  2. By tower induction on the statement. For $cF in itree.sb_Sigma$ it is direct
     by case analysis. For $cF in itree.wb_Sigma$, use the fact that

     #let xfmap = $de(prime.rev.double""cnorm(itree.fmap))$
     $ t_1 itree.eatlr t_2 -> (f th xfmap th t_1) itree.eatlr (f th xfmap th t_2) $

     where $xfmap$ is the one step unfolding of $itree.fmap$ operating on an exposed interaction tree.
  3. By tower induction on the statement. For $cF in itree.sb_Sigma$ it is direct
     by case analysis. For $cF in itree.wb_Sigma$, use the following fact.

     #let xbind = $de(prime.rev.double""cnorm(itree.bind))$
     $ t_1 itree.eatlr t_2 -> (t_1 th xbind th f) itree.eatlr (t_2 th xbind th f) $
  (4--9) By direct application of (1--3), using @lem-tower-fix.
]

While perhaps not very impressive, the above lemma is very important. Points (4--9)
prove that return, fmap and bind are well-defined as operators on the quotients of strategies
respectively by strong and weak bisimilarity. But more importantly, points (1--3)
prove that one can reason compositionally _during_ any bisimulation proof. To relate
two returns under any bisimulation candidate, simply relate their output. To relate
two sequential compositions (bind) under any bisimulation candidate, it suffices to
first relate the two head computations and then, pointwise, the continuations.

#remark[
  This last fact (3) is sometimes called "bisimulation up-to bind". We can now see why it was
  important to construct bisimilarity not as fixed points on a lattice of relations but
  on a lattice of pre-relators. Indeed, the statement (3) makes use of the bisimulation
  candidate at two different output relations $X^rel.r$ and $Y^rel.r$. If we were to use
  the lattice of family relations, the output relation parameter of a bisimulation candidate
  would be fixed, making the statement impossible to write. As it is done in the #txsc[InteractionTree]
  library~#mcite(<XiaZHHMPZ20>), only a weaker statement can be made, in which the head
  computations must be related by bisimilarity, instead of the bisimulation candidate.
]

Before turning to the monad and functor laws, let us revisit the property of
relators regarding relation re-indexing that we were missing in
@lem-sbisim-props and @lem-wbisim-props. As we now know the action $itree.fmap$
of $itree.t$ on morphisms, we can give its statement and proof. Intuitively, it states
that whenever two "fmap-ed" computations are related by some bisimulation candidate,
then their inside computation is actually directly related by the candidate, with
a re-indexed output relation.

#lemma[Bisimulation Re-Indexing][
  Given $Sigma cl icont.t th I$, for any
  $X^rel.r cl rel.irel th X_1 th X_2$, $f_1 cl Y_1 ctx.arr X_1$ and $f_2 cl Y_2 ctx.arr X_2$ and for any strong or weak bisimulation candidate $cF in
  itree.sb_Sigma$ or $cF in itree.wb_Sigma$, the following holds.

  $ (f_1 itree.fmap ar) relix(cF th X^r) (f_2 itree.fmap ar) quad lt.tilde quad cF th (f_1 relix(X^r) f_2) $
]
#proof[
  By tower induction on the statement. For $cF in itree.sb_Sigma$ it is direct
  by case analysis. For $cF in itree.wb_Sigma$, use the following fact.

  #let xfmap = $de(prime.rev.double""cnorm(itree.fmap))$
  $ (f_1 th xfmap th t_1) itree.eatlr t_2 -> exists th t_3, th (t_1 itree.eatlr t_3) and t_2 = (f th xfmap th t_3) $
  #v(-2em)
]

#remark[
  Together with @lem-sbisim-props, the above lemma verifies that any strong
  bisimulation candidate is a relator for $itree.t_Sigma$. Moreover, @lem-up2bind verifies
  that any strong bisimulation candidate is a monad relator for $itree.t_Sigma$, in the
  sense of~#nm[Dal Lago], #nm[Gavazzo] and #nm[Levy]~#mcite(<LagoGL17>).
  As such, we can in a sense say that "up-to relator principles" are valid for
  strong bisimilarity, which is just a precise way to say that standard
  compositional reasoning is allowed during strong bisimilarity proofs.

  The same is almost entirely true for weak bisimilarity, with the sole exception of
  transitivity. As such, although weak _bisimilarity_ is indeed a monad relator,
  weak bisimulation _candidates_ fail the generalized transitivity requirement.
]

We can finally prove the monad laws as well as coherence of fmap. We only prove
them w.r.t. strong bisimilarity, as this implies weak bisimilarity.

#lemma[ITree Monad Laws][
  Given $Sigma cl itree.t_Sigma$, for all $x cl X th i$, $t cl itree.t_Sigma th
  X th i$, $f cl X ctx.arr itree.t_Sigma th Y$, $g cl Y ctx.arr itree.t_Sigma th Z$
  and $h cl X ctx.arr Y$ the following statements are true.

  1. $(itree.ret th x itree.bind f) itree.eq f th x$
  2. $(t itree.bind itree.ret) itree.eq t$
  3. $(t itree.bind f) itree.bind g itree.eq t itree.bind (f itree.kbind g)$
  4. $(t itree.bind (itree.ret compose h)) itree.eq (h itree.fmap t)$
]
#proof[
  1. By one-step unfolding.
  2. By direct tower induction.
  3. By direct tower induction.
  4. By direct tower induction.
  #v(-2em)
]

#remark[
  Note that as a direct consequence of the above lemma, we can derive the usual
  properties of fmap, exhibiting $itree.t_Sigma$ as a functor.
]

This concludes the monadic theory of interaction trees. We put a finishing touch by
introducing the so-called "do notation". We write, e.g.,

$ kw.do x <- t; th y <- f th x; th g th y $

instead of

$ t itree.bind (kw.fun th x |-> th f th x itree.bind (kw.fun th y |-> th g th y)). $

/*
To make the best out of this syntax, we finish up by defining some "generic
effects", i.e., helpers to perform a silent step or play a move.

#tom[
  C'est quoi un "generic effect"? Pourquoi on appelle ça comme ça? La def de
  $itree.xvis$ est très bizarre, pas fastoche à lire, et pas utilisée pour
  l'instant dans la suite...
]
#peio[
  Effectivement c'est tricky en indexés, avec l'apparition de #subs.fiber pour
  passer d'une famille fibrée à une famille indexée. Le
  generic effect d'une theorie algébrique c'est la transfo $Sigma => T_Sigma$,
  qui est plus pratique à utiliser en do-notation que la structure d'algèbre
  $Sigma T_Sigma => T_Sigma$. Je garde en suspend: si c'est nécessaire plus tard
  je détaille plus, sinon j'enlèverai.
]

#definition[Generic Effects][
  Given $Sigma cl icont.t th I$, we define the following generic effects,

  $ itree.xtau th {i} cl itree.t_Sigma th (subs.fiber th (kw.fun th x cl base.unit. th i) th i \
    itree.xtau := itree.tau th (itree.ret th (subs.fib th base.tt)) $

  $ itree.xvis th {i} th (q cl Sigma .icont.qry th i) cl itree.t_Sigma th (subs.fiber th (Sigma .icont.nxt th {q})) th i \
    itree.xvis th q := itree.vis th q th (kw.fun th r. th itree.ret th (subs.fib th r)) $

  #margin-note(dy: -4em)[ While slightly funky, the type of $itree.xvis$ is
    quite notable: it is the type of what #nm[Xia] et. al~#num-cite(<XiaZHHMPZ20>)
    call _event handlers_.  It encodes a natural transformation of $[| Sigma |]$
    into $itree.t_Sigma$. This one in particular is the identity handler, part
    of a larger structure making $itree.t$ a _relative
    monad_~#num-cite(<AltenkirchCU10>) on $icont.t th I -> (base.Type^I ->
    base.Type^I)$. Alas, its definition is irrelevant to OGS correctness and does
    not fit into this margin...

  ]
  where $subs.fiber$ is defined by the following data type.

  $ kw.dat th subs.fiber th (f cl A -> B) cl B -> base.Type kw.whr \
    pat1(subs.fib th (x cl A) cl subs.fiber th f th (f th x)) $
]
*/

== Iteration Operators <sec-iter>

Interaction trees~#mcite(<XiaZHHMPZ20>) were originally introduced to encode
arbitrary---i.e., possibly non-terminating---computation. As such, apart from
monadic operators, they support _iteration operators_ which intuitively allow
one to write arbitrary "while" loops. Pioneered by #nm[Elgot] in the setting
of fixed points in algebraic
theories~#mcite(<Elgot75>), iteration in monadic computations enjoys a vast
literature. Recalling that a monadic term $a cl M th X$ can be seen intuitively as an
"$M$-term" with variables in $X$, the idea is to define systems of recursive
equations as morphisms

$ f cl X -> M th (Y + X). $

Assuming $X := { x_i }_(1 <= i <= n)$ and writing $f_i$ for $f th x_i$, this system is intuitively

$ s_1 & itree.weq f_1 && [x_1 |-> s_1, x_2 |-> s_2, th ..., th x_n |-> s_n] \
  s_2 & itree.weq f_2 && [x_1 |-> s_1, x_2 |-> s_2, th ..., th x_n |-> s_n] \
      & th dots.v \
  s_n & itree.weq f_n && [x_1 |-> s_1, x_2 |-> s_2, th ..., th x_n |-> s_n], $

where each $f_i$ is an $M$-term mentioning any recursive variables $x_j
cl X$ or any parameter $y_j cl Y$. A _solution_ is then a mapping $s cl X ->
M th Y$ assigning to each "unknown" in $X$ an $M$-term mentioning only
parameters in $Y$. A solution must obviously satisfy the original equation
system, which in the monadic language may be stated as follows.

$ s th x
  #h(1.4em) itree.weq #h(1.4em)
  f th x itree.bind
      funpat(gap: #0em,
          base.inj1 th y & |-> th itree.ret th y,
          base.inj2 th x & |-> th s th x,
) $

While the basic idea is simple, a number of subtle questions arise quite quickly
during axiomatization. Should all equation systems have solutions? Should the
solution be unique? If not, when some solution can be selected by an
iteration operator, what coherence properties should this operator satisfy? In
fact, almost all imaginable points in the design space have been explored, in an
explosion of competing definitions. The concepts have historically been
organized roughly as follows.

#block(stroke: 1pt, inset: 0.8em, radius: 5pt)[
*Iterative Things* ~~ Every _guarded_ equation
system, i.e., eliminating problematic equations where
some $x_i approx x_j$, has a _unique_ solution. The following variants have been defined (not all of comparable generality):

- _iterative theories_, for terms in finitary algebraic theories~#mcite(dy:
  -4em, <Elgot75>),
- _iterative algebras_, for algebras associated to such theories~#mcite(dy: -2em, <Nelson83>),
- _completely iterative monads_, for _ideal_ monads, where there is a way to
    make sense of guardedness~#mcite(dy: -2.5em, <AczelAMV03>).
- _completely iterative algebras_, for functor algebras, with an adapted notion of _flat_
  equation system~#mcite(dy: -1em, <AdamekMV04>),

Absence of the prefix "completely" denotes the fact that only finitary equation
systems are solved.
]

#block(stroke: 1pt, inset: 0.8em, radius: 5pt)[
*Iteration Things and #nm[Elgot] Things* ~~ Every equation system has a _choice_ of
solution, subject to coherence conditions. The following notions have been
defined:

- _iteration theories_, for terms in finitary algebraic theories~#mcite(dy: -4em, <BloomE93>),
- _#nm[Elgot] algebras_, for finitary functor algebras~#mcite(dy: -2em, <AdamekMV06>),
- _#nm[Elgot] monads_, for finitary monads~#mcite(dy: -1em, <AdamekMV10>),
- _complete #nm[Elgot] monads_, for any monad~#mcite(dy: 1em, <GoncharovRS15>).

The older "iteration" prefix requires only the four so-called #nm[Conway] axioms on
the iteration operator, while the more recent "#nm[Elgot]" prefix denotes the addition
of the "uniformity" axiom. The prefix "complete" has the same meaning as for
iterative things.
]

More recently, several works have tried to unify the above two families, by
axiomatizing abstract _guardedness criteria_, for which guarded equations have a
coherent choice of solution~#mcite(<GoncharovRP17>)#mcite(dy: 4em,
<MiliusL17a>). This criterion may be syntactic as in the first family, or
vacuous (every equation is considered guarded) as in the second
family. The iteration operator may then be axiomatized to be coherent with gradually
more constraining notions of coherence. These coherences can be in the style of
iteration or #nm[Elgot] monads, and culminate in the strongest coherence, the
_unicity_ condition. For the type theory practitioner seeking a modern account,
I recommend in particular #nm[Goncharov] et al.~#num-cite(<GoncharovRP17>),
which also features much appreciated graphical depictions of all kinds of
coherence laws.

The original #nm[InteractionTree] library~#num-cite(<XiaZHHMPZ20>) has for now
only be concerned with an iteration operator solving arbitrary systems, which
can be shown to verify the (complete) #nm[Elgot] monad laws w.r.t. _weak_
bisimilarity. As we will show, this operator lifts without surprises to our
indexed setting. However, unicity of solution is quite a tempting principle
even if it is not available for every equation system, and our OGS correctness
proof will crucially depend it. As such, we will also present the iterative
structure of indexed interaction trees, w.r.t. to two notions of guardedness.
First, the usual simple guardedness of ideal monads~#mcite(<GoncharovRP17>)
and second, a finer notion of _eventual_ guardedness. It is to the best of our
knowledge the first time that this _eventual_ guardedness condition is
presented, although a similar idea is present in several proofs by #nm[Adámek],
#nm[Milius] and #nm[Velebil]~#mcite(<AdamekMV10>).

=== Unguarded Iteration

Let us start by lifting the standard unguarded iteration of interaction trees
to our indexed setting.

By implementing iteration operators we are tickling the limits of what can be
expressed in our metatheory using coinductive definitions. As such this section
and the following will contain a couple tricky functions, which have been
tailored to work well with Rocq's syntactic guardedness checker. We try to
comment on each one, but some will surely remain mysterious. Let us start with
such a function.

#definition[Weird Copairing][
  Given $Sigma cl icont.t th I$ define the following _weird copairing_ function.

  $ weirdcopr(ar,ar) th {X th Y th Z} cl (X ctx.arr itree.tp_Sigma th Z) -> (Y ctx.arr itree.tp_Sigma th Z) \
    #h(6em) -> (X base.sum Y) ctx.arr itree.t_Sigma th Z \
    weirdcopr(f, g) th r :=
      pat(itree.obs := kw.case r \
        pat(base.inj1 th x & := f th x,
            base.inj2 th y & := g th y)) $
]

#remark[
  Note the exposed interaction trees in the codomain of $f$ and $g$ above!
  Moreover, we do not directly case-split on $r$ which would define the function with
  two clauses. Instead, the idea is to be _lazy_ on the argument $r$ and only
  inspect it when the tree is observed, i.e., below $itree.obs$. Indeed, a general trick to help
  satisfy guardedness is to copattern-match on $itree.obs$ as early as
  possible, i.e., use maximally lazy definitions.
]

This helper is enough to provide a clean definition of unguarded iteration.

#definition[Interaction Tree Iteration][
  Let $Sigma cl icont.t th I$. Given an equation $f cl X ctx.arr itree.t_Sigma th (Y
  base.sum X)$, define its _iteration_ coinductively as follows.

  $ itree.iter_f cl X ctx.arr itree.t_Sigma th Y \
    itree.iter_f th x := f th x itree.bind weirdcopr(itree.retF,itree.tauF compose itree.iter_f) $
] <def-iter>

#remark[
  It is quite a miracle that this coinductive definition is accepted. In Rocq,
  it depends on two crucial tricks we have seen: the lazy copairing and the
  bind operator defined with the continuation bound outside of the
  coinductive definition. If either is skipped, the above definition is
  rejected. The more robust way to define unguarded iteration would be to
  specialize the bind operator, generalizing the above definition to

  $ de("iter-aux")_f cl itree.t_Sigma th (Y base.sum X) ctx.arr itree.t_Sigma th Y $

  and then defining $itree.iter_f th x := de("iter-aux")_f th (f th x)$. This
  would however require proving more properties, relating this specialized
  bind operator to the usual one.
]

#lemma[Iter Fixed Point][ \
  Given $Sigma cl icont.t th I$, for all $f cl X ctx.arr itree.t_Sigma th (Y + X)$,
  $itree.iter_f$ is a weak fixed point of $f$, i.e., the following holds.

  $ itree.iter_f th x
    itree.weq
    f th x itree.bind
        funpat(gap: #0em,
               base.inj1 th y & |-> th itree.ret th y,
               base.inj2 th x & |-> th itree.iter_f th x) $
]
#proof[
  By definition $itree.iter_f th x := f th x itree.bind weirdcopr(itree.retF,itree.tauF compose itree.iter_f)$.
  As such, both sides start with the same computation $f th x$. By @lem-up2bind it suffices to prove that
  the continuations are pointwise weakly bisimilar. Introduce $r cl Y base.sum X$ and proceed by
  one-step unfolding (@lem-tower-props (1)).
  - For $base.inj1 th y$, conclude by $itree.retR$.
  - For $base.inj2 th x$, eat the #itree.tauF on the left on conclude by reflexivity.
  #v(-2em)
]

Furthermore, we prove the following monotonicity statement for iteration.

#lemma[Iter Monotonicity][ \
  Given $Sigma cl icont.t th I$, for all $X^rel.r cl rel.irel th X^1 th X^2$ and
  $Y^rel.r cl rel.irel th Y^1 th Y^2$, the following statements holds.

  1. $ itree.iter xrel((rel.forall X^rel.r rel.iarr iteqn(Y^rel.r rel.sum th X^rel.r)) rel.arr (rel.forall X^rel.r rel.iarr iteqn(Y^rel.r))) itree.iter $
  2. $ itree.iter xrel((rel.forall X^rel.r rel.iarr itweqn(Y^rel.r rel.sum th X^rel.r)) rel.arr (rel.forall X^rel.r rel.iarr itweqn(Y^rel.r))) itree.iter $
] <lem-iter-mon>
#proof[
  The proof is by straightforward tower induction. Let us detail it for strong bisimilarity.
  By tower induction, let us prove that for all $cF in tower.t_(itree.sb_Sigma)$ the following
  holds.
  $ itree.iter xrel((rel.forall X^rel.r rel.iarr cF th (Y^rel.r rel.sum th X^rel.r)) rel.arr (rel.forall X^rel.r rel.iarr cF th Y^rel.r)) itree.iter $

  The statement is inf-closed. Assuming the statement for $cF$, let us prove it for
  $itree.sb_Sigma th cF$. Introduce the hypotheses
  $ f^rel.r cl f^1 xrel(rel.forall X^rel.r rel.iarr itree.sb_Sigma th cF th (Y^rel.r rel.sum th X^rel.r)) f^2 \
    x^r cl X^rel.r th x^1 th x^2. $

  We need to prove
  $ itree.iter th f^1 th x^1 xrel(itree.sb_Sigma th cF th Y^rel.r) itree.iter th f^2 th x^2 $

  By definition, both sides are given by binds, respectively starting by $f^1 th x^1$ and $f^2 th x^2$.
  By $x^rel.r$ applied to $f^rel.r$, these are related suitably, so that by
  @lem-up2bind it now suffices to relate the continutations pointwise.
  - For $base.inj1 th y$, conclude by $itree.retR$ and reflexivity on $y$.
  - For $base.inj2 th x$, conclude by $itree.tauR$ and coinduction hypothesis.
  #v(-2em)
]

We will not prove here that this iteration operator satisfies the requirements
of complete #nm[Elgot] monads. These properties could be useful for reasoning about
interaction trees constructed by iteration, but they are quite limited compared
to something such as uniqueness of solutions. The prime shortcoming of these
coherence properties, is that they are limited to rearranging equation systems.
As such, they are hardly useful to establish bisimilarity between an interaction
tree constructed by iteration and another one, constructed entirely differently.
Because such a bisimilarity proof will be at the cornerstone of our OGS
correctness proof, we need to look further into guardedness, the key to
uniqueness of solutions.

=== Guarded Iteration

A general trend in the research on iteration operators is the observation that,
very often, the unguarded iteration operator of, e.g., an #nm[Elgot] monad, may be
shown to somehow derive from an underlying _guarded_ iteration operator enjoying
unique fixed points, with the former #nm[Elgot] monad typically being a quotient of the
latter iterative monad. With interaction trees, we find ourselves exactly in this situation.
Indeed, as we will see, every equation system is weakly bisimilar to a guarded
equation system. Our previous unguarded iteration operator can then be recast as
constructing the unique fixed point of this new guarded equation system, up to strong
bisimilarity#margin-note(dy: -4em, mark: true)[
  In hindsight, it should not come as a surprise that primitively only guarded and
  unique fixed points exist. This is what coinduction in our metatheory provides us with.
  Because we work in a constructive metatheory there is no place for doubt, and
  to be accepted, any definition must precisely, i.e., _uniquely_, pinpoint some semantical
  object. It is rather tautological that any definition must indeed
  define something!
].
Without further ado, let us define this guarded iteration operator.

#definition[Guardedness][ Let $Sigma cl icont.t th I$. An action is _guarded in
  $X$_ if it satisfies the predicate
  $ kw.dat itree.actguard th {X th Y th A th i} cl itree.F_Sigma th (Y base.sum X) th A th i -> base.Prop $
  defined by the following constructors.

  #mathpar(block: true, spacing: 1fr,
    inferrule("", $itree.gret cl itree.actguard th (itree.retF th (base.inj1 th y))$),
    inferrule("", $itree.gtau cl itree.actguard th (itree.tauF th t)$),
    inferrule("", $itree.gvis cl itree.actguard th (itree.visF th q th k)$),
  )

  Furthermore, an interaction tree is _guarded in $X$_ if its observation is:

  $ itree.guard th {X th Y th i} cl itree.t_Sigma th (Y base.sum X) th i -> base.Prop \
    itree.guard th t := itree.actguard th t .itree.obs . $

  And, finally, guardedness of equations is defined pointwise:

  $ itree.eqguard th {X th Y} cl (X ctx.arr itree.t_Sigma th (Y base.sum X)) -> base.Prop \
    itree.eqguard th f := forall th {i} th (x cl X th i) -> itree.guard th (f th x) . $
] <def-guarded>

Before even constructing them, we can prove that fixed points of guarded equations
w.r.t. strong bisimilarity are unique.

#lemma[Unique Guarded Fixed Points][
  Given $Sigma cl icont.t th I$ and a guarded equation $f cl X ctx.arr
  itree.t_Sigma th (Y base.sum X)$, for any two fixed points $s_1, s_2$ of
  $f$ w.r.t. strong bisimilarity, i.e., such that for all $x$ and $i = 1, 2$ we have

  $ s_i th x
    itree.eq
    f th x itree.bind
        funpat(gap: #0.2em,
        base.inj1 th y & |-> th itree.ret th y,
        base.inj2 th x & |-> th s_i th x,
    ) quad , $
  then for all $x$, $s_1 th x itree.eq s_2 th x$.
] <lem-gfix-uniq>
#proof[
  By tower induction, assume a strong bisimulation candidate $cF$ such that
  $ forall th x -> cF th rel.diagS th (s_1 th x) th (s_2 th x) $
  and introduce the argument $x$. After rewriting (using up-to transitivity, @lem-sbisim-props) by both fixed point hypotheses, the
  goal is now to prove

    $ (f th x itree.bind
        funpat(gap: #0em,
        base.inj1 th y & |-> th itree.ret th y,
        base.inj2 th x & |-> th s_1 th x,
    )) \
    quad quad xrel(itree.sb_Sigma th cF th rel.diagS) \
    (f th x itree.bind
        funpat(gap: #0em,
        base.inj1 th y & |-> th itree.ret th y,
        base.inj2 th x & |-> th s_2 th x,
    ))
  $

  By inspecting the first step of $f th x$, by guardedness we obtain a
  synchronization and it now suffices to prove that for some tree $t$
  the following holds.

  $ (t itree.bind
        funpat(gap: #0em,
        base.inj1 th y & |-> th itree.ret th y,
        base.inj2 th x & |-> th s_1 th x,
    ))
    xrel(cF th rel.diagS)
    (t itree.bind
        funpat(gap: #0em,
        base.inj1 th y & |-> th itree.ret th y,
        base.inj2 th x & |-> th s_2 th x,
    ))
  $

  Conclude by up-to-bind (@lem-up2bind) and case analysis, with the first case
  proven by reflexivity and the second by coinduction hypothesis.
]

Let us now construct this unique fixed point.

#definition[Guarded Iteration][
  Let $Sigma cl icont.t th I$. Given an equation $f cl X ctx.arr
  itree.t_Sigma th (Y base.sum X)$ with guardedness witness $H cl itree.eqguard th f$,
  first define the following _guarded unfolding function_.

  $ itree.gstep_(f,H) cl (itree.t_Sigma th (Y base.sum X) ctx.arr itree.t_Sigma th Y) -> (X ctx.arr itree.tp_Sigma th Y) \
    itree.gstep_(f,H) th g th x := kw.case (f th x) .itree.obs | H th x \
    pat((itree.retF th (base.inj1 y)) & th p  & := itree.retF th y,
        (itree.retF th (base.inj2 x)) & th (!) & #hide($:=$),
        (itree.tauF th t)             & th p  & := itree.tauF th (g th t),
        (itree.visF th q th k)        & th p  & := itree.visF th q th (kw.fun th r |-> th g th (k th r))) $

  We then define the following coinductive auxiliary function.

  $ itree.giter^de("aux")_(f,H) cl itree.t_Sigma th (Y base.sum X) ctx.arr itree.t_Sigma th Y \
    itree.giter^de("aux")_(f,H) th t := t itree.bind weirdcopr(itree.retF, itree.gstep_(f,H) th itree.giter^de("aux")_(f,H))
  $

  Finally, we define the _guarded iteration_ as follows.

  $ itree.giter_(f,H) cl X ctx.arr itree.t_Sigma th Y \
    itree.giter_(f,H) th x := itree.giter^de("aux")_(f,H) th (f th x) $

  We will omit the guardedness witness $H$ when clear from context.
] <def-giter>

#remark[
  While a bit scary, the above definition of $itree.gstep$ is simply mimicking
  the first step of a "bind" on $f th x$, delegating the rest of the work to
  its argument $g$. Thanks to the added information from the guardedness
  witness, it is able to only trigger subsequent computation in a guarded
  fashion. This can be seen from its type, as it returns an exposed
  interaction tree. Recall that for unguarded iteration, this same
  guardedness was achieved artificially, by wrapping the whole call in a
  silent step.

  Because of this one step of observing on $f th x$, the subsequent computation will be
  triggered on an arbitrary $t cl itree.t_Sigma th (Y base.sum X) th i$, instead of something
  of the form $f th x$. Hence the coinductive knot must be tied with such a generalized
  argument, as is done in $itree.giter^de("aux")$.
]

#theorem[Guarded Fixed Point][
  Let $Sigma cl icont.t th I$. For any guarded equation $f cl X ctx.arr
  itree.t_Sigma th (Y + X)$, $itree.giter_f$ is the unique fixed point of
  $f$ w.r.t. strong bisimilarity.
] <lem-giter-fix>
#proof[
  Since by @lem-gfix-uniq guarded fixed points are unique w.r.t. strong
  bisimilarity, it suffices to show that it is indeed a fixed point, i.e.,

  $ itree.giter_f th x
    itree.eq f th x itree.bind
      funpat(gap: #0em,
        base.inj1 th y & |-> th itree.ret th y,
        base.inj2 th x & |-> th itree.giter_f th x,
      ) $

  As both sides start by binding $f th x$, by @lem-up2bind it suffices to
  relate the continuations pointwise. Introduce the argument $r$ and proceed by
  one-step unfolding (@lem-tower-props (1)), then splitting on $r$. For $r :=
  base.inj1 th y$, conclude by $itree.retR$. For $r := base.inj2 th x$, we
  need to prove the following.

  $ (itree.gstep_f th itree.giter^de("aux")_f th x) .itree.obs xsb(itree.eq) (itree.giter_f th x) .itree.obs $

  Both sides can be seen to start by observing $(f th x) .itree.obs$ so let us case split.

  - $itree.retF th (base.inj1 th y)$ #sym.space.quad Conclude by $itree.retR$ and reflexivity.
  - $itree.retF th (base.inj2 th x)$ #sym.space.quad Absurd by guardedness hypothesis $H th x$.
  - $itree.tauF th t$ #sym.space.quad Conclude by $itree.tauR$ and reflexivity.
  - $itree.visF th q th k$ #sym.space.quad Conclude by $itree.visR$ and pointwise reflexivity.
  #v(-2em)
]

We have thus exhibited interaction trees (considered up to strong bisimilarity)
as a completely iterative monad. Let us now link this to unguarded iteration.

#lemma[
  Given $Sigma cl icont.t th I$ and an equation $f cl X ctx.arr
  itree.t_Sigma th (Y + X)$

  1. Assuming $f$ is guarded, for all $x$, $itree.giter_f th x itree.weq itree.iter_f th x$.
  2. Let $f' th x := f itree.bind (itree.tauF itree.copr itree.retF)$. Then,
     $f'$ is guarded and for all $x$, $ itree.iter_f th x itree.eq itree.giter_f' th x. $  ]
<lem-iter-giter>
#proof[
  1. By tower induction, assume a weak bisimulation candidate $cF$ such that
     the statement holds and let us prove it for $itree.wb_Sigma th cF$.
     Introduce $x$ and rewrite the LHS by the strong fixed point property so that the goal is now
     $ (f th x itree.bind funpat(gap: #0em,
          base.inj1 th y & |-> th itree.ret th y,
          base.inj2 th x & |-> th itree.giter_f th x,
          ))\

        quad quad xrel(itree.wb_Sigma th cF th rel.diagS) \
       (f th x itree.bind weirdcopr(itree.retF,itree.tauF compose itree.iter_f)) $

    Both sides start by observing $f th x$. By case analysis, refute the problematic case
    using the guardedness hypothesis on $f$ and exhibit a synchronization guard ($itree.retR$, $itree.tauR$ or $itree.visR$)
    in the other cases. Both sides still continue to start by the same computation, so that
    by @lem-up2bind it suffices to relate the continuations pointwise w.r.t. $cF$.
    For $base.inj1 th y$ conclude by reflexivity. For $base.inj2 th x$, eat the $itree.tauF$ on
    the right and conclude by coinduction hypothesis.
  2. For any $x$, by case analysis on $(f th x) .itree.obs$ we can show that $f' th x$ is guarded.
     Then, by direct tower induction, following approximately the same proof pattern as (1),
     without eating the $itree.tauF$ at the end.
  #v(-2em)
]

=== Eventually Guarded Iteration

Equipped with this new guarded iteration, we finally obtain our powerful
uniqueness of fixed points. This principle will provide us with a big hammer,
very useful for hitting nails looking like $itree.giter_f th x itree.eq t th x$.
However, being guarded is quite a strong requirement! Notably, our equation of
interest in this thesis, the one defining the composition of OGS strategies and
counter-strategies, has no hope of being guarded. However, observe that if
there is a finite chain $x_1 ↦ x_2 ↦ ... ↦ x_n ↦ t$, such that $t$ is guarded,
then after $n$ iteration step, $x_1$ will be mapped to a guarded $t$. The
iteration starting from $x_1$ is then still uniquely defined. This was already
noted by #nm[Adámek], #nm[Milius] and #nm[Velebil]~#mcite(<AdamekMV10>) with
their notion of _grounded_ variables. However, a clear definition and study of
equations containing only grounded variables, or _eventually guarded equations_
as we call them, is still novel to the best of our knowledge. In fact, in future
work it might be fruitful to consider this in the setting
of~#nm[Goncharov] et al.~#mcite(<GoncharovRP17>), as a generic relaxation of
any abstract guardedness criterion.

#definition[Eventual Guardedness][ Let $Sigma cl icont.t th I$ and $f cl X ctx.arr
  itree.t_Sigma th (Y + X)$. An interaction tree is _eventually guarded w.r.t.
  $f$_ if it verifies the inductive predicate
  $ kw.dat itree.evguard_f th {i} cl itree.tp_Sigma th (Y + X) th i -> base.Prop $
  defined by mutually with the following shorthand

  $ itree.evguard_f th {i} cl itree.t_Sigma th (Y + X) th i -> base.Prop \
    itree.evguard_f th t := itree.actevguard_f th t .itree.obs $

  and whose constructors are given as follows.

  #mathpar(block: true, spacing: 1fr,
    inferrule(
      $p cl itree.actguard th t$,
      $itree.evg th p cl itree.actevguard_f th t$
    ),
    inferrule(
      $p cl itree.evguard_f th (f th x)$,
      $itree.evs th p cl itree.actevguard_f th (itree.retF th (base.inj2 th x))$
    ),
  )

  An equation is _eventually guarded_ if it is pointwise eventually guarded
  w.r.t. itself.

  $ itree.eqevguard th {X th Y} cl (X ctx.arr itree.t_Sigma th (Y + X)) -> base.Prop \
    itree.eqevguard th f := forall th {i} th (x cl X th i) -> itree.evguard_f th (f th x) $
] <def-guarded>

As for guardedness, we can show unicity of fixed points w.r.t. strong bisimilarity of
eventually guarded equations.

#lemma[Uniqueness of Eventually Guarded Fixed Points][
  Given $Sigma cl icont.t th I$ and $f cl X ctx.arr itree.t_Sigma th (Y + X)$ such that
  $f$ is eventually guarded, for any fixed points $g$ and $h$ of $f$ w.r.t.
  strong bisimilarity, for all $x$, we have $g th x itree.eq h th x$.
] <lem-evfix-uniq>
#proof[
  By tower induction, then by induction on the eventual guardedness proof,
  repeatedly rewriting both sides by the fixed point equation to exhibit a
  synchronization point.
]

To construct an eventually guarded fixed point, we reduce the problem to
computing a guarded fixed point. Indeed, any eventually guarded equation can be
pointwise _unrolled_ into a guarded one.

#definition[Unrolling][
  Let $Sigma cl icont.t th I$. Given $f cl X ctx.arr
  itree.t_Sigma th (Y + X)$ and eventually guarded $t$ w.r.t. $f$, define the
  _unrolling of $t$_ as the following inductive definition.

  $ itree.evunroll_f th {i} th (t cl itree.tp_Sigma th (X + Y) th i) cl itree.actevguard_f th t -> itree.tp_Sigma th (X + Y) th i $
  #v(-0.4em)
  $ & itree.evunroll_f th (itree.retF th (base.inj1 th x)) th && (itree.evs th p) & := & itree.evunroll_f th (f th x).itree.obs th p \
    & itree.evunroll_f th (itree.retF th (base.inj2 th y)) th && p & := & itree.retF th (base.inj2 th y) \
    & itree.evunroll_f th (itree.tauF th t) th && p & := & itree.tauF th t \
    & itree.evunroll_f th (itree.visF th q th k) th && p & := & itree.visF th q th k $

  Moreover, define the following _pointwise unrolling_ of $f$.

  $ itree.equnroll_f cl itree.eqevguard th f -> (X ctx.arr itree.t_Sigma th (Y + X)) \
    itree.equnroll_f th H th x := pat(itree.obs := itree.evunroll_f th (f th x).itree.obs th (H th x)) $
]

#lemma[Unroll Guarded][
  Given $Sigma cl icont.t th I$ and $f cl X ctx.arr itree.t_Sigma th (Y + X)$ such that
  $H cl itree.eqevguard th f$, then $itree.equnroll_f th H$ is guarded.
]
#proof[By direct induction.]

We can now define our candidate fixed point by using the guarded iteration.

#definition[Eventually Guarded Iteration][
  Given $Sigma cl icont.t th I$ and $f cl X ctx.arr itree.t_Sigma th (Y + X)$ such that
  $H cl itree.eqevguard th f$, define the _eventually guarded iteration of $f$_ as follows.

  $ itree.eviter_(f,H) cl X => itree.t_Sigma th Y \
    itree.eviter_(f,H) := itree.giter_(itree.equnroll th f th H) $
]

It now remains to verify that this construction is indeed a fixed point
of $f$, as for now we only know that it is a fixed point of the unrolled equation.

#theorem[Eventually Guarded Fixed Point][
  Given $Sigma cl icont.t th I$ and $f cl X ctx.arr itree.t_Sigma th (Y + X)$ such that
  $f$ is eventually guarded, then $itree.eviter_f$ is the unique fixed point of $f$ w.r.t.
  strong bisimilarity.
] <thm-eviter-fix>

#proof[
  By @lem-evfix-uniq, eventually guarded fixed points are unique w.r.t.
  pointwise strong bisimilarity, so it suffices to prove that $itree.eviter_f$ is a fixed
  point of $f$. This is proven by induction on the eventual guardedness witness and
  repeated one-step unfolding on both sides, appealing to the guarded fixed point
  property on the base case.
]

Once again, we further relate the eventually guarded iteration of an equation
with its unguarded iteration.

#lemma[
  Given $Sigma cl icont.t th I$ and an eventually guarded equation $f cl X ctx.arr
  itree.t_Sigma th (Y + X)$, then for all $x$,

  $ itree.eviter_f th x itree.weq itree.iter_f th x $
] <lem-eviter-iter>
#proof[
  By direct tower induction, then by induction on the eventually guardedness witness.
  For the step case, eat the #itree.tauF on the right and conclude by induction hypothesis.
  For the base case proceed by analysis of the guardedness witness, exhibiting a
  synchronization point, then further eat the #itree.tauF on the right and conclude
  by coinduction hypothesis.
]

This concludes not only our study of iteration operators, but this whole
chapter. We now have enough base theory on games and strategies, both
represented as transition systems or as indexed interaction trees. Our last
theorem, unicity of eventually guarded equations, will provide us with the core
coinduction proof technique to obtain OGS correctness. Although we will stop
referring to them at every single step, the bunch of compositional reasoning
principles proven throughout the last few section will also be instrumental in
achieving flexible reasoning on complex game strategies.

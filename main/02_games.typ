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
  #margin-note[This is called _discrete game_ by Levy & Staton~#num-cite(<LevyS14>).]
  Given $I^+, I^- cl base.Set$ a _game with active positions $I^+$
  and passive positions $I^-$_ is given by the following record.
  $ & kw.rec th game.g th I^+ th I^- th kw.whr \
    & quad game.client cl game.hg th I^+ th I^- \
    & quad game.server cl game.hg th I^- th I^+ $
] <def-g>

=== Categorical Structure

In order to make (half-)games into proper categories, we will define their
morphisms. As games are parametrized over sets of positions, game morphisms
could be naturally defined parametrized over position morphisms, in the
displayed style of Benedikt Ahrens and Peter Lumsdaine~#mcite(<AhrensL19>), but
I will resist the urge to dive too deeply into the structure of games and leave
most of it for further work to expose. Indeed we will require none of it
for our main goal of proving OGS correct. Moreover, as already noted by
Pierre-Évariste Dagand and Conor McBride~#mcite(<DagandM13>, supplement: "p. 10")
in the similar setting of indexed containers, the extremely rich
structures at play require advanced concepts to faithfully describe, such as
framed bicategories and two-sided fibrations.

#definition[Half-Game Simulation][
  Given two half-games $A, B cl game.hg th I th J$, a _half-game simulation
  from $A$ to $B$_ is given by the following record.

  $ kw.rec game.hsim th A th B kw.whr \
    quad game.hstr {i} cl A .game.mv th i -> B .game.mv th i \
    quad game.hscoh {i} th (m cl A .game.mv th i) cl B .game.nx th (game.hstr th m) = A .game.nx th m$
]

#definition[Simulation][
  Given two half-games $A, B cl game.g th I^+ th I^-$, a
  _game simulation from $A$ to $B$_ is given by the following
  record.

  $ kw.rec game.sim th A th B kw.whr \
    quad game.scli cl game.hsim th A .game.client th B .game.client \
    quad game.ssrv cl game.hsim th B .game.server th A .game.server $
]

#remark[Half-Game is Functorial][
  $game.hg$ extends to a strict functor $base.Set^"op" -> base.Set -> base.Cat$ as witnessed
  by the following action on morphisms, which we write in infix style.

  $ - game.reixl - game.reixr - cl (I_2 -> I_1) -> game.hg th I_1 th J_1 -> (J_1 -> J_2) -> game.hg th I_2 th J_2 \
    (f game.reixl A game.reixr g) .game.mv th i := A .game.mv th (f th i) \
    (f game.reixl A game.reixr g) .game.nx th m := g th (A .game.nx th m) $

  The identity and composition laws of this functor hold _definitionally_
  (assuming $eta$-laws on records and functions).
]


=== Example Games

Let us introduce a couple example games, to get a feel for their expressivity.

#let conway = (
  t: de("Conway"),
  lft: pr("left"),
  rgt: pr("right"),
  ls: de("G-Conway"),
)

*Conway Games* #sym.space Conway games are an important tool in the study of
_combinatorial games_~#mcite(<Conway76>) and may in fact be considered their prime
definition. I will explain how they are an instance of our notion. The
definition of Conway games is exceedingly simple: a conway game $G cl
conway.t$ is given by two subsets of Conway games $G_L, G_R subset.eq
conway.t$. This self-referential definition should be interpreted as a
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

#definition[Conway Game][
    The set of _Conway games_ is given by the following coinductive record.

    $ kw.rec conway.t cl base.Set kw.whr \
      quad conway.lft cl subs.Fam th conway.t \
      quad conway.rgt cl subs.Fam th conway.t $
]

We can now give the Levy & Staton game of Conway games. As in a Conway game one
does not known whose turn it is to play, the sets of active and passive positions
will be the same. Moreover, the current position is in fact given by the current
Conway game.

#example[Game of Conway Games][
  Notice that $I -> subs.Fam th J$ is just a shuffling of $game.hg th I th J$:

  $ de("fam-to-hg") cl (I -> subs.Fam th J) -> game.hg th I th J \
    (de("fam-to-hg") th F) .game.mv th i := (F th i) .subs.dom \
    (de("fam-to-hg") th F) .game.nx th {i} th d := (F th i).subs.idx th d $

  Then, the _game of Conway games_ can be given as follows.

  $ conway.ls cl game.g th conway.t th conway.t \
    conway.ls .game.client := de("fam-to-hg") th conway.lft \
    conway.ls .game.server := de("fam-to-hg") th conway.rgt $
]

#peio[inj LS $=>$ Conway]

*Applicative Bisimilarity* #sym.space #peio[applicative bisim]

*OGS Game* #sym.space #peio[ogs stlc?]

=== Strategies as Transition Systems

Following Levy & Staton~#num-cite(<LevyS14>) we now define client strategies as
transition systems over a given game. We will only define _client_ strategies,
since _server_ strategies can be simply derived from client strategies on the
dual game---the prime benefit of our symmetric notion of game. We first need to
define two interpretations of half-games as functors.

#definition[Half-Game Functors][
  Given a half-game $G cl game.hg th I th J$, we define the
  _active interpretation_ and _passive interpretation of $G$_ as two functors
  $base.Set^J -> base.Set^I$, written $G game.extA -$ and $G game.extP -$.

  $ (G game.extA X) th i := (m cl G.game.mv th i) times X th (G.game.nx th m) \
    (G game.extP X) th i := (m cl G.game.mv th i) -> X th (G.game.nx th m) $
] <def-hg-ext>

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

#definition[Transition System][
  Given a game $G cl game.g th I^+ th I^-$ and a family $R cl I^+ -> base.Set$,
  a _transition system over $G$ with output $R$_ is given by the following record.

  $
    kw.rec strat.t_G th R kw.whr \
    quad strat.stp cl I^+ -> base.Set \
    quad strat.stn cl I^- -> base.Set \
    quad strat.play cl strat.stp => R + strat.stp + G.game.client game.extA strat.stn \
    quad strat.coplay cl strat.stn => G.game.server game.extP strat.stp $
  #margin-note(dy: -8em)[
    In Levy & Staton~#num-cite(<LevyS14>), the output parameter $R$ is not present and this is
    called a _small-step system over $G$_, and . We can recover their
    definition by setting $R = emptyset$.
  ]
  Where $X => Y := forall th {i}, th X i -> Y i$ denotes a morphism of families.
] <def-tsys>

There is a lot to unpack here. First the states: instead of a mere set, as is
usual in a classical transition system, they here consist of two families
#strat.stp, #strat.stn _over_ respectively the active and passive game
positions. It is important not to confuse _positions_ and _states_. The former
consist of the information used to determine which moves are allowed to be
played. The latter consist of the information used by a given strategy to
determine how to play. Their relationship is similar to that of types to terms.

The $strat.play$ function takes as inputs $i cl I^+$ an active position, $s cl strat.stp th i$ an active
state over it and returns one of three things:

/ $R th i$: "return move" \
  This case was not present in Levy & Staton~#num-cite(<LevyS14>), but
  it allows a strategy to end the game, provided it exhibits an output. As we
  will see in @sec-itree with interaction trees, this is crucial for
  compositional manipulation.

/ $strat.stp th i$: "silent move" \
  In this case, the strategy postpones progression in the game. This case
  allows for strategies to be _partial_ in the same sense as Venanzio Capretta's
  #delay.t monad~#mcite(<Capretta05>). _Total strategies_ without this case would
  make perfect sense, but we are interested in arbitrary, hence partial, computations.

/ $G.game.client game.extA strat.stn$: "client move" \
  By @def-hg-ext, this data consists of a client move valid at the current
  position, together with a passive state over the next position. This case is
  the one which actually _chooses_ a move and sends it to a hypothetical
  opponent.

The #strat.coplay function is simpler. By @def-hg-ext, it takes a passive
position, a passive state over it and a currently valid server move and must
return an active state over the next position.

== Indexed Interaction Trees <sec-itree>

=== Coinductive Strategies

In @def-tsys, I have defined strategies similarly to Levy &
Staton~#mcite(<LevyS14>), that is, by a state-and-transition-function
presentation of automata. This representation is theoretically satisfying,
however most of the time it is painful to work with formally. As an example,
lets assume I want to define a binary combinator, taking two systems as
arguments and returning a third one. Each of these is a dependent record with
four fields, so that I have to work with eight input components to define two
families of states, and then, depending on these new states, I have to
write two suitable transition functions. This is a lot to manage! The heavyness
of explicitely constructing automata is one of the reasons why widely used
programming languages have introduced syntactic facilities like the "yield" and
"await" keywords for writing state machines. #peio[ref?]

The way out of this misery is to forget about states altogether. Notice that
@def-tsys is exactly the definition of a coalgebra for some endofunctor on
$(I^+ -> base.Set) times (I^- -> base.Set)$. Then, as by definition any
coalgebra maps uniquely into the final coalgebra, it is sufficient to work with
this final coalgebra, whose carrier---or states---intuitively consists of
infinite trees, describing the traces of any possible transition system over
$G$.

However, before constructing this final coalgebra, I will simplify the setting
slightly. Notice that we can easily make passive states disappear, by
describing systems as a family of active states $strat.stp cl I^+ -> base.Set$
and a single transition function:

$ strat.stp => R + strat.stp + G.game.client game.extA (G.game.server game.extP strat.stp) $

This exhibits strategies as coalgebras for the following functor.
#margin-note[
  This category is less informative but equally expressive as
  transition systems over $G$, as it forms a coreflective subcategory.
  #peio[right Tom?]
]

$ X |-> R + X + G.game.client game.extA (G.game.server game.extP X)) $

Since in this functor nothing really depends on the server positions $I^-$, we
can play the same trick and eliminate the passive positions from the
description of games, obtaining back indexed polynomial functors, or more
precisely their type theoretic incarnation as _indexed containers_. Remember
that the reason for preferring games over indexed containers was to ease
swapping client and server. But since strategies are inherently biased towards
one side, we might as well use the simpler notion.

#definition[Indexed Container][
  Given $I cl base.Set$, an _indexed container with positions $I$_ is given
  by the following record.

  $ kw.rec icont.t I cl base.Set kw.whr \
    quad icont.qry cl I -> base.Set \
    quad icont.rsp th {i} cl icont.qry th i -> base.Set \
    quad icont.nxt th {i} th {q cl icont.qry th i} cl icont.rsp th q -> I $
]

#definition[Extension of a Polynomial][
  Given an indexed polynomial $Sigma cl icont.t th I$, we define it's extension
  $[| Sigma |] cl base.Set^I -> base.Set^I$ as the following functor.

  $ [| Sigma |] th X th i :=
      (q cl Sigma .icont.qry th i)
      times ((r cl Sigma .icont.rsp th q) -> X th (Sigma .icont.nxt th r)) $
]


#definition[Game to Container][
  We give a functor $floor(-) cl game.g th I^+ th I^- -> icont.t th I^+$ defined
  on objets as follows.

  /*$ (icont.g2c th A) .icont.qry th i := A .game.client"".game.mv th i \
    (icont.g2c th A) .icont.rsp th q := A .game.server"".game.mv th (A .game.client"".game.nx th q) \
    (icont.g2c th A) .icont.nxt th r := A .game.server"".game.nx th r $*/
  $ floor(A) .icont.qry th i := A .game.client"".game.mv th i \
    floor(A) .icont.rsp th q := A .game.server"".game.mv th (A .game.client"".game.nx th q) \
    floor(A) .icont.nxt th r := A .game.server"".game.nx th r $

  It preserves the extension strictly, in the sense that for all $A cl
  game.g th I^+ th I^-$, the functor $A.game.client game.extA (A.game.server game.extP -))$ is
  definitionally equal to $[| floor(A) |]$.
]

#remark[Container to Game][
  Remark that while games contain information about passive positions which
  containers do not, we can make it up and inject them into games as follows.

  $ ceil(-) cl (Sigma cl icont.t th I) -> game.g th I th ((i cl I) times Sigma .icont.qry th i) \
    ceil(Sigma) .game.client"".game.mv th i := Sigma .icont.qry th i \
    ceil(Sigma) .game.client"".game.nx th {i} th m := (i, m) \
    ceil(Sigma) .game.server"".game.mv th (i, m) := Sigma .icont.rsp th m \
    ceil(Sigma) .game.server"".game.nx th m := Sigma .icont.nxt th m $

  Note that $floor(-) compose ceil(-)$ is definitionally equal to the
  identity on containers.
]

After this interlude on indexed containers, we are now ready to go back to
strategies. Recall that we had turned strategies into coalgebras for the
functor $X |-> R + X + G.game.client game.extA (G.game.server game.extP X))$
and that we wanted to construct its final coalgebra. Fully forgetting about
passive information, we can now instead work with the functor
$X |-> R + X + [| Sigma |] th X$ for some container $Sigma$, which I call
the _action functor on $Sigma$_.

#definition[Action Functor][
  Given a signature $Sigma cl icont.t th I$ and an output $R cl
  I -> base.Set$, the _action functor on $Sigma$ with output $R$_,
  $itree.F_Sigma th R cl base.Set^I -> base.Set^I$ is defined by the following
  data type.

  $ kw.dat itree.F_Sigma th R th X th i th base.Set kw.whr \
    quad itree.retF th (r cl R th i) \
    quad itree.tauF th (t cl X th i) \
    quad itree.visF
      th (q cl Sigma .icont.qry th i)
      th (k cl (r cl Sigma .icont.rsp th q) -> X th (Sigma .icont.nxt th r)) $
]

Being itself an instance of indexed container, $itree.F_Sigma th R$ has a
thorougly understood theory of fixpoints~#mcite(<AltenkirchGHMM15>) and we can
form its final coalgebra as a coinductive family which is accepted by most type
theory implementations such as Agda and Coq.

#definition[Indexed Interaction Tree][
  Given a signature $Sigma cl icont.t th I$ and an output $R cl I -> base.Set$,
  the family of _indexed interaction trees on $Sigma$ with output $R$_,
  $itree.t_Sigma th R cl base.Set^I$ is given by the following coinductive
  record.

  $ kw.rec itree.t_Sigma th R th i cl base.Set kw.whr \
    quad itree.obs cl itree.F_Sigma th R th (itree.t_Sigma th R) th i $
]

Notice that this definition is to interaction trees~#mcite(<XiaZHHMPZ20>)
what inductive families are to inductive data types. As we will discover
in the remainder of this chapter, all of the monadic theory of interaction
trees lifts neatly to this newly indexed setting, an "outrageous fortune"
described by Conor McBride in #mcite(dy: 1.2em, <McBride11>).

Before moving on to define bisimilarity, let us first link this definition
to the previous one of transition system over a game.

#definition[Strategies][
  Given a game $G cl game.g th I^+ th I^-$ and output $R cl I^+ -> base.Set$,
  the _active strategies over $G$ with output $R$_, $game.stratA_G th R cl
  I^+ -> base.Set$ and the _passive strategies over $G$ with output $R$_,
  $game.stratP_G th R cl I^- -> base.Set$ are given as follows.

  $ game.stratA_G th R := itree.t_floor(G) th R \
    game.stratP_G th R := G.game.server game.extP game.stratA_G th R $
]

#lemma[System Unrolling][
  Together, $game.stratA_G th R$ and $game.stratP_G th R$ form the state families
  of the final transition system over $G$ with output $R$, as witnessed by
  the following _unrolling maps_, assuming $S cl strat.t_G th R$.

  $ itree.unrollA cl S .strat.stp => game.stratA_G th R \
    itree.unrollP cl S .strat.stp => game.stratP_G th R \
    \
    (itree.unrollA th s) .itree.obs th kw.wit S .strat.play th s \
    quad | cs("inj"_1) th r := itree.retF th r \
    quad | cs("inj"_2) th s' := itree.tauF th (itree.unrollA th s') \
    quad | cs("inj"_3) th (m , s') := itree.visF th m th (itree.unrollP th s') \
    itree.unrollP th s th m := itree.unrollA th (S .strat.coplay th s th m) $

  Where $cs("inj"_1), cs("inj"_2), cs("inj"_3)$ denote the obvious injections into
  the ternary coproduct.
]

=== Bisimilarity

==== Coinduction with Complete Lattices

==== Strong Bisimilarity

==== Weak Bisimilarity

=== Monad Structure

=== Interpretation

== Iteration Operators <sec-iter>

=== Fixpoints of Equations

#import "/lib/all.typ": *

= Coinductive Game Strategies

$#context text.font$

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
notion of _interaction tree_ introduced by Li-yao Xia et
al.~#mcite(<XiaZHHMPZ20>), originally motivated by representing executable
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

#guil[Should you say that $i^+$ is taken in $I^+$ and $i^-$ in $I^-$ ?]

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
Pierre-Évariste Dagand and Conor McBride~#mcite(<DagandM13>, supplement: "Sec. 1.3")
in the similar setting of indexed containers, the extremely rich
structures at play require advanced concepts to faithfully describe, such as
framed bicategories and two-sided fibrations.

#peio["simulation" vs "morphism"?]

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

#guil[You could introduce the notion of composition of simulations,
and the identity simulation.]

#remark[Half-Game is Functorial][
  $game.hg$ extends to a strict functor $base.Set^"op" times base.Set -> base.Cat$ as witnessed
  by the following action on morphisms, which we write curried and in infix style.

  $ ar game.reixl ar game.reixr ar cl (I_2 -> I_1) -> game.hg th I_1 th J_1 -> (J_1 -> J_2) -> game.hg th I_2 th J_2 \
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
_combinatorial games_~#mcite(<Conway76>)#peio[check def there] and may in fact be considered their prime
definition. I will explain how they are an instance of our notion. The
definition of Conway games is exceedingly simple: a Conway game $G cl
conway.t$ is given by two subsets of Conway games $G_L, G_R subset.eq
conway.t$. This self-referential definition should be interpreted as a
coinductive one. The left subset $G_L$ is to be thought of as the set of games
reachable by the left player in one move, and symmetrically for $G_R$.

#guil[I think Joyal was the first to introduce a categorical
structure on Conway games. See also the presentation by
Méllies of Conway games in connection with Game Semantics.]

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
  $base.Set^J -> base.Set^I$, written $G game.extA ar$ and $G game.extP ar$.

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
  Given a game $G cl game.g th I^+ th I^-$ and a family $R cl base.Set^(I^+)$,
  a _transition system over $G$ with output $R$_ is given by the following record.

  $ kw.rec strat.t_G th R kw.whr \
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

#guil[You could explain why there is no return move for Opponent.]

== Strategies as Indexed Interaction Trees <sec-itree>

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
$base.Set^(I^+) times base.Set^(I^-)$. Then, as by definition any
coalgebra maps uniquely into the final coalgebra, it is sufficient to work with
this final coalgebra, whose carrier---or states---intuitively consists of
infinite trees, describing the traces of any possible transition system over
$G$.

However, before constructing this final coalgebra, I will simplify the setting
slightly. Notice that we can easily make passive states disappear, by
describing systems as a family of active states $strat.stp cl base.Set^(I^+)$
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
precisely their type theoretic incarnation as _indexed
containers_~#mcite(<AltenkirchGHMM15>). Remember that the reason for preferring
games over indexed containers was to ease swapping client and server.
#guil[This was not explained before.] But since
strategies are inherently biased towards one side, we might as well use the
simpler notion.

#definition[Indexed Container][
  Given $I cl base.Set$, an _indexed container with positions $I$_ is given
  by the following record.

  $ kw.rec icont.t I cl base.Set kw.whr \
    quad icont.qry cl I -> base.Set \
    quad icont.rsp th {i} cl icont.qry th i -> base.Set \
    quad icont.nxt th {i} th {q cl icont.qry th i} cl icont.rsp th q -> I $
]

#definition[Extension of a Container][
  Given an indexed container $Sigma cl icont.t th I$, we define it's _extension_
  $[| Sigma |] cl base.Set^I -> base.Set^I$ as the following functor.

  $ [| Sigma |] th X th i :=
      (q cl Sigma .icont.qry th i)
      times ((r cl Sigma .icont.rsp th q) -> X th (Sigma .icont.nxt th r)) $
]


#definition[Game to Container][
  We give a functor $floor(ar) cl game.g th I^+ th I^- -> icont.t th I^+$ defined
  on objets as follows.

  /*$ (icont.g2c th A) .icont.qry th i := A .game.client"".game.mv th i \
    (icont.g2c th A) .icont.rsp th q := A .game.server"".game.mv th (A .game.client"".game.nx th q) \
    (icont.g2c th A) .icont.nxt th r := A .game.server"".game.nx th r $*/
  $ floor(A) .icont.qry th i := A .game.client"".game.mv th i \
    floor(A) .icont.rsp th q := A .game.server"".game.mv th (A .game.client"".game.nx th q) \
    floor(A) .icont.nxt th r := A .game.server"".game.nx th r $

  It preserves the extension strictly, in the sense that for all $A cl
  game.g th I^+ th I^-$, the functor $A.game.client game.extA (A.game.server game.extP ar))$ is
  definitionally equal to $[| floor(A) |]$.
]

#remark[Container to Game][
  Remark that while games contain information about passive positions which
  containers do not, we can make it up and inject them into games as follows.

  $ ceil(ar) cl (Sigma cl icont.t th I) -> game.g th I th ((i cl I) times Sigma .icont.qry th i) \
    ceil(Sigma) .game.client"".game.mv th i := Sigma .icont.qry th i \
    ceil(Sigma) .game.client"".game.nx th {i} th m := (i, m) \
    ceil(Sigma) .game.server"".game.mv th (i, m) := Sigma .icont.rsp th m \
    ceil(Sigma) .game.server"".game.nx th m := Sigma .icont.nxt th m $

  Note that $floor(ar) compose ceil(ar)$ is definitionally equal to the
  identity on containers.
]
#guil[What is the identity on containers?]

After this interlude on indexed containers, we are now ready to go back to
strategies. Recall that we had turned strategies into coalgebras for the
functor $X |-> R + X + G.game.client game.extA (G.game.server game.extP X))$
and that we wanted to construct its final coalgebra. Fully forgetting about
passive information, we can now instead work with the functor
$X |-> R + X + [| Sigma |] th X$ for some container $Sigma$, which I call
the _action functor on $Sigma$_.

#definition[Action Functor][
  Given a signature $Sigma cl icont.t th I$ and an output $R cl
  base.Set^I$, the _action functor on $Sigma$ with output $R$_,
  $itree.F_Sigma th R cl base.Set^I -> base.Set^I$ is defined by the following
  data type.

  $ kw.dat itree.F_Sigma th R th X th i cl base.Set kw.whr \
    quad itree.retF th (r cl R th i) \
    quad itree.tauF th (t cl X th i) \
    quad itree.visF
      th (q cl Sigma .icont.qry th i)
      th (k cl (r cl Sigma .icont.rsp th q) -> X th (Sigma .icont.nxt th r)) $
]

Being itself an instance of indexed container, $itree.F_Sigma th R$ has a
thorougly understood theory of fixpoints~#mcite(<AltenkirchGHMM15>) and we can
form its final coalgebra as a coinductive family which is accepted by most type
theory implementations#guil[proof assistants] such as Agda and Coq.

#definition[Indexed Interaction Tree][
  Given a signature $Sigma cl icont.t th I$ and an output $R cl base.Set^I$,
  the family of _indexed interaction trees on $Sigma$ with output $R$_,
  $itree.t_Sigma th R cl base.Set^I$ is given by the following coinductive
  record.

  $ kw.rec itree.t_Sigma th R th i cl base.Set kw.whr \
    quad itree.obs cl itree.F_Sigma th R th (itree.t_Sigma th R) th i $

  Furthermore, define the following shorthands:

  $ (itree.ret th x) .itree.obs := itree.retF th x \
    (itree.tau th t) .itree.obs := itree.tauF th t \
    (itree.vis th q th k) .itree.obs := itree.visF th q th k $
] <def-itree>

#guil[I don't understand these shorthands. In which sense can $itree.ret th x$ be seen
as of type $itree.t_Sigma$ ?]

Notice that this definition is to interaction trees~#mcite(<XiaZHHMPZ20>)
what inductive families are to inductive data types. As we will discover
in the remainder of this chapter, all of the monadic theory of interaction
trees lifts neatly to this newly indexed setting, an "outrageous fortune"
described by Conor McBride in #mcite(dy: 1.2em, <McBride11>).

#guil[Do you mean that this structure of
indexed interaction tree was already present in
#mcite(dy: 1.2em, <McBride11>)?]

Before moving on to define bisimilarity, let us first link this definition
to the previous one of transition system over a game.

#definition[Strategies][
  Given a game $G cl game.g th I^+ th I^-$ and output $R cl base.Set^(I^+)$,
  the _active strategies over $G$ with output $R$_, $game.stratA_G th R cl
  base.Set^(I^+)$ and the _passive strategies over $G$ with output $R$_,
  $game.stratP_G th R cl base.Set^(I^-)$ are given as follows.

  $ game.stratA_G th R := itree.t_floor(G) th R \
    game.stratP_G th R := G.game.server game.extP game.stratA_G th R $
] <def-strat>

#guil[Can you relate this definition of strategies to the one
given in #num-cite(<LevyS14>) (Definition 2)?]

#lemma[System Unrolling][
  Together, $game.stratA_G th R$ and $game.stratP_G th R$ form the state families
  of the final transition system over $G$ with output $R$, as witnessed by
  the following _unrolling maps_, assuming $S cl strat.t_G th R$.

  $ itree.unrollA cl S .strat.stp => game.stratA_G th R \
    itree.unrollP cl S .strat.stn => game.stratP_G th R \
    \
    (itree.unrollA th s) .itree.obs th kw.wit S .strat.play th s \
    quad | cs("inj"_1) th r := itree.retF th r \
    quad | cs("inj"_2) th s' := itree.tauF th (itree.unrollA th s') \
    quad | cs("inj"_3) th (m , s') := itree.visF th m th (itree.unrollP th s') \
    itree.unrollP th s th m := itree.unrollA th (S .strat.coplay th s th m) $

  $cs("inj"_1)$, $cs("inj"_2)$ and $cs("inj"_3)$ denote the obvious injections
  into the ternary coproduct. These functions can be shown to be the
  computational part of the unique coalgebra morphism between $S$ and
  strategies.
] <def-unroll>

#guil[I am struggling to understand this lemma,
what is a state family of the final transition system ?]

== Bisimilarity

The natural notion of equality on automata is the notion bisimilarity.
Intuitively, a bisimulation between two automata consists of a relation between
their respective states, which is preserved by the transition functions. Two
automata are then said to be _bisimilar_ when one can exhibit a bisimulation
relation between them. Another way to phrase this is that two automata are
bisimilar whenever they are related by the greatest bisimulation relation, the
_bisimilarity_, yielding again a coinductive notion. As our strategies feature
_silent moves_ (the #itree.tauF nodes of the action functor), we will need to
consider two variants, _strong_ and _weak_ bisimilarity. Strong bisimilarity
requires that both strategy trees match at each step, fully synchronized. Weak
bisimilarity on the other hand, allows both strategies to differ by a finite
amount of #itree.tauF nodes in between any two synchronization points.

Before translating these ideas into type theory, we will need a bit of
preliminary tools. Most implementations of type theory provide some form of
support for coinductive records (such as @def-itree) and for cofixpoints, or
coinductive definitions (such as @def-unroll). However, these features---in
particular cofixpoints---are at times brittle, because the theory relies on a
syntactic _guardedness_ criterion to decide whether a given definition should
be accepted. For simple definitions---in fact more precisely for
computationally relevant definitions---I will indulge the whims of syntactic
guardedness. But for complex bisimilarity proofs such as which will appear
later in this thesis, being at the mercy of a syntactic implementation detail
is a recipy for failure.

To tackle this problem, Agda provides more robust capabilities in the form of
_sized types_, for which the well-formedness criterion is based on typing.
However they are not available in Coq, the language in which this thesis has
been formalized. Moreover, in Agda's experimental tradition, while they do work
when used in the intended programming patterns, their semantics are still not
fully clear #peio[ref multi-clocked guarded TT] 

#guil[I don't think the connection between sized types and guarded recursive types has been worked out]. We will take an entirely
different route, building coinduction for ourselves, _inside_ type theory.
Indeed, as demonstrated by Damien Pous' coq-coinduction
library~#mcite(<Pous16>, supplement: [https://github.com/damien-pous/coinduction]),
powerful coinductive constructions and reasoning principles for propositional
types are derivable in the presence of impredicativity.

=== Coinduction with Complete Lattices

The basis of coq-coinduction is the observation that with impredicativity,
#base.Prop forms a complete lattice. In fact not only propositions, but also
predicates $X -> base.Prop$ or relations $X -> Y -> base.Prop$, our case of
interest for bisimilarity. By the Knaster-Tarski theorem one can obtain the
greatest fixpoint $nu f := or.big { x | x lt.tilde f th x }$ of any monotone
endo-map $f$ on the complete lattice.

This is only the first part of the story. Indeed this will provide us with the
greatest fixpoint $nu f$, in our case, bisimilarity, but the reasoning
principles will be cumbersome. At first sight, the only principle available is the
following one.

#centering(inferrule(
  [$x lt.tilde f th x$],
  [$x lt.tilde nu f$]
))

Programming solely with this principle is painful, much in the same way as
manipulating inductive types solely using eliminators, instead of using
pattern-matching and recursive functions. Thankfully, in the context of
bisimulations, a line of work has developped a theory of _enhanced_
bisimulations, in which the premise is weakened to $x lt.tilde f th (g th x)$---
bisimulation _up-to $g$_---for some _compatible_ $g$, which must verify $g
compose f lt.tilde f compose g$. This eases bisimilarity proofs where, for
example, the relation between states is only preserved by the transition
functions up-to transitive closure, provided the transitive closure has been
proven compatible.

Satisfyingly, the least upper bound of all compatible function is still
compatible. It is called the _companion_ of $f$, written $t_f$, and moreover
satisfies $t_f bot th approx nu f$. This enables to work with the following
generalized principle.

#centering(inferrule(
  [$x lt.tilde f th (t_f th x)$],
  [$x lt.tilde nu f$]
))

In this way, one delays until actually required in the proof the choice and use
of any particular enhancement $g lt.tilde t_f$. This theory based on the
companion is the one at use in the Coq formalization of this thesis. However,
since I started writing the formalization, an even more practical solution 
emerged: Steven Schäfer and Gert Smolka's _tower induction_~#mcite(<SchaferS17>).
Although it has been merged into coq-coinduction, I did not have the time to
port my Coq development to the new version. I will nonetheless present it
here and use it in the rest of the thesis.

Tower induction rests upon the inductive definition of the tower predicate,
whose elements can be understood as all the transfinite iterations of $f$,
starting from $top$.

#definition[Tower][
  Given a complete lattice $X$ and a monotone endo-map $f cl X -> X$, the
  _$f$-tower_ is an inductive predicate defined as follows.

  $ kw.dat th tower.t_f cl X -> base.Prop kw.whr \
    quad tower.tb th {x} cl tower.t_f th x -> tower.t_f th (f th x) \
    quad tower.tinf th {P} cl P subset.eq tower.t_f -> tower.t_f th (and.big P) $

  We will write $x in tower.t_f$ for $tower.t_f th x$.
] <def-tower>

#theorem[Tower Induction][
  Given a complete lattice $X$, a monotone endo-map $f cl X -> X$ and an inf-closed
  predicate $P cl X -> base.Prop$, the following principle is true.

  #inferrule(
    [$forall x in tower.t_f, P th x -> P th (f th x)$],
    [$forall x in tower.t_f, P th x$],
    suppl: tower.tind
  )
] <thm-tower-ind>
#proof[
  Assuming that $P$ is inf-closed and that the premise is valid, i.e.,

  $ K cl forall th {M} -> M subset.eq P -> P th (and.big M) \
    H cl forall th {x} -> x in tower.t_f -> P th x -> P th (f th x), $

  define the following by induction.

  $ tower.tind cl forall th {x} -> x in tower.t_f -> P th x \
    tower.tind th (tower.tb t) := H th t th (tower.tind th t) \
    tower.tind th (tower.tinf s) := K th (tower.tind compose s) $
  #v(-2em)
]

#lemma[Tower Properties][
  Given a complete lattice $X$ and a monotone endo-map $f cl X -> X$,
  for all $x in tower.t_f$ the following statements are true.

  1. $f th x lt.tilde x$
  2. $forall th y -> y lt.tilde f th y -> y lt.tilde x$ 
] <lem-tower-props>
#proof[Both by direct tower induction on the statement.]

#theorem[Tower Fixpoint][
  Given a complete lattice $X$ and a monotone endo-map $f cl X -> X$, pose
  $tower.nu f := and.big tower.t_f$.
  The following statements are true:
  1. $tower.nu f in tower.t_f$
  2. $tower.nu f approx f th (tower.nu f)$,
  3. for all $x$, if $x lt.tilde f th x$, then $x lt.tilde tower.nu f$.
] <lem-tower-fix>
#proof[
  1. By $tower.tinf th (lambda t. th t)$.
  2. By antisymmetry. First, $nu f$ is a pre-fixed point by 1. and @lem-tower-props.
     Second, by $tower.tb$ and 1., we have $f th (tower.nu f) in tower.t_f$, hence by
     infimum property, $nu f lt.tilde f th (nu f)$.
  3. By 1. and @lem-tower-props.
  #v(-2em)
]

And this is it! I really want to stress the fact that this is the entirety of the
mathematical content of this theory of coinduction, and yet it
provides an exceedingly versatile and easy to use theorem. It is easily shown
to subsume the tools provided by the companion construction and by parametrized
coinduction~#mcite(<HurNDV13>). The coq-coinduction library follows-up with
some helpers for deriving inf-closedness of predicates, the definition of the
most useful instances of complete lattices and some generic duality and
symmetry arguments. Schäfer and Smolka~#mcite(<SchaferS17>) follow-up by
deriving the companion and then provide a case study on strong bisimilarity in
the Calculus of Communicating Processes (CCS).

=== Strong Bisimilarity

#peio[intro nulle, citer @Levy11]
Equipped with this new construction of coinductive fixpoints we will apply them, in the
complete lattice of relations. Bisimilarity (both strong and weak), are typically built
on non-indexed automata, which moreover do not have _outputs_. As such they consist of
a single relation, on such automata. As our automata (indexed interaction trees,
@def-itree) are indexed and moreover have an output, our bisimilarity notions will
instead take the form of family-relation transformers. More precisely, in this section
our goal is, given a family-relation $R^rel.r$ on outputs $R^1, R^2$ of type

$ R^rel.r cl forall th {i} -> R^1 th i -> R^2 th i -> base.Prop, $

to capture strong bisimilarity as

$ ar iteq(R^rel.r) ar cl
  forall th {i} -> itree.t_Sigma th R^1 th i
                -> itree.t_Sigma th R^2 th i
                -> base.Prop. $

We start with some preliminary notations for our indexed relations.

#definition[Family Relation][
  Given $I cl base.Set$ and two families $X, Y cl base.Set^I$, the set of
  _family relations between $X$ and $Y$_ is defined as follows.

  $ rel.irel th X th Y := forall th {i} -> X th i -> Y th i -> base.Prop $

  We define the standard operators of diagonal, converse and sequential composition
  on family relations.

  #mathpar(spacing: 2em, block: false, inset: 0.5em,
    [$ & rel.diagS cl rel.irel th X th X \
       & rel.diagS th a th b := a = b $],
    [$ & ar^rel.revS cl rel.irel th X th Y -> rel.irel th Y th X \
       & R^rel.revS th a th b := R th b th a $],
    [$ & ar rel.seqS ar cl rel.irel th X th Y -> rel.irel th Y th Z -> rel.irel th X th Z \
       & (R rel.seqS S) th a th c := exists th b, R th a th b and S th b th c $]
  )
]

#definition[Family Equivalence][
  Given $R cl rel.irel th X th X$ the following
  statements are taken as definitions.
  - _$R$ is reflexive_ whenever $rel.diagS lt.tilde R$.
  - _$R$ is symmetric_ whenever $R^rel.revS lt.tilde R$.
  - _$R$ is transitive_ whenever $R rel.seqS R lt.tilde R$.
  - _$R$ is an equivalence_ whenever all the above is true.
]

As these indexed relations are quite a mouthful, the following definition will
be quite heavy in symbols. However, it is important to stress that it is
entirely straightforward. Indeed, it follows more or less directly from
a relational interpretation of type theory.

#definition[Action Relator][
  Given $Sigma cl icont.t th I$, an output relation $R^rel.r cl rel.irel th R^1
  th R^2$, and a parameter relation $X^rel.r cl rel.irel th X^1 th X^2$, the
  _action relator over $Sigma$_ of type

  $ itree.RS th R^rel.r th X^rel.r
      cl rel.irel th (itree.F_Sigma th R^1 th X^1) th (itree.F_Sigma th R^1 th X^2) $

  is defined by the following data type.

  $ kw.dat itree.RS th R^rel.r th X^rel.r th {i} kw.whr \
    quad itree.retR {r^1 th r^2} th (r^rel.r cl R^rel.r th r^1 th r^2)
      cl itree.RS th R^rel.r th X^rel.r th (itree.retF th r^1) (itree.retF th r^2) \
    quad itree.tauR {t^1 th t^2} th (t^rel.r cl X^rel.r th t^1 th t^2)
      cl itree.RS th R^rel.r th X^rel.r th (itree.tauF th t^1) (itree.tauF th t^2) \
    quad itree.visR
      th {q th k^1 th k^2} th (k^rel.r cl (r cl Sigma .icont.rsp th q) -> X^rel.r th (k^1 th r) (k^2 th r)) \
      quad quad cl itree.RS th R^rel.r th X^rel.r th (itree.visF th q th k^1) (itree.visF th q th k^2) $
]

#lemma[
  #peio[ref relator, also @Levy11]
  All the following statements are true (understood as universally quantified).

  #let xx = [$R^rel.r$]
  #let yy = [$X^rel.r$]

  $ rel.diagS
      & lt.tilde itree.RS th rel.diagS th rel.diagS \
    (itree.RS th R^rel.r th X^rel.r)^rel.revS 
      & lt.tilde itree.RS th xx^rel.revS th yy^rel.revS \
    itree.RS th R^rel.r_1 th X^rel.r_1 rel.seqS itree.RS th R^rel.r_2 th X^rel.r_2
      & lt.tilde itree.RS th (R^rel.r_1 rel.seqS R^rel.r_2) th (X^rel.r_1 rel.seqS X^rel.r_2) $

  Moreover $itree.RS$ is monotone in both arguments.
] <lem-actrel-props>
#proof[By direct case analysis.]

#definition[Interaction Relation Lattice][
  Given $Sigma cl icont.t th I$, we define the _interaction relation lattice over $Sigma$_ as follows.

  $rel.lat_Sigma := forall th {R^1 th R^2} -> rel.irel th R^1 th R^2 -> rel.irel th (itree.t_Sigma th R^1) th (itree.t_Sigma th R^2))$

  It is ultimately a set of dependent functions into $base.Prop$, as such it
  forms a complete lattice by pointwise lifting of the structure on
  $base.Prop$.
]

#definition[Strong Bisimilarity][
  Given $Sigma cl icont.t th I$, we define the _strong bisimulation map over
  $Sigma$_ as the following monotone endo-map on the interaction lattice over $Sigma$.

  $ itree.sb_Sigma cl rel.lat_Sigma -> rel.lat_Sigma \
    itree.sb_Sigma th x th R^rel.r th t^1 th t^2 := \
      quad itree.RS th R^rel.r th (x th R^rel.r) th (t^1 .itree.obs) th (t^2 .itree.obs) $

  We define heterogeneous and homogeneous _strong bisimilarity_ as follows.

  $ a iteq(R^rel.r) b := tower.nu th itree.sb_Sigma th R^rel.r th a th b \
    a de(approx.eq) b := a iteq(rel.diagS) b $
]

#lemma[
  Given $Sigma cl icont.t th I$, for all $x in tower.t_(itree.sb_Sigma)$, the
  following statements are true.

  #let xx = [$R^rel.r$]

  $ R^rel.r_1 lt.tilde R^rel.r_2 -> x th R^rel.r_1 & lt.tilde x th R^rel.r_2 \
    rel.diagS & lt.tilde x th rel.diagS \
    (x th R^rel.r)^rel.revS & lt.tilde x th xx^rel.revS \
    x th R^rel.r_1 rel.seqS x th R^rel.r_2 & lt.tilde x th (R^rel.r_1 rel.seqS R^rel.r_2) $

  As a consequence, when $R^rel.r cl rel.irel th X th X$ is an equivalence relation,
  $x th R^rel.r$ is an equivalence relation. In particular the strong
  bisimilarity $de(approx.eq)$ is an equivalence relation.
] <lem-sbisim-props>
#proof[
  All the statements are proven by direct tower induction, applying the corresponding
  statement from @lem-actrel-props.

  For example for the first one, pose $P th x$ to be the goal, i.e.,

  $ P th x := & forall th {R^1 th R^2} th {R^rel.r_1 th R^rel.r_2 cl rel.irel th R^1 th R^2} \
              & -> R^rel.r_1 lt.tilde R^rel.r_2 -> x th R^rel.r_1 lt.tilde x th R^rel.r_2. $ 

  $P$ is inf-closed. Moreover, the premise of tower induction requires that

  $ P th x -> P th (itree.sb_Sigma th x), $

  i.e., introducing all arguments of the implication we need to prove
  #inferrule(
    (
      [$forall th {X^1 th X^2} th {R^rel.r_1 th R^rel.r_2}
        -> R^rel.r_1 lt.tilde R^rel.r_2
        -> x th R^rel.r_1 lt.tilde x th R^rel.r_2$],
      [$R^rel.r_1 lt.tilde R^rel.r_2$],
      [$itree.RS th R^rel.r_1 th (x th R^rel.r_1) th (t_1 .itree.obs) th (t_2 .itree.obs)$]
    ),
    [$itree.RS th R^rel.r_2 th (x th R^rel.r_2) th (t_1 .itree.obs) th (t_2 .itree.obs)$],
    suppl: ","
  )

  which follows by direct application of the fact that #itree.RS is monotone in
  both arguments (@lem-actrel-props).
]

This concludes for strong bisimilarity: we have defined it and proved by
@lem-sbisim-props the most important properties, namely that when $R^rel.r$ is
well-behaved, not only it is an equivalence relation, but bisimulation proofs
can work up-to reflexivity, symmetry and transitivity.

=== Weak Bisimilarity

As hinted previously, we wish to characterize a second notion of bisimilarity, which
would gloss over the precise number of silent #itree.tauF moves of the two interaction trees. While
strong bisimilarity will play the role of (extensional) equality between trees, that is,
a technical tool, weak bisimilarity will play the role of a semantic equivalence.

To define weak bisimilarity, we will follow a similar route to strong bisimilarity, 
reusing the action relator, but when defining the monotone endo-map, we will insert
a gagdet, allowing to skip over a finite number of silent moves. Let us define this
gadget. For readability, we will define a shorthand for trees where the top layer of
actions has been exposed:

$ itree.tp_Sigma th R := itree.F_Sigma th R th (itree.t_Sigma th R) $

#definition[Eating Relation][
  Given $Sigma cl icont.t th I$ and $R cl base.Set^I$, define the _eating relation_
  $itree.eat_Sigma^R cl rel.irel th (itree.tp_Sigma th R) th (itree.tp_Sigma th R)$ as follows.

  $ kw.dat th itree.eat_Sigma^R th {i} := \
    quad itree.eatR th {t} cl itree.eat_Sigma^R th t th t \
    quad itree.eatS th {t_1 th t_2} cl itree.eat_Sigma^R th (t_1 .itree.obs) th t_2
         -> itree.eat_Sigma^R th (itree.tauF th t_1) th t_2 $

  We define the following shorthands:
  #let xx = $itree.eat_Sigma^R$
  $ itree.eatlr th := xx \
    itree.eatrl th := xx^rel.revS $
]

#lemma[
  For all $Sigma$ and $R$, the eating relation $itree.eat_Sigma^R$ is reflexive and
  transitive.
]
#proof[By direct induction.]

#definition[Weak Bisimilarity][
  Given $Sigma cl icont.t th I$, we define the _weak bisimulation map over
  $Sigma$_ as the following monotone endo-map on the interaction lattice over $Sigma$.

  #let xx = [$itree.eat_Sigma^R$]

  $ itree.wb_Sigma cl rel.lat_Sigma -> rel.lat_Sigma \
    itree.wb_Sigma th x th R^rel.r th t^1 th t^2 := \
      quad (cnorm(itree.eatlr) rel.seqS itree.RS th R^rel.r th (x th R^rel.r)
            rel.seqS cnorm(itree.eatrl)) th (t^1 .itree.obs) th (t^2 .itree.obs) $

  We define heterogeneous and homogeneous _weak bisimilarity_ as follows.

  $ a itweq(R^rel.r) b := tower.nu th itree.wb_Sigma th R^rel.r th a th b \
    a de(approx) b := a itweq(rel.diagS) b $
]

#lemma[
  Given $Sigma cl icont.t th I$, for all $x in tower.t_(itree.wb_Sigma)$, the
  following statements are true.

  #let xx = [$R^rel.r$]

  $ R^rel.r_1 lt.tilde R^rel.r_2 -> x th R^rel.r_1 & lt.tilde x th R^rel.r_2 \
    rel.diagS & lt.tilde x th rel.diagS \
    (x th R^rel.r)^rel.revS & lt.tilde x th xx^rel.revS $

  In particular the weak bisimilarity $de(approx)$ is reflexive and symmetric.
] <lem-wbisim-props>
#proof[
  By direct tower induction, as for @lem-sbisim-props.
]

Notice that in the previous lemma we have left out the statement regarding
sequential composition of relations. Indeed it is well-known that weak bisimulation
proofs up-to transitivity is not valid. However we would still like to prove weak
bisimilarity transitive!

#lemma[
  Given $Sigma cl icont.t th I$ and $R^rel.r cl rel.irel th R th R$, if $R$ is transitive,
  then so is $itweq(R^rel.r)$.
]
#proof[
  Pose the following shorthands, respectively for the "one
  step sychnronization then weak bisimilarity" and for the one step unfolding of weak
  bisimilarity.

  #let sync = de(crel(math.attach(sym.approx, tr: "s")))
  #let weak = de(crel(math.attach(sym.approx, tr: "w")))
  #let eat = itree.eatlr
  #let eatr = itree.eatrl

  $ sync "" & := itree.RS th R^rel.r th itweq(R^rel.r) \
    weak "" & := cnorm(eat) rel.seqS cnorm(sync) rel.seqS cnorm(eatr) $

  Prove the following statements by direct induction on the eating relation for all $a, b, c$.

  1. $a eat itree.tauF th b sync c -> a sync c$
  2. $ a sync itree.tauF th b eatr c -> a sync c$

  Observe that the following statements are true by case analysis.

  3. $itree.tauF th a weak b -> a .itree.obs weak b$
  4. $a weak itree.tauF b -> a weak b .itree.obs$

  Using 3. and 4. and transitivity of the eating relation, prove the following statements by induction.

  5. $a crel((weak rel.seqS eat)) itree.retF th r -> a crel((eat rel.seqS sync)) itree.retF r$
  6. $a crel((weak rel.seqS eat)) itree.visF th q th k -> a crel((eat rel.seqS sync)) itree.visF th q th k$
  7. $itree.retF th r crel((eatr rel.seqS weak)) b -> itree.retF th r crel((sync rel.seqS eatr)) b$
  8. $itree.visF th q th k crel((eatr rel.seqS weak)) b -> itree.visF th q th k crel((sync rel.seqS eatr)) b$

  Finally, note that the following is true by (nested) induction.

  9. $a crel((eatr rel.seqS eat)) b -> a eat b or a eatr b$

  Finally, we prove transitivity of $itweq(R^rel.r)$ by tower induction on

  $ P th x := cnorm(itweq(R^rel.r)) rel.seqS cnorm(itweq(R^rel.r)) lt.tilde x th R^rel.r. $

  $P$ is inf-closed. Assuming $P th x$, let us prove $P th (itree.wb_Sigma th x)$, i.e.,

  $ cnorm(itweq(R^rel.r)) rel.seqS cnorm(itweq(R^rel.r)) th th lt.tilde th th itree.wb_Sigma th x th R^rel.r $

  By one step unfolding, it suffices to prove the following.

  $ cnorm(weak) rel.seqS cnorm(weak)
    th th lt.tilde th th
    cnorm(eat) rel.seqS itree.RS th R^rel.r th (x th R^rel.r) rel.seqS cnorm(eatr) $

  Introducing and decomposing the hypotheses, we obtain the following:

  $ a eat x_1 sync x_2 eatr b eat y_1 sync y_2 eatr c $

  Apply 9. between $x_2$ and $y_1$. Assume that the left case is true,
  i.e., $x_2 eat y_1$ (for the right case, swap applications of 5. and 6. with
  corresponding applications of 7. and 8.). By case on $y_1$.

  - When $y_1 = itree.retF th r$,

    $ & a & eat x_1 & sync x_2 &          & eat itree.retF th r & sync y_2 eatr c & \
    & a & eat x_1 & sync x_2 & eatr x_2 & eat itree.retF th r & sync y_2 eatr c & quad "by refl." \
    & a &         & weak     &      x_2 & eat itree.retF th r & sync y_2 eatr c & quad "by def." \
    & a &         & eat      &      x_3 & sync itree.retF th r & sync y_2 eatr c & quad "by 5." \
  $

    By concatenation (@lem-actrel-props) between $x_3$ and $y_2$, we obtain 

    $ itree.RS th (R^rel.r rel.seqS R^rel.r) th (cnorm(itweq(R^rel.r)) rel.seqS
    cnorm(itweq(R^rel.r))) th x_3 th y_2. $

    By transitivity, $R^rel.r rel.seqS R^rel.r lt.tilde R^rel.r$. Using this
    and the coinduction hypothesis $P th x$, by monotonicity
    (@lem-actrel-props) we obtain the following and conclude.

    $ itree.RS th R^rel.r th (x th R^rel.r) th x_3 th y_2. $

  - When $y_1 = itree.visF th q th k$, the reasoning is the same, swapping
    lemma 5. by lemma 6.
  - When $y_1 = itree.tauF th t$,

    $ & a & eat x_1 & sync x_2 & eat itree.tauF th t & sync y_2 eatr c & \
      & a & eat x_1 & sync x_2 &                     & sync y_2 eatr c & quad "by 1." \
    $

    By @lem-actrel-props, using concatenation between $x_2$ and $y_2$, we obtain 

    $ itree.RS th (R^rel.r rel.seqS R^rel.r) th (cnorm(itweq(R^rel.r)) rel.seqS
      cnorm(itweq(R^rel.r))) th x_3 th y_2, $

    we then conclude as before by transitivity of $R^rel.r$ and coinduction hypothesis.
    #v(-2em) // BUG?
]

#lemma[Up-to strong bisimilarity][
  Given $Sigma cl icont.t th I$ and $R^rel.r cl rel.irel th R th R$, if $R$ is transitive,
  for all $x in tower.t_(itree.wb_Sigma)$,

  $ cnorm(iteq(R^rel.r)) rel.seqS x th R^rel.r rel.seqS cnorm(iteq(R^rel.r))
    lt.tilde x th R^rel.r $
]
#proof[
  #let strong = de(crel(math.attach(sym.approx.eq, tr: "s")))
  #let sync = crel(math.attach(de(sym.approx), tr: de("s"), br: "x"))
  #let weak = crel(math.attach(de(sym.approx), tr: de("w"), br: "x"))
  #let eat = itree.eatlr
  #let eatr = itree.eatrl

  Let us define the following shorthand.

  $ "" strong "" & := itree.RS th R^rel.r th iteq(R^rel.r) \
    "" sync "" & := itree.RS th R^rel.r th (x th R^rel.r) \
    "" weak "" & := cnorm(eat) rel.seqS cnorm(sync) rel.seqS cnorm(eatr) $

  Prove the following statements by direct induction.

  1. $a crel((strong rel.seqS eat)) b -> a crel((eat rel.seqS strong)) b $
  2. $a crel((eatr rel.seqS strong)) b -> a crel((strong rel.seqS eatr)) b $

  Then, let us prove the goal by tower induction on

  $ P th x := cnorm(iteq(R^rel.r)) rel.seqS x th R^rel.r rel.seqS cnorm(iteq(R^rel.r))
    lt.tilde x th R^rel.r. $

  $P$ is inf-closed. Assuming $P th x$, let us prove $P th (itree.wb_Sigma th x)$, i.e.,

  $ cnorm(iteq(R^rel.r)) rel.seqS itree.wb_Sigma th x th R^rel.r rel.seqS cnorm(iteq(R^rel.r))
    lt.tilde itree.wb_Sigma th x th R^rel.r. $

  By one-step unfolding it suffices to prove the following.

  $ cnorm(strong) rel.seqS cnorm(weak) rel.seqS cnorm(strong) lt.tilde cnorm(weak) $

  Introducing and destructing the hypotheses we proceed as follows.

  $ a & strong b & eat x_1    & sync x_2 & eatr c     & strong d & \
    a & eat y_1  & strong x_1 & sync x_2 & strong y_2 & eatr d   & quad "by 1. and 2." $

  By concatenation (@lem-actrel-props) between $y_1$ and $y_2$, we obtain 

  $ itree.RS th (R^rel.r rel.seqS R^rel.r rel.seqS R^rel.r)
      th (cnorm(iteq(R^rel.r)) rel.seqS x th R^rel.r rel.seqS cnorm(iteq(R^rel.r)))
      th y_1 th y_2. $

  By transitivity of $R^rel.r$, $P th x$ and monotonicity (@lem-actrel-props)
  we deduce $itree.RS th R^rel.r th (x th R^rel.r) th y_1 th y_2$ and conclude.
]

This sequence of juggling concludes our core properties for weak bisimilarity:
we know that for well-behaved $R^rel.r$ it is an equivalence relation and that
it supports coinductive proofs up-to reflexivity, up-to symmetry and up-to
strong bisimilarity.

== Monad Structure

An important structure available on interaction trees is that they form a
monad. Indeed as they are parametrized by an _output_ family $R$, a strategy
with output $R$ can be considered as an impure computation returning some $R$.
Its _effects_ will be to perform game moves and wait for an answer. While at
first sight---considering only the goal of representing game strategies---such
an output might seem unnecessary, the compositionality offered by monads, that
is, sequential composition, is tremendously useful to construct and reason on
strategies piecewise.

The monad structure on interaction trees takes place in the family category
$base.Set^I$ and its laws will hold both w.r.t. strong bisimilarity and weak
bisimilarity. One way to view this is to say that I will define _two_ monads.
However, in line with my choice of using intensional type theory, I will first
define a _pre-monad_ structure, containing only the computationally relevant
operation and then provide two sets of laws.

In fact in @def-itree, we have already defined the "return" operator, $itree.ret$,
which can be typed as follows.

$ itree.ret th {X} cl X => itree.t_Sigma th X $

Let us define the "bind" operator, which works by tree grafting.

#definition[Interaction Tree Bind][
  #margin-note[
    Note that defining $itree.subst_f$ _with $f$ fixed_ is not a
    mere stylistic consideration. Indeed, what it achieves, is to pull the
    binder for $f$ out
    of the coinductive definition. This enables the syntactic guardedness
    checker to more easily understand subsequent coinductive definition making
    use of the bind operator. To the best of my knowledge, this trick was first
    used in the InteractionTree library~#num-cite(<XiaZHHMPZ20>). In general, it
    is always fruitful to take as many binders as possible out of the cofixpoint
    definition.
  ]
  Let $Sigma cl icont.t th I$. Given $X, Y cl base.Set^I$ and $f cl X => itree.t_Sigma th Y$,
  define _interaction tree substitution_ as follows.
  $ itree.subst_f cl itree.t_Sigma th X => itree.t_Sigma th Y \
    (itree.subst_f th t) .itree.obs kw.wit t .itree.obs \
    quad | itree.retF th x := (k th x) .itree.obs \
    quad | itree.tauF th t := itree.tauF th (itree.subst_f th t) \
    quad | itree.visF th q th k := itree.visF th q th (lambda th r. th itree.subst_f th (k th r)) $

  Then, define the _interaction tree bind_ operator as

  $ ar itree.bind ar th {X th Y th i} cl itree.t_Sigma th X th i -> (X => itree.t_Sigma th Y) -> itree.t_Sigma th Y th i \
    t itree.bind f := itree.subst_f th t $
]

Before proving the monad laws, we will first prove that our operators respect
both strong and weak bisimilarity, in other words that they are _monotone_. For
strong bisimilarity and $itree.ret$, the statement is the following.

$ forall th {X^rel.r cl rel.irel th X^1 th X^2} th {i cl I} th {x_1 cl X^1 th i} th {x_2 cl X^1 th i} \
  quad -> X^rel.r th x_1 th x_2 -> itree.ret th x_1 iteq(X^rel.r) itree.ret th x_2 $

This is quite heavy, and many more complex monotonicity statements will appear
in the thesis. As such from now on we will extensively use relational
combinators. To simplify reading such complex relations we will write $a
xrel(R) b$ for $R th a th b$. Our final goal is to write something such as follows.

$ forall th {X^rel.r} -> itree.ret xrel(X^rel.r rel.iarr cnorm(iteq(X^rel.r))) itree.ret $

To achieve this, define the following combinators.

$ ar rel.arr ar cl rel.rel th X_1 th X_2 -> rel.rel th Y_1 th Y_2 -> rel.rel th (X_1 -> Y_1) th (X_2 -> Y_2) \
  (R rel.arr S) th f th g := forall th {x_1 x_2} -> R th x_1 th x_2 -> S th (f th x_1) th (g th x_2) $

$ ar rel.iarr ar cl rel.irel th X_1 th X_2 -> rel.irel th Y_1 th Y_2 -> rel.irel th (X_1 => Y_1) th (X_2 => Y_2) \
  (R rel.iarr S) th f th g := forall th {x_1 x_2} -> R th x_1 th x_2 -> S th (f th x_1) th (g th x_2) $

$ rel.forall cl (forall th {i} -> rel.rel th (X_1 th i) th (X_2 th i)) -> rel.rel th (forall th {i} -> X_1 th i) th (forall th {i} -> X_2 th i) \
  (rel.forall th R) th f th g := forall th {i} -> R th (f th {i}) th (g th {i}) $

Moreover we will write $rel.forall th A$ for $rel.forall th (lambda th {i}. th A)$.

#lemma[ITree Monad Monotonicity][
  Given $Sigma cl itree.t_Sigma$, for any $X^rel.r$ and $Y^rel.r$ and for any $x cl rel.lat_Sigma$
  such that either $x in itree.sb_Sigma$ or $x in itree.wb_Sigma$, the following statements are true.

  1. $itree.ret xrel(X^rel.r rel.arr x th X^rel.r) itree.ret$
  2. $(ar itree.bind ar) xrel(rel.forall th x th X^rel.r rel.arr (X^rel.r rel.iarr x th Y^rel.r) rel.arr x th Y^rel.r) (ar itree.bind ar)$

  As a consequence, return and bind respect both strong and weak bisimilarity:
  3. $itree.ret xrel(X^rel.r rel.arr cnorm(iteq(X^rel.r))) itree.ret$
  4. $itree.ret xrel(X^rel.r rel.arr cnorm(itweq(X^rel.r))) itree.ret$
  5. $(ar itree.bind ar) xrel(rel.forall th cnorm(iteq(X^rel.r)) rel.arr (X^rel.r rel.iarr cnorm(iteq(Y^rel.r))) rel.arr cnorm(iteq(Y^rel.r))) (ar itree.bind ar)$
  6. $(ar itree.bind ar) xrel(rel.forall th cnorm(itweq(X^rel.r)) rel.arr (X^rel.r rel.iarr cnorm(itweq(Y^rel.r))) rel.arr cnorm(itweq(Y^rel.r))) (ar itree.bind ar)$
]
#proof[
  1. Assuming $X^rel.r th x_1 th x_2$, observe that $itree.sb_Sigma th x th
     X^rel.r th (itree.ret th x_1) th (itree.ret th x_2)$, which by @lem-tower-props
     implies $x th X^rel.r th (itree.ret th x_1) th (itree.ret th x_2)$. It is
     similarly for $x in itree.wb_Sigma$, using reflexivity of $itree.eat_Sigma^(R^rel.r)$.
  2. By tower induction on the statement. For $x in itree.sb_Sigma$ it is direct
     by unfolding and dependent pattern matching.
     For $x in itree.wb_Sigma$, use the following fact.
     $ t_1 itree.eatlr t_2 -> (t_1 itree.bind f) itree.eatlr (t_2 itree.bind f) $
  3--6. By direct application of 1--2, using @lem-tower-fix.
]

While perhaps not very impressive, the last lemma is very important. Points
3--6 prove that return and bind are well-defined as operators on the setoids of
strongly- and weakly-bisimilar strategies. But more importantly, point 2. it
also proves that during a coinductive proof, to relate two sequential compositions
one can first relate the prefixes and then, pointwise, the continuations. This
fact is sometimes called "bisimulation up-to bind".

#lemma[ITree Monad Laws][
  Given $Sigma cl itree.t_Sigma$, for all $x cl X th i$, $t cl itree.t_Sigma th
  X th i$, $f cl X => itree.t_Sigma th Y$ and $g cl Y => itree.t_Sigma th Z$
  the following statements are true.

  1. $(itree.ret th x itree.bind f) itree.eq f th x$
  2. $(t itree.bind itree.ret) itree.eq t$
  3. $(t itree.bind f) itree.bind g itree.eq t itree.bind (f itree.kbind g)$
]
#proof[
  1. By one-step unfolding.
  2. By direct tower induction.
  3. By direct tower induction.
  #v(-2em)
]

This concludes the monadic theory of interaction trees. We will make some use of the
so-called "do notation", to write, e.g.,

$ kw.do x <- t; th y <- f th x; th g th y $

instead of

$ t itree.bind (lambda th x. th f th x itree.bind (lambda th y. th g th y)) $

To make the best out of this syntax, we define some "generic effects", i.e. helpers
to perform a silent step or play a move.

#definition[Generic Effects][
  Given $Sigma cl icont.t th I$, we define the following generic effects.

  $ itree.gtau th {i} cl itree.t_Sigma th (lambda th i . th base.unit) th i \
    itree.gtau := itree.tau th (itree.ret th base.tt) $

  $ itree.gvis th {i} th (q cl Sigma .icont.qry th i) cl itree.t_Sigma th (subs.fiber th (Sigma .icont.nxt th {q})) th i \
    itree.gvis th q := itree.vis th q th (lambda th r. th itree.ret th (subs.fib th r)) $
  #margin-note(dy: -4em)[
    While slightly funky, the type of $itree.gvis$ is quite notable: it is
    the type of what Xia et. al~#num-cite(<XiaZHHMPZ20>) call _event handlers_.
    It encodes a natural transformation of $[| Sigma |]$ into $itree.t_Sigma$. This one
    in particular is the identity handler, part of a larger
    structure making $itree.t$ a relative monad~#num-cite(<AltenkirchCU10>)
    on $icont.t th I -> (base.Set^I -> base.Set^I)$. Alas, its definition is
    irrelevant to OGS correction and does not fit into this margin...
  ]
  $subs.fiber$ is defined by the following data type.

  $ kw.dat th subs.fiber th (f cl A -> B) cl B -> base.Set kw.whr \
    quad subs.fib th (x cl A) cl subs.fiber th f th (f th x) $
]


== Iteration Operators <sec-iter>

=== Fixed points of Equations

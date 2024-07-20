#import "/lib/all.typ": *

= Coinductive Game Strategies

As we have seen, Operational Game Semantics, and more generally interactive
semantics, rest upon a dialogue following particular rules, a so-called two
player game. The main task in this chapter is to properly define what is
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
the other hand, in game semantics, the traditional approach is more extensional.
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
computation, interacting with its environment by means of uninterpreted
events. Recognizing "programs" as Player strategies, "environments" as yet
unknown Opponent strategies and "uninterpreted events" as move exchanges, we
are quite close to our setting of alternating two player games. However, there
are two remaining obstactles in order to apply interaction trees to our
use case.

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

Happily, both of these points can be resolved by swapping the notion
of event from interaction trees, with the notion of game introduced by
Paul Levy and Sam Staton~#mcite(<LevyS14>). The rest of the chapter is
organized as follows.

- In @sec-levy-staton, I reconstruct Paul Levy and Sam Staton's notion of
  game and of coalgebraic transition system.
- In @sec-itree, I introduce _indexed interaction trees_, a novel generalization of
  interaction trees adapted to the above notion of games. I introduce the
  definition of their bisimilarity and their general theory, lifted from the
  non-indexed setting.
- In @sec-iter, I develop upon the theory of iteration operators, providing a
  novel _eventually guarded iteration_, applicable to the delay
  monad~#mcite(<Capretta05>), but also to indexed and non-indexed interaction
  trees.

== Levy & Staton Games <sec-levy-staton>

=== An Intuitive Reconstruction

The definition of game obtained by Levy & Staton in
#mcite(<LevyS14>) arises quite naturally from what is intuitively understood by
a "game". Let's build it up first hand.

In the common sense of the word, a game is described by the moves
allowed at any point of the play, together with winning conditions and
their associated rewards. As I am here only interested in games
insofar as they provide a framework for structured interactions, usual
notions from classical game theory such as "winning", "reward" or
"optimal play" will be completely absent. Moreover, I will restrict
attention to games where two agents play in alternating turns. Thus,
for my purpose, games will just consist of the description of allowed
moves.#margin-note[Games in such a retricted view---two-player,
alternating, no notion of winning---are similar to combinatorial games
and might perhaps be more appropriately named _protocols_, as
typically arises in the field of computer networks.]

Starting from the idea that a game is described by the moves allowed for each
player, arguably the simplest formalization is to say that a game consists
of a pair $(M^+, M^-)$ of sets, encoding the set of moves allowed for each
player. For example, taking $M^+$ and $M^-$ to be both equal to the set of UTF-8
character strings, we can think of this as the "game of chatting" where the two
players are to alternatively exchange text messages. This definition readily
encodes simple kinds of interactions: at a coarse level we could argue that a
lot of low-level protocols consist in two players alternatively exchanging byte
sequences. However, games-as-set-pairs are very restrictive in the sense that
any move from, say, $M^+$ is valid at any point where it is the first player's
turn. Thus, games-as-set-pairs are missing a shared game state, a game
_position_, something enabling the set of allowed moves to evolve over the
course of the dialogue. In particular, our game of interest, Operational Game
Semantics, makes use of such evolution of moves: since players introduce
variables while playing, moves mentioning some variable $x$ should only be
allowed after $x$ has been introduced. 

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

In order to make (half-)games into a proper category, we will define their
morphisms. As games are parametrized over sets of positions, game morphisms
could be naturally defined as parametrized over position morphisms, in the
displayed style of Benedikt Ahrens and Peter Lumsdaine~#mcite(<AhrensL19>),
#tom[Normalement ça se fait pas trop de donner les prénoms, et chuis un peu
d'accord que ça devient vite lourd.] but I will resist the urge to dive too
deeply into the structure of games and leave most of it for further work to
expose. Indeed, we will require none of it for our main goal of proving
correctness of OGS. Moreover, as already noted by Pierre-Évariste Dagand and
Conor McBride~#mcite(<DagandM13>, supplement: "Sec. 1.3") in the similar setting
of indexed containers, describing the extremely rich structures at play requires
advanced concepts, such as framed bicategories and two-sided fibrations.

#peio["simulation" vs "morphism"?]

#definition[Half-Game Simulation][
  Given two half-games $A, B cl game.hg th I th J$, a _half-game simulation
  from $A$ to $B$_ is given by the following record.

#tom[by a record of the following type (partout...)?]
  

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

#remark[Half-Game is Functorial][ $game.hg$ extends to a strict functor
  $base.Set^"op" times base.Set -> base.Cat$ as witnessed by the following
  action on morphisms, presented in curried form and written in infix notation.

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
_combinatorial games_~#mcite(<Conway76>)#peio[check def there] and may in fact
be considered their prime definition. I will explain how they are an instance of
our notion. We will use the following coinductive, exceedingly simple
definition: a Conway game $G cl conway.t$ is given by two subsets of Conway
games $G_L, G_R subset.eq conway.t$. The left subset $G_L$ is to be thought of
as the set of games reachable by the left player in one move, and symmetrically
for $G_R$.

#margin-note[For a more in-depth discussion of the two notions of subsets in
    type theory, see #text-cite(<HancockH06>, supplement: [pp. 194--198])]
In order to translate this definition into type theory, the only
question is how to represent subsets.
The most familiar one is the powerset construction, adopting the point-of-view
of subsets as predicates:

$ subs.Pow cl base.Set -> base.Set \
  subs.Pow th X kw.whr X -> base.Prop $

However there is another, more intensional one, viewing subsets as families:

#tom[Proof-relevant plus que intentional, non?] 

#tom[Euh... et en fait je comprends pas la def... Ah si, c'est la version
fibrée! Qui l'eut cru venant de toi... Bon, bref, ça coule pas de source à cet
endroit.]

#tom[De plus, les deux defs n'étant pas équivalentes, est-ce qu'il ne vaudrait
pas mieux assumer la différence et appeler ça des proof-relevant Conway games?]

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

#example[Game of Conway Games][ We start by noticing that $I -> subs.Fam th J$
  is just a shuffling of $game.hg th I th J$:

  $ de("fam-to-hg") cl (I -> subs.Fam th J) -> game.hg th I th J \
    (de("fam-to-hg") th F) .game.mv th i := (F th i) .subs.dom \
    (de("fam-to-hg") th F) .game.nx th {i} th m := (F th i).subs.idx th m $

Furthermore, the projection maps $conway.lft$ and $conway.rgt$ have the
following type,

  $ conway.lft,conway.rgt cl conway.t -> subs.Fam th conway.t$

so that applying $de("fam-to-hg")$ yields half-games.

Then, the _game of Conway games_ can be given as follows.

  $ conway.ls cl game.g th conway.t th conway.t \
    conway.ls .game.client := de("fam-to-hg") th conway.lft \
    conway.ls .game.server := de("fam-to-hg") th conway.rgt $
]

#peio[inj LS $=>$ Conway]

#tom[Bon c'est rigolo, mais le sens de tout ça n'est pas hyper clair, si? Est-ce
que les parties au sens de Conway sont les mêmes que celles de Levy-Staton sur
$conway.ls$?]

*Applicative Bisimilarity* #sym.space #peio[applicative bisim]

*OGS Game* #sym.space #peio[ogs stlc?]

=== Strategies as Transition Systems

Following Levy & Staton~#num-cite(<LevyS14>), we now define client strategies as
 transition systems over a given game. We will only define _client_ strategies,
since _server_ strategies can be simply derived from client strategies on the
dual game---the prime benefit of our symmetric notion of game. We first need to
define two interpretations of half-games as functors.


#tom[Les espaces sont bizarres dans la def ci-dessous, non?]
#definition[Half-Game Functors][
  Given a half-game $G cl game.hg th I th J$, we define the
  _active interpretation_ and _passive interpretation of $G$_ as the functors
  $G game.extA -, G game.extP - cl base.Set^J -> base.Set^I$ defined as follows.

  $ (G game.extA X) th i := (m cl G.game.mv th i) times X th (G.game.nx th m) \
    (G game.extP X) th i := (m cl G.game.mv th i) -> X th (G.game.nx th m) $
] <def-hg-ext>

#tom[Chuis pas super fan de la notation $game.extA$, parce qu'elle ressemble
trop à $game.extP$, elle évoque aussi un adjoint à droite plus qu'à gauche.]

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
    called a _small-step system over $G$_. We can recover their
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

The $strat.play$ function takes as inputs an active position $i cl I^+$, an
active state  $s cl strat.stp th i$  over $i$ and returns one of three things:

/ a _return move_ in $R th i$:  \
  This case was not present in Levy & Staton~#num-cite(<LevyS14>), but
  it allows a strategy to end the game, provided it exhibits an output. As we
  will see in @sec-itree with interaction trees, this is crucial for
  compositional manipulation.

/ a _silent move_ in $strat.stp th i$: \
  In this case, the strategy postpones progression in the game. This case
  allows for strategies to be _partial_ in the same sense as Venanzio Capretta's
  #delay.t monad~#mcite(<Capretta05>). _Total strategies_ without this case would
  make perfect sense, but we are interested in arbitrary, hence partial, computations.

/ a _client move_ in $G.game.client game.extA strat.stn$:  \
  By @def-hg-ext, this data consists of a client move valid at the current
  position, together with a passive state over the next position. This case is
  the one which actually _chooses_ a move and sends it to a hypothetical
  opponent.

The #strat.coplay function is simpler. By @def-hg-ext, it takes a passive
position, a passive state over it, and a currently valid server move, and must
then return an active state over the next position.

== Strategies as Indexed Interaction Trees <sec-itree>

In @def-tsys, I have defined strategies similarly to Levy &
Staton~#mcite(<LevyS14>), that is, by a state-and-transition-function
presentation of automata. This representation is theoretically satisfying,
however most of the time it is painful to work with formally. As an example,
let's assume I want to define a binary combinator, taking two systems as
arguments and returning a third one. Each of these is a dependent record with
four fields, so that I have to work with eight input components to define two
families of states, and then, depending on these new states, I have to write two
suitable transition functions. This is a lot to manage! The heaviness of
explicitly constructing automata is one of the reasons why widely used
programming languages have introduced syntactic facilities like the "yield" and
"await" keywords for writing state machines. #peio[ref?]

#tom[Ça je connais pas du tout.]

In order to rectify this, we forget about states altogether. Notice that @def-tsys is
exactly the definition of a coalgebra for some endofunctor on $(I^+ -> base.Set)
times (I^- -> base.Set)$. Then, as by definition any coalgebra maps uniquely
into the final coalgebra, it is sufficient to work with this final coalgebra,
whose states intuitively consist of infinite trees, describing
the traces of any possible transition system over $G$.

#tom[Là-dessus ptet dire "modulo les questions de taille" quelque part?]

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
  #tom[Eeeeeh, je sais pas... C'est les strats où $strat.coplay$ est injective,
  c'est ça? Si oui, je dirais plutôt réflexive: si je note $S^i$ la strat
  "injective" en ce sens induite par $S$, on a plutôt un morphisme $S -> S^i$,
  qui est universel vis-à-vis des strats injectives, si je me trompe pas. Non? ]
]

$ X |-> R + X + G.game.client game.extA (G.game.server game.extP X)) $

#tom[Le truc ci-dessous s'enfonce dans une voie un peu imprévisible, donc c'est
dur à suivre. Il faudrait ptet baliser un peu mieux, dire où tu vas.]
Since in this functor nothing really depends on the server positions $I^-$, we
can play the same trick and eliminate passive positions from the
description of games, obtaining back indexed polynomial functors, or more
precisely their type-theoretic incarnation as _indexed
containers_~#mcite(<AltenkirchGHMM15>). Remember that the reason for preferring
games over indexed containers was to ease swapping client and server. But since
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
  Given an indexed container $Sigma cl icont.t th I$, we define its _extension_
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

#remark[Container to Game][ Although games include information about passive
  positions which containers do not, we can guess this information and inject
  containters into games as follows.

  $ ceil(-) cl (Sigma cl icont.t th I) -> game.g th I th ((i cl I) times Sigma .icont.qry th i) \
    ceil(Sigma) .game.client"".game.mv th i := Sigma .icont.qry th i \
    ceil(Sigma) .game.client"".game.nx th {i} th m := (i, m) \
    ceil(Sigma) .game.server"".game.mv th (i, m) := Sigma .icont.rsp th m \
    ceil(Sigma) .game.server"".game.nx th m := Sigma .icont.nxt th m $

  We observe in passing that $floor(-) compose ceil(-)$ is definitionally equal
  to the identity on containers, but not the other way around. ]

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

  $ kw.dat itree.F_Sigma th R th X th i cl base.Set kw.whr \
    quad itree.retF th (r cl R th i) \
    quad itree.tauF th (t cl X th i) \
    quad itree.visF
      th (q cl Sigma .icont.qry th i)
      th (k cl (r cl Sigma .icont.rsp th q) -> X th (Sigma .icont.nxt th r)) $
]

Being itself the extension of some indexed container, $itree.F_Sigma th R$ has a
thorougly understood theory of fixpoints~#mcite(<AltenkirchGHMM15>) and we can
form its final coalgebra as a coinductive family which is accepted by most type
theory implementations such as Agda and Coq.

#tom[Là je me rends compte que la rédaction est un poil trop linéaire à mon
goût. La def des arbres d'interation indexés est perdue au milieu d'une longue
histoire. Est-ce que tu devrais pas faire une sous-partie "coalgèbre finale /
arbres d'interaction"?] 

#definition[Indexed Interaction Tree][ Given a signature
$Sigma cl icont.t th I$ and an output $R cl I -> base.Set$, the family of
  _indexed interaction trees on $Sigma$ with output $R$_, $itree.t_Sigma th R cl
  base.Set^I$ is given by the following coinductive record.

  $ kw.rec itree.t_Sigma th R th i cl base.Set kw.whr \
    quad itree.obs cl itree.F_Sigma th R th (itree.t_Sigma th R) th i $

  Furthermore, define the following shorthands:

  $ (itree.ret th x) .itree.obs := itree.retF th x \
    (itree.tau th t) .itree.obs := itree.tauF th t \
    (itree.vis th q th k) .itree.obs := itree.visF th q th k $
] <def-itree>

#tom[pas compris les shorthands. Est-ce que tu essaies de dire que 
$itree.ret th x := { itree.obs = itree.retF t x}$, par exemple?]

Notice that this definition is to interaction trees~#mcite(<XiaZHHMPZ20>)
what inductive families are to inductive data types. As we will discover
in the remainder of this chapter, all of the monadic theory of interaction
trees lifts neatly to this newly indexed setting, an "outrageous fortune"
described by Conor McBride in #mcite(dy: 1.2em, <McBride11>).

#tom[Cette phrase devrait-elle être après la def qui suit?] Before moving on to
define bisimilarity, let us first link this definition to transition systems
over games.

#definition[Strategies][
  Given a game $G cl game.g th I^+ th I^-$ and output $R cl I^+ -> base.Set$,
  the _active strategies over $G$ with output $R$_, $game.stratA_G th R cl
  I^+ -> base.Set$ and the _passive strategies over $G$ with output $R$_,
  $game.stratP_G th R cl I^- -> base.Set$ are given as follows.

  $ game.stratA_G th R := itree.t_floor(G) th R \
    game.stratP_G th R := G.game.server game.extP game.stratA_G th R $
] <def-strat>

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

#tom[La systaxe $(itree.unrollA th s) .itree.obs th kw.wit S .strat.play th s$
m'est inconnue, et est un peu obscure, alors que pourtant ce qu'il faut faire
est clair. J'imagine laborieusement que ça veut dire $itree.unrollA th s :=
"match" S .strat.play th s "with"...$? Ça sera ptet introduit kek part?]

#tom[Et aussi, ça serait bien de rendre explicite que c'est une def
coinductive.]

== Bisimilarity

The natural notion of equality on automata is the notion bisimilarity.
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
support for coinductive records (such as @def-itree) and for cofixpoints, or
coinductive definitions (such as @def-unroll). However, these features---in
particular cofixpoints---are at times brittle, because the theory relies on a
syntactic _guardedness_ #tom[(c'est syntaxique en Agda? Ah, je vois que tu en
parles plus tard, mais en lisant ici on se demande ce qui se passe, vu que
depuis le début on fait du Coq $|$ Agda sans distinction.)] criterion to decide
whether a given definition should be accepted. For simple definitions---in fact
more precisely for computationally relevant definitions---I will indulge the
whims of syntactic guardedness. But for complex bisimilarity proofs such as
those which will appear later in this thesis, being at the mercy of a syntactic
implementation detail is a recipe for failure.

To tackle this problem, Agda provides more robust capabilities in the form of
_sized types_, for which the well-formedness criterion is based on typing.
However they are not available in Coq, the language in which this thesis has
been formalized. Moreover, in Agda's experimental tradition, while they do work
when used in the intended programming patterns, their semantics are still not
fully clear #peio[ref multi-clocked guarded TT]. We will take an entirely
different route, building coinduction for ourselves, _inside_ type theory.
Indeed, as demonstrated by Damien Pous's coq-coinduction
library~#mcite(<Pous16>, supplement: [https://github.com/damien-pous/coinduction]),
powerful coinductive constructions and reasoning principles for propositional
types are derivable in the presence of impredicativity.
#tom[Pourquoi la font de coq-coinduction est-elle si petite?]


=== Coinduction with Complete Lattices

The basis of coq-coinduction is the observation that with impredicativity,
#base.Prop forms a complete lattice. In fact, not only #base.Prop, but also
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
compose f lt.tilde f compose g$. #tom[Attention, la compatibilité n'est pas
nécessaire, si?] This eases bisimilarity proofs where, for
example, the relation between states is only preserved by the transition
functions up-to transitive closure, provided the transitive closure has been
proven compatible.

Satisfyingly, the least upper bound of all compatible functions is still
compatible. It is called the _companion_ of $f$, written $t_f$, and moreover
satisfies $t_f bot th approx nu f$. This enables working with the following
generalized principle.

#centering(inferrule(
  [$x lt.tilde f th (t_f th x)$],
  [$x lt.tilde nu f$]
))

In this way, one delays until actually required in the proof the choice and use
of any particular enhancement $g lt.tilde t_f$. This theory based on the
companion is the one used in the Coq formalization of this thesis. However,
since I started writing the formalization, an even more practical solution,
Steven Schäfer and Gert Smolka's _tower induction_~#mcite(<SchaferS17>), has
been merged into coq-coinduction. However, I did not have the time to
port my Coq development to the new version. I will nonetheless present it
here and use it in the rest of the thesis.

Tower induction rests upon the inductive definition of the tower predicate,
whose elements can be understood as all the transfinite iterations of $f$,
starting from $top$. #tom[Formulation bizarre: le tower predicate, c'est $t_f$?]

#definition[Tower][
  Given a complete lattice $X$ and a monotone endo-map $f cl X -> X$, the
  _$f$-tower_ is an inductive predicate defined as follows.

  $ kw.dat th tower.t_f cl X -> base.Prop kw.whr \
    quad tower.tb {x} cl tower.t_f th x -> tower.t_f th (f th x) \
    quad tower.tinf {P} cl P subset.eq tower.t_f -> tower.t_f th (and.big P) $

  We will write $x in tower.t_f$ for $tower.t_f th x$. ] <def-tower> 
  
#tom[Dur à lire! Je pense qu'a minima il faudrait expliquer que $P subset.eq
tower.t_f$ signifie $forall x:X, P th x → tower.t_f th x$. Mais ça serait ptet
même mieux de dire "where we write ..., and accordingly $P subset.eq tower.t_f$
for $forall x, P th x -> x in tower.t_f$" et d'utiliser ces notations dans toute
la def. En fait, plus précisément, je crois que je préfèrerais que tu choisisses
définitivement entre $x in P$ et $P th x$, resp. $M subset.eq P$ et $forall x, M
th x -> P th x$. Y en a de partout plus bas et c'est tout mélangé.

Mais de toute façon ça sera dur à lire, pcq le lien avec le compagnon ne
saute pas du tout aux yeux. L'intuition des constructeurs manque cruellement, je
trouve.

Par ex, c'est plus ou moins clair que $tower.tb$ correspond au jeu de
bisim, mais tu sais expliquer la présence de $tower.tinf$?

Est-ce qu'une présentation par règles d'inférences aide à comprendre? Je tente:

  #inferrule(
    [$x in tower.t_f$],
    [$f th x in tower.t_f$],
  )
  #inferrule(
    ([$... $],
    [$x_i in tower.t_f $],
    [$... $]),
        [$ and.big_i x_i in tower.t_f$],
  )
  
]

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

#tom[Y a une "compo sous $forall$" ici, pas sûr d'avoir vu ça noté comme ça
ailleurs, j'ai eu un peu l'impression de me faire arnaquer...]

#theorem[Tower Fixpoint][
  Given a complete lattice $X$ and a monotone endo-map $f cl X -> X$, pose
  $tower.nu f := and.big tower.t_f$.
  The following statements are true:
  1. $tower.nu f in tower.t_f$
  2. $f th (tower.nu f) lt.tilde tower.nu f$,
  3. $tower.nu f lt.tilde f th (tower.nu f)$,
  4. for all $x$, if $x lt.tilde f th x$, then $x lt.tilde tower.nu f$.
] <lem-tower-fix>
#proof[
  1. By $tower.tinf th (lambda t. th t)$.
  2. Using 1., by tower induction on $P th x := f th x lt.tilde x$
  3. Using 1., by $tower.tb$ we have $f th (tower.nu f) in tower.t_f$, the result
     follows by definition of $tower.nu f$ as an infimum.
  4. Using 1., by tower induction on $P th y := x lt.tilde y$.
  #v(-2em)
]

#tom[Je comprends pas le (2), tu peux détailler un poil?

  Sinon, typomaniac strikes back: j'ai jamais vu des items référencés par "1.",
plutôt (1).]

And this is it! I really want to stress the fact that this is the entirety of the
mathematical content of this theory of coinduction, and yet it
provides an exceedingly versatile and easy-to-use theorem. It is easily shown
to subsume the tools provided by the companion construction and by parametrized
coinduction~#mcite(<HurNDV13>). The coq-coinduction library follows-up with
some helpers for deriving inf-closedness of predicates, the definition of the
most useful instances of complete lattices and some generic duality and
symmetry arguments. Schäfer and Smolka~#mcite(<SchaferS17>) follow-up by
deriving the companion and then provide a case study on strong bisimilarity in
the Calculus of Communicating Processes (CCS).

=== Strong Bisimilarity

#peio[intro nulle, citer @Levy11] Equipped with this new construction of
coinductive fixpoints we will apply them, in the complete lattice of relations.
Bisimilarity (both strong and weak), are typically built on non-indexed
automata, which moreover do not have _outputs_. As such they consist of a single
relation, on such automata. As our automata (indexed interaction trees,
@def-itree) are indexed and moreover have an output, our notions of bisimilarity
will instead take the form of indexed relation #tom[je remplace family-relation
par indexed relation, vu que family relation est défini ci-dessous.]
transformers. More precisely, in this section, we fix a signature $Sigma cl
icont.t th I$, and then, given an indexed relation $R^rel.r$ on outputs $R^1,
R^2$, i.e.,

$ R^rel.r cl forall th {i} -> R^1 th i -> R^2 th i -> base.Prop, $

we define strong bisimilarity as a family-relation

$ - iteq(R^rel.r) - cl
  forall th {i} -> itree.t_Sigma th R^1 th i
                -> itree.t_Sigma th R^2 th i
                -> base.Prop. $

We start with some preliminary notation for our indexed relations.

#definition[Family Relation][
  Given $I cl base.Set$ and two families $X, Y cl I -> base.Set$, the set of
  _family relations between $X$ and $Y$_ is defined as follows.

  $ rel.irel th X th Y := forall th {i} -> X th i -> Y th i -> base.Prop $

  We denote by $lt.tilde$ (in infix notation) the standard ordering on family
  relations, defined by
  
  $ R lt.tilde S := forall th {i} th x th y, R th x th y -> S th x th y, $

  for any $R,S : rel.irel th X th Y$.  

  We define the standard operators of diagonal, converse, and sequential
  composition on family relations, as follows.

  #mathpar(spacing: 2em, block: false, inset: 0.5em,
    [$ & rel.diagS cl rel.irel th X th X \
       & rel.diagS th a th b := a = b $],
    [$ & -^rel.revS cl rel.irel th X th Y -> rel.irel th Y th X \
       & R^rel.revS th a th b := R th b th a $],
    [$ & - rel.seqS - cl rel.irel th X th Y -> rel.irel th Y th Z -> rel.irel th X th Z \
       & (R rel.seqS S) th a th c := exists th b, R th a th b and S th b th c $]
  )
]

#definition[Family Equivalence][
  Given $R cl rel.irel th X th X$, we say that
  - _$R$ is reflexive_ whenever $rel.diagS lt.tilde R$;
  - _$R$ is symmetric_ whenever $R^rel.revS lt.tilde R$;
  - _$R$ is transitive_ whenever $R rel.seqS R lt.tilde R$; and
  - _$R$ is an equivalence_ whenever it is reflexive, symmetric, and transitive.
]

As indexed relations are quite a mouthful, the following definition will be
quite heavy notationally. However, it is important to stress that it is entirely
straightforward. Indeed, it follows more or less directly from a relational
interpretation of type theory. #tom[Comprends pas.]

#tom[Dans la def ci-dessous, ça me met de la charge cognitive superflue d'avoir
$R^1$ et $R^2$ qui ne sont pas des relations. Tu pourrais ptet les appeler
$A^i$, comme "answer"?] 

#definition[Action Relator][
Given $Sigma cl icont.t th I$, an output relation $R^rel.r cl rel.irel th R^1 th
  R^2$, and a parameter relation $X^rel.r cl rel.irel th X^1 th X^2$, the
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
  The following statements hold (understood as universally quantified).

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

#tom[Le premier point est presque trop efficace, ptet tu pourrais mettre une
remarque pour expliquer les arguments implicites des $rel.diagS$? Les expliciter
serait trop long?

Et ptet pour les catégoriciennes dire que c'est le relèvement canonique aux relations?]

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

  For any given family relation $R^r : rel.irel th R^1 th R^2$, we define
  heterogeneous and homogeneous _strong bisimilarity_ over $R^r$, denoted by
  $iteq(R^rel.r)$, as follows.

  $ a iteq(R^rel.r) b := tower.nu th itree.sb_Sigma th R^rel.r th a th b \
    a de(approx.eq) b := a iteq(rel.diagS) b $
]

#tom[Ptet faire la remarque qu'ici on prend le point fixe avant d'appliquer à
$R^r$, mais que ça revient au même que de fixer $R^r$ puis prendre le point fixe
puisque tout est point à point.]

#lemma[
  Given $Sigma cl icont.t th I$, for all $x in tower.t_(itree.sb_Sigma)$, the
  following statements are true.

#tom[Ah, arrivé ici, je sais pointer une raison qui fait que ta présentation de
la tower induction est un peu rude: c'est qu'on n'a aucune intuition de ce
qu'est un élément de $tower.t_f$. Ici, tu quantifies dessus et ça m'évoque rien.]

  #let xx = [$R^rel.r$]

  $ R^rel.r_1 lt.tilde R^rel.r_2 -> x th R^rel.r_1 & lt.tilde x th R^rel.r_2 \
    rel.diagS & lt.tilde x th rel.diagS \
    (x th R^rel.r)^rel.revS & lt.tilde x th xx^rel.revS \
    x th R^rel.r_1 rel.seqS x th R^rel.r_2 & lt.tilde x th (R^rel.r_1 rel.seqS R^rel.r_2) $

  As a consequence, when $R^rel.r cl rel.irel th X th X$ is an equivalence
  relation, $x th R^rel.r$ is an equivalence relation. In particular, strong
  bisimilarity $de(approx.eq)$ is an equivalence relation. ] <lem-sbisim-props>

#proof[ All statements are proven by direct tower induction, applying the
corresponding statement from @lem-actrel-props.

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
  $ itree.eatlr := xx \
    itree.eatrl := xx^rel.revS $
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
      quad (itree.eatlr rel.seqS itree.RS th R^rel.r th (x th R^rel.r) rel.seqS itree.eatrl) th (t^1 .itree.obs) th (t^2 .itree.obs) $

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

  $ "" sync "" & := itree.RS th R^rel.r th itweq(R^rel.r) \
    "" weak "" & := "" eat rel.seqS sync rel.seqS eatr $

  Prove the following statements by direct induction on the eating relation for all $a, b, c$.

  1. $a eat itree.tauF th b sync c -> a sync c$
  2. $ a sync itree.tauF th b eatr c -> a sync c$

  Observe that the following statements are true by case analysis.

  3. $itree.tauF th a weak b -> a .itree.obs weak b$
  4. $a weak itree.tauF b -> a weak b .itree.obs$

  Using 3. and 4., prove the following statements by induction.

  5. $a crel((weak rel.seqS eat)) itree.retF th r -> a crel((eat rel.seqS sync)) itree.retF r$
  6. $a crel((weak rel.seqS eat)) itree.visF th q th k -> a crel((eat rel.seqS sync)) itree.visF th q th k$
  7. $itree.retF th r crel((eatr rel.seqS weak)) b -> itree.retF th r crel((sync rel.seqS eatr)) b$
  8. $itree.visF th q th k crel((eatr rel.seqS weak)) b -> itree.visF th q th k crel((sync rel.seqS eatr)) b$

  Finally, note that the following is true by (nested) induction.

  9. $a crel((eatr rel.seqS eat)) b -> a eat b or a eatr b$

  Then, we prove the following statment.

  10. $cnorm(weak) rel.seqS cnorm(weak) th th lt.tilde th th cnorm(eat) rel.seqS itree.RS th R^rel.r th (itweq(R^rel.r) rel.seqS itweq(R^rel.r)) rel.seqS eatr$

  Introducing and decomposing the hypotheses, we obtain the following:

  $ a eat x_1 sync x_2 eatr b eat y_1 sync y_2 eatr c $

  By applying 9. in the middle, assume w.l.o.g. that the left case is true,
  i.e., $x_2 eat y_1$ (for the right case, swap applications of 5. and 6. with
  corresponding applications of 7. and 8.). By case on $y_1$.

  - When $y_1 = itree.retF th r$,

    $ & a & eat x_1 & sync x_2 &          & eat itree.retF th r & sync y_2 eatr c & \
    & a & eat x_1 & sync x_2 & eatr x_2 & eat itree.retF th r & sync y_2 eatr c & quad "by refl." \
    & a &         & weak     &      x_2 & eat itree.retF th r & sync y_2 eatr c & quad "by def." \
    & a &         & eat      &      x_3 & sync itree.retF th r & sync y_2 eatr c & quad "by 5." \
  $

    By concatenation (@lem-actrel-props) between $x_3$ and $y_2$, we obtain 

    $ itree.RS th (R^rel.r rel.seqS R^rel.r) th (itweq(R^rel.r) rel.seqS
    itweq(R^rel.r)) th x_3 th y_2. $

    By transitivity, $R^rel.r rel.seqS R^rel.r lt.tilde R^rel.r$. By
    monotonicity (@lem-actrel-props) we obtain the following and conclude.

    $ itree.RS th R^rel.r th (itweq(R^rel.r) rel.seqS
    itweq(R^rel.r)) th x_3 th y_2. $

  - When $y_1 = itree.visF th q th k$, the reasoning is the same, swapping
    lemma 5. with lemma 6.
  - When $y_1 = itree.tauF th t$,

    $ & a & eat x_1 & sync x_2 & eat itree.tauF th t & sync y_2 eatr c & \
      & a & eat x_1 & sync x_2 &                     & sync y_2 eatr c & quad "by 1." \
    $

    By @lem-actrel-props, using concatenation between $x_2$ and $y_2$, we obtain 

    $ itree.RS th (R^rel.r rel.seqS R^rel.r) th (itweq(R^rel.r) rel.seqS
    itweq(R^rel.r)) th x_3 th y_2, $

    we then conclude as before by transitivity of $R^rel.r$.

  This conclude the proof of 10. Finally, we prove transitivity of
  $itweq(R^rel.r)$ by tower induction on

  $ P th x := cnorm(itweq(R^rel.r)) rel.seqS cnorm(itweq(R^rel.r)) lt.tilde x th R^rel.r. $

  $P$ is inf-closed. Assuming $P th x$, let us prove $P th (itree.wb_Sigma th x)$, i.e.,

  $ cnorm(itweq(R^rel.r)) rel.seqS cnorm(itweq(R^rel.r)) th th lt.tilde th th itree.wb_Sigma th x th R^rel.r $

  By one step unfolding, it suffices to prove the following.

  $ cnorm(weak) rel.seqS cnorm(weak)
    th th lt.tilde th th
    cnorm(eat) rel.seqS itree.RS th R^rel.r th (x th R^rel.r) rel.seqS cnorm(eatr) $

  We apply 10. and conclude by monotonicity on $P th x$.
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
    "" weak "" & := cnorm(eat) rel.seqS sync rel.seqS eatr $

  Prove the following statements by direct induction.

  1. $a crel((strong rel.seqS eat)) b -> a crel((eat rel.seqS strong)) b $
  2. $a crel((eatr rel.seqS strong)) b -> a crel((strong rel.seqS eatr)) b $

  Then, prove the goal by tower induction on

  $ P th x := cnorm(iteq(R^rel.r)) rel.seqS x th R^rel.r rel.seqS cnorm(iteq(R^rel.r))
    lt.tilde x th R^rel.r. $

  $P$ is inf-closed. Assuming $P th x$, let us prove $P th (itree.wb_Sigma th x)$, i.e.,

  $ cnorm(iteq(R^rel.r)) rel.seqS itree.wb_Sigma th x th R^rel.r rel.seqS cnorm(iteq(R^rel.r))
    lt.tilde itree.wb_Sigma th x th R^rel.r. $

  By one-step unfolding it suffices to prove the following.

  $ strong rel.seqS weak rel.seqS strong
    th th lt.tilde th th weak $

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

== Core Operations

=== Monad Structure

=== Interpretation

== Iteration Operators <sec-iter>

=== Fixed points of Equations

#import "/lib/all.typ": *

= Coinductive Game Strategies <ch-game>

As we have seen, Operational Game Semantics, and more generally interactive
semantics, rest upon a dialogue following particular rules, a so-called two
player game. The main task in this chapter is to properly define what is
meant by a "game", "strategy", "transition system", and to provide basic
building blocks for manipulating them. This chapter thus takes a step back and
temporarily puts on hold our concerns about programming language semantics, in
order to introduce the tools required to concretely represent games and
strategies in type theory. These tools are in part novel, but consist mostly of
natural extensions of preexisting devices.

== A Matter of Computation

At heart, a strategy for a given two player game is an automaton of some kind,
in the loose sense that it has some internal states tracking information
required to choose moves, and alternates between two kinds of transitions.
Whenever it is their turn, i.e., in an active state, a strategy must choose a
move to play and transition to a passive state. And in a passive state, the
strategy must accept any possible move made by a hypothetical opponent and
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
#nm[Levy] and #nm[Staton]~#mcite(<LevyS14>). The rest of the chapter is
organized as follows.

- In @sec-levy-staton, I reconstruct Paul Levy and Sam Staton's notion of
  game and of coalgebraic transition system.
- In @sec-itree, I introduce _indexed interaction trees_, a novel generalization of
  interaction trees adapted to the above notion of games.
- In @sec-bisim, I define their bisimilarity together with powerful reasoning
  principles based on a lattice-theoretic fixed point construction.
- In @sec-itree-monad, I give a little bit of structure to indexed interaction
  tree, lifted from the non-indexed setting.
- In @sec-iter I develop upon the theory of iteration operators, providing a
  novel _eventually guarded iteration_, applicable to the delay
  monad~#mcite(<Capretta05>), but also to indexed and non-indexed interaction
  trees.

== #nm[Levy] & #nm[Staton] Games <sec-levy-staton>

=== An Intuitive Reconstruction

The definition of game obtained by #nm[Levy] and #nm[Staton] in
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
by mere sets, we can describe them by two families $M^+ cl I^+ -> base.Type$ and
$M^- cl I^- -> base.Type$, mapping to each position the set of currently allowed
moves. Finally, we must describe how the position evolves after a move has been
played. This can be encoded by two maps $"next"^+ cl forall i^+, th M^+ th i^+ ->
I^-$ and $"next"^- cl forall i^-, th M^- th i^- -> I^+$. This leads us to the
following definitions.

#definition[Half-Game][
  Given $I, J cl base.Type$ a _half-game with input positions $I$
  and output positions $J$_ is given by a record of the following type.

  $ kw.rec th game.hg th I th J th kw.whr \
    pat(game.mv cl I -> base.Type,
        game.nx th {i} cl game.mv th i -> J) $
] <def-hg>

#definition[Game][
  #margin-note[This is called _discrete game_ by #nm[Levy] and #nm[Staton]~#num-cite(<LevyS14>).]
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
displayed style of #nm[Ahrens] and #nm[Lumsdaine]~#mcite(<AhrensL19>),
but I will resist the urge to dive too
deeply into the structure of games and leave most of it for further work to
expose. Indeed, we will require none of it for our main goal of proving
correctness of OGS. Moreover, as already noted by #nm[Dagand] and
#nm[McBride]~#mcite(<DagandM13>, supplement: "Sec. 1.3") in the similar setting
of indexed containers, describing the extremely rich structures at play requires
advanced concepts, such as framed bicategories and two-sided fibrations.

#peio["simulation" vs "morphism"?]

#definition[Half-Game Simulation][
  Given two half-games $A, B cl game.hg th I th J$, a _half-game simulation
  from $A$ to $B$_ is given by the following record.

#tom[by a record of the following type (partout...)?]
  

  $ kw.rec game.hsim th A th B kw.whr \
    pat(game.hstr {i} cl A .game.mv th i -> B .game.mv th i,
        game.hscoh {i} th (m cl A .game.mv th i) cl B .game.nx th (game.hstr th m) = A .game.nx th m) $
]


#definition[Simulation][
  Given two games $A, B cl game.g th I^+ th I^-$, a _game simulation from $A$
  to $B$_ is given by a record of the following type.

  $ kw.rec game.sim th A th B kw.whr \
    pat(game.scli cl game.hsim th A .game.client th B .game.client,
        game.ssrv cl game.hsim th B .game.server th A .game.server) $
]

#guil[Tu pourrais expliquer à ce moment là la structure catégorique sur HGame et sur Game,
en explicitant notamment la composition de simulations et la simulation identité.
Sinon on a du mal à comprendre d'où sort le $base.Cat$ en dessous.]

#remark[Half-Game is Functorial][
  $game.hg$ extends to a strict functor $base.Type^"op" times base.Type -> base.Cat$ as witnessed
  by the following action on morphisms, which we write curried and in infix style.

  $ ar game.reixl ar game.reixr ar cl (I_2 -> I_1) -> game.hg th I_1 th J_1 -> (J_1 -> J_2) -> game.hg th I_2 th J_2 \
    f game.reixl A game.reixr g :=
    pat(game.mv th i & := A .game.mv th (f th i),
        game.nx th m & := g th (A .game.nx th m)) $

  The identity and composition laws of this functor hold _definitionally_
  (assuming #{sym.eta}-laws on records and functions).
]


=== Example Games

Let us introduce a couple example games, to get a feel for their expressivity.

#let conway = (
  t: de("Conway"),
  lft: pr("left"),
  rgt: pr("right"),
  ls: de("G-Conway"),
)

*#nm[Conway] Games* #sym.space #nm[Conway] games are an important tool in the study of
_combinatorial games_~#mcite(<Conway76>) #peio[check def there] and may in fact
be considered their prime definition. I will explain how they are an instance of
our notion. We will use the following coinductive, exceedingly simple
definition: a #nm[Conway] game $G cl conway.t$ is given by two subsets of #nm[Conway]
games $G_L, G_R subset.eq conway.t$. The left subset $G_L$ is to be thought of
as the set of games reachable by the left player in one move, and symmetrically
for $G_R$.

#guil[I think Joyal was the first to introduce a categorical
structure on Conway games. See also the presentation by
Méllies of Conway games in connection with Game Semantics.]

#margin-note[For a more in-depth discussion of the two notions of subsets in
    type theory, see #text-cite(<HancockH06>, supplement: [pp. 194--198])]
In order to translate this definition into type theory, the only
question is how to represent subsets.
The most familiar one is the powerset construction, adopting the point-of-view
of subsets as (proof-relevant) predicates:

$ subs.Pow cl base.Type -> base.Type \
  subs.Pow th X kw.whr X -> base.Type $

However there is another, more intensional one, viewing subsets as families:

#tom[Proof-relevant plus que intentional, non?] 
#tom[Euh... et en fait je comprends pas la def... Ah si, c'est la version
fibrée! Qui l'eut cru venant de toi... Bon, bref, ça coule pas de source à cet
endroit.]
#tom[De plus, les deux defs n'étant pas équivalentes, est-ce qu'il ne vaudrait
pas mieux assumer la différence et appeler ça des proof-relevant Conway games?]

$ kw.rec subs.Fam th (X cl base.Type) cl base.Type kw.whr \
  pat(subs.dom cl base.Type,
      subs.idx cl subs.dom -> X) $

Because we want to easily manipulate the support of the two subsets $G_L$ and
$G_R$, i.e., in this context the set of left moves and right moves, we adopt
the second representation.

#definition[#nm[Conway] Game][
    The set of _#nm[Conway] games_ is given by the following coinductive record.

    $ kw.rec conway.t cl base.Type kw.whr \
      pat(conway.lft cl subs.Fam th conway.t,
          conway.rgt cl subs.Fam th conway.t) $
]

We can now give the #nm[Levy] & #nm[Staton] game of #nm[Conway] games. As in a
#nm[Conway] game one does not known whose turn it is to play, the sets of
active and passive positions will be the same. Moreover, the current position
is in fact given by the current Conway game.

#example[Game of #nm[Conway] Games][ We start by noticing that $I -> subs.Fam th J$
  is just a shuffling of $game.hg th I th J$:

  $ de("fam-to-hg") cl (I -> subs.Fam th J) -> game.hg th I th J \
    de("fam-to-hg") th F :=
      pat(game.mv th i & := (F th i) .subs.dom,
          game.nx th {i} th m & := (F th i).subs.idx th m) $

Then, the _game of #nm[Conway] games_ can be given as follows.

  $ conway.ls cl game.g th conway.t th conway.t \
    conway.ls :=
      pat(game.client := de("fam-to-hg") th conway.lft,
          game.server := de("fam-to-hg") th conway.rgt) $
]

#peio[inj LS $=>$ Conway]

#tom[Bon c'est rigolo, mais le sens de tout ça n'est pas hyper clair, si? Est-ce
que les parties au sens de Conway sont les mêmes que celles de Levy-Staton sur
$conway.ls$?]

*Applicative Bisimilarity* #sym.space #peio[applicative bisim]

*OGS Game* #sym.space #peio[ogs stlc?]

=== Strategies as Transition Systems

Following #nm[Levy] and #nm[Staton]~#num-cite(<LevyS14>), we now define client
strategies as transition systems over a given game. We will only define
_client_ strategies, since _server_ strategies can be simply derived from
client strategies on the dual game---the prime benefit of our symmetric notion
of game. We first need to define two interpretations of half-games as functors.


#tom[Les espaces sont bizarres dans la def ci-dessous, non?]
#peio[Fixed? Je vois pas trop lesquels]
#definition[Half-Game Functors][
  Given a half-game $G cl game.hg th I th J$, we define the
  _active interpretation_ and _passive interpretation of $G$_ as functors
  $base.Type^J -> base.Type^I$, written $G game.extA ar$ and $G game.extP ar$ and defined as follows.

  $ (G game.extA X) th i := (m cl G.game.mv th i) times X th (G.game.nx th m) \
    (G game.extP X) th i := (m cl G.game.mv th i) -> X th (G.game.nx th m) $
] <def-hg-ext>

#tom[Chuis pas super fan de la notation $game.extA$, parce qu'elle ressemble
trop à $game.extP$, elle évoque aussi un adjoint à droite plus qu'à gauche.]
#peio[Mieux?]
#guil[Je trouve ça mieux.]

#definition[Transition System][
  Given a game $G cl game.g th I^+ th I^-$ and a family $R cl base.Type^(I^+)$,
  a _transition system over $G$ with output $R$_ is given by the following record.
  #margin-note(dy: -2.7em)[
    In #nm[Levy] & #nm[Staton]~#num-cite(<LevyS14>), the output parameter $R$ is not present and this is
    called a _small-step system over $G$_. We can recover their
    definition by setting $R = emptyset$.
  ]

  $ kw.rec strat.t_G th R kw.whr \
    pat(strat.stp cl I^+ -> base.Type,
        strat.stn cl I^- -> base.Type,
        strat.play cl strat.stp => R + strat.stp + G.game.client game.extA strat.stn,
        strat.coplay cl strat.stn => G.game.server game.extP strat.stp) $
  Where $X => Y := forall th {i}, th X i -> Y i$ denotes a morphism of families.
] <def-tsys>

There is a lot to unpack here. First the states: instead of a mere set, as is
usual in a classical transition system, they here consist of two families
#strat.stp, #strat.stn _over_ respectively the active and passive game
positions. It is important not to confuse _positions_ and _states_. The former
consists of the information used to determine which moves are allowed to be
played. The latter consists of the information used by a given strategy to
determine how to play. Their relationship is similar to that of types to terms.

The $strat.play$ function takes as inputs an active position $i cl I^+$, an
active state  $s cl strat.stp th i$  over $i$ and returns one of three things:

#par(hanging-indent: 2em)[$R th i$ ~~ _"return move"_ \
  This case was not present in #nm[Levy] & #nm[Staton]~#num-cite(<LevyS14>), but
  it allows a strategy to end the game, provided it exhibits an output. As we
  will see with interaction trees in @sec-itree, this allows to equip transition
  systems with a monad structure, an important tool for compositional manipulation.
]

#par(hanging-indent: 2em)[$strat.stp th i$ ~~ _"silent move"_ \
  In this case, the strategy postpones progression in the game. This case
  allows for strategies to be _partial_ in the same sense as #nm[Capretta]'s
  #delay.t monad~#mcite(<Capretta05>). _Total strategies_ without this case would
  make perfect sense, but we are interested in arbitrary, hence partial, computations.
]

#par(hanging-indent: 2em)[$(G.game.client game.extA strat.stn) th i$ ~~ _"client move"_ \
  By @def-hg-ext, this data consists of a client move valid at the current
  position $i$, together with a passive state over the next position. This case is
  the one which actually _chooses_ a move and sends it to a hypothetical
  opponent.
]

The #strat.coplay function is simpler. By @def-hg-ext, it takes a passive
position, a passive state over it, and a currently valid _"server move"_, and must
then return an active state over the next position.

#guil[You could explain why there is no return move for Opponent.]
#tom[+1! Et "compositional manipulation" survend un peu le truc, non?]
#peio[C'est mieux?]
#guil[oui!]

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

In @def-tsys, I have defined strategies similarly to #nm[Levy] and
#nm[Staton]~#mcite(<LevyS14>), that is, by a state-and-transition-function
presentation of automata. This representation is theoretically satisfying,
however most of the time it is painful to work with formally. As an example,
let's assume I want to define a binary combinator, taking two transition systems as
arguments and returning a third one. Each of the two inputs is a dependent record with
four fields, so that I have to work with eight input components to define the
resulting transition systems, itself consisting of two families of states, and
then, depending on these new states, two suitable transition functions. This is
a lot to manage!

This unwieldiness is well known: while useful, writing state-machine-like code
is closely linked to the dreaded _spaghetti code_ and _callback hell_. It is
perhaps the prime reason why widely used programming languages have started
organizing it using syntactic facilities like the #txtt("yield") keyword of python's
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
opaque notion of automaton (e.g., generators, awaitables), for which the only possible
operation is _stepping_, i.e., running until the next transition.
In this section I will apply this methodology to the definition of transition
systems over games and this will bring us to my first contribution: _indexed
interaction trees_.

#tom[Ça je connais pas du tout.]
#yann[Euuuh je ne comprends pas bien le lien avec cooperative multithreading]
#peio[Better?]
#guil[Je suis encore un peu perplexe par le paragraphe du dessus,
mais c'est surement car je ne m'y connais pas du tout en event-driven programming.]

=== From Games to Containers

Notice that @def-tsys is exactly the definition of a coalgebra for some
endofunctor on $base.Type^(I^+) times base.Type^(I^-)$.
#guil[Est-ce-que tu peux détailler ? Vu que G et R dépendent aussi de 
$I^+$ et $I^-$, ce n'est pas complètement évident je trouve.]
 Then, as by definition
any coalgebra maps uniquely into the final coalgebra, it is sufficient to work
with this final coalgebra, whose states intuitively consist of infinite trees,
describing the traces of any possible transition system over $G$. This
"universal" state space---the state space of the final coalgebra---will be our
core notion of automata.

#tom[Là-dessus ptet dire "modulo les questions de taille" quelque part?]
#peio[Je comprend pas où ça poserait pb, la coinduction coq nous donne bien
une coalgèbre terminale des t-sys de taille $alpha$ (les itree), elle-mème un
t-sys de taille $alpha$, il n'y a pas de bump de taille.]

However, before constructing this final coalgebra, I will simplify the setting
slightly. Notice that we can easily make passive states disappear, by
describing systems as a family of active states $strat.stp cl base.Type^(I^+)$
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
  #peio[Ah oui ok, j'ai posé le calcul. C'est plutot celles où $strat.coplay$ est l'identité (ou un iso).
    Du coup la strat $S^i$ induite elle a les même états actifs, et comme états passifs
    $G.game.server game.extP S^+$. Donc oui $S -> ceil(S^i)$ c'est l'unité de l'adjonction.
    Et la counité est un iso: $ceil(T)^i approx T$.]
]

$ X |-> R + X + G.game.client game.extA (G.game.server game.extP X)) $

#tom[Le truc ci-dessous s'enfonce dans une voie un peu imprévisible, donc c'est
dur à suivre. Il faudrait ptet baliser un peu mieux, dire où tu vas.]
Since in this functor nothing really depends on the server positions $I^-$, we
can play the same trick and eliminate passive positions from the
description of games, obtaining back indexed polynomial functors, or more
precisely their type-theoretic incarnation as _indexed
containers_~#mcite(dy: 10em, <AltenkirchGHMM15>). Remember that the reason for preferring
games over indexed containers was to ease swapping client and server.
#guil[Tu ne l'as pas expliqué avant, du coup tu pourrais enlever le "Remember that".] But since
strategies are inherently biased towards one side, we might as well use the
simpler notion.


#definition[Indexed Container][
  Given $I cl base.Type$, an _indexed container with positions $I$_ is given
  by the following record.

  $ kw.rec icont.t I cl base.Type kw.whr \
    pat(icont.qry cl I -> base.Type,
        icont.rsp th {i} cl icont.qry th i -> base.Type,
        icont.nxt th {i} th {q cl icont.qry th i} cl icont.rsp th q -> I) $
]

#definition[Extension of a Container][
  Given an indexed container $Sigma cl icont.t th I$, we define its _extension_
  $[| Sigma |] cl base.Type^I -> base.Type^I$ as the following functor.

  $ [| Sigma |] th X th i :=
      (q cl Sigma .icont.qry th i)
      times ((r cl Sigma .icont.rsp th q) -> X th (Sigma .icont.nxt th r)) $
]


#definition[Game to Container][
  There is a functor from games to containers defined on object as follows.
    $game.g th I^+ th I^- -> icont.t th I^+$ defined
  on objects as follows.

  $ floor(ar) cl game.g th I^+ th I^- -> icont.t th I^+ \
    floor(A) :=
      pat(icont.qry th i & := A .game.client"".game.mv th i,
          icont.rsp th q & := A .game.server"".game.mv th (A .game.client"".game.nx th q),
          icont.nxt th r & := A .game.server"".game.nx th r) $

  It preserves the extension strictly, in the sense that for all $A cl
  game.g th I^+ th I^-$, the functor $A.game.client game.extA (A.game.server game.extP ar))$ is
  definitionally equal to $[| floor(A) |]$.
]

#remark[Container to Game][ Although games include information about passive
  positions which containers do not, we can guess this information and inject
  containers into games as follows.

  $ ceil(ar) cl (Sigma cl icont.t th I) -> game.g th I th ((i cl I) times Sigma .icont.qry th i) \
    ceil(Sigma) :=
      pat(game.client & := pat(game.mv th i & := Sigma .icont.qry th i,
                               game.nx th {i} th m & := (i , m)),
          game.server & := pat(game.mv th "(" i "," m ")" & := Sigma .icont.rsp th m,
                               game.nx th m & := Sigma .icont.nxt th m)) $

  We observe in passing that $floor(ar) compose ceil(ar)$ is definitionally equal
  to the identity on containers, but not the other way around.
]

=== Indexed Interaction Trees

After this interlude on indexed containers, we are now ready to go back to
strategies. Recall that we had turned strategies into coalgebras for the
functor $X |-> R + X + G.game.client game.extA (G.game.server game.extP X))$
and that we wanted to construct its final coalgebra. Fully forgetting about
passive information, we can now instead work with the functor
$X |-> R + X + [| Sigma |] th X$ for some container $Sigma$, which I call
the _action functor_ on $Sigma$.

#definition[Action Functor][
  Given a signature $Sigma cl icont.t th I$ and an output $R cl
  base.Type^I$, the _action functor on $Sigma$ with output $R$_,
  $itree.F_Sigma th R cl base.Type^I -> base.Type^I$ is defined by the following
  data type.

  $ kw.dat itree.F_Sigma th R th X th i cl base.Type kw.whr \
    pat(
      itree.retF th (r cl R th i),
      itree.tauF th (t cl X th i),
      itree.visF
        th (q cl Sigma .icont.qry th i)
        th (k cl (r cl Sigma .icont.rsp th q) -> X th (Sigma .icont.nxt th r))) $
]

Being itself the extension of some indexed container, $itree.F_Sigma th R$ has a
thoroughly understood theory of fixed points~#mcite(<AltenkirchGHMM15>) and we can
form its final coalgebra as a coinductive family which is accepted by most type
theory implementations#guil[proof assistants] such as Agda and Coq.

#tom[Là je me rends compte que la rédaction est un poil trop linéaire à mon
goût. La def des arbres d'interation indexés est perdue au milieu d'une longue
histoire. Est-ce que tu devrais pas faire une sous-partie "coalgèbre finale /
arbres d'interaction"?] 
#guil[On a notamment une définition indirecte des Indexed Interaction Tree,
vu que tu souhaites faire apparaitre explicitement le foncteur 
$itree.F_Sigma$ dont ils sont la coalgèbre finale, plutôt que donner une 
définition directe. Ça serait bien d'avertir les lecteurices de tes objectifs à ce sujet 
en début de section 2.3.]

#definition[Indexed Interaction Tree][ Given a signature $Sigma cl
  icont.t th I$ and an output $R cl base.Type^I$, the family of
  _indexed interaction trees on $Sigma$ with output $R$_, denoted by
  $itree.t_Sigma th R cl base.Type^I$, is given by coinductive records of the following
  type.

  $ kw.rec itree.t_Sigma th R th i cl base.Type kw.whr \
    pat1(itree.obs cl itree.F_Sigma th R th (itree.t_Sigma th R) th i) $

  Furthermore, define the following shorthands:

  $ & itree.ret th x      & := & pat1(itree.obs := itree.retF th x) \
    & itree.tau th t      & := & pat1(itree.obs := itree.tauF th t) \
    & itree.vis th q th k & := & pat1(itree.obs := itree.visF th q th k) $
] <def-itree>

#guil[I don't understand these shorthands. In which sense can $itree.ret th x$ be seen
as of type $itree.t_Sigma$ ?]
#tom[pas compris les shorthands. Est-ce que tu essaies de dire que 
$itree.ret th x := { itree.obs = itree.retF t x}$, par exemple?]
#peio[Yes, c'est mieux comme ça non?]

Notice that this definition is to interaction trees~#mcite(<XiaZHHMPZ20>)
what inductive families are to inductive data types. As we will discover
in the remainder of this chapter, all of the monadic theory of interaction
trees lifts neatly to this newly indexed setting, an "outrageous fortune"
described by Conor McBride in #mcite(dy: 1.2em, <McBride11>).

#guil[Do you mean that this structure of
indexed interaction tree was already present in
#mcite(dy: 1.2em, <McBride11>)?]
#tom[+1, ça serait bien d'expliquer le lien avec le papier de Conor.]

#tom[Cette phrase devrait-elle être après la def qui suit?] Before moving on to
define bisimilarity, let us first link this definition to transition systems
over games.

#definition[Strategies][
  Given a game $G cl game.g th I^+ th I^-$ and output $R cl base.Type^(I^+)$,
  the _active strategies over $G$ with output $R$_, $game.stratA_G th R cl
  base.Type^(I^+)$ and the _passive strategies over $G$ with output $R$_,
  $game.stratP_G th R cl base.Type^(I^-)$ are given as follows.

  $ game.stratA_G th R := itree.t_floor(G) th R \
    game.stratP_G th R := G.game.server game.extP game.stratA_G th R $
] <def-strat>

#guil[Can you relate this definition of strategies to the one
given in #num-cite(<LevyS14>) (Definition 2)?]

#tom[Ah bien vu! Mais ça va être pénible, pcq leur def ne me semble pas
trivialement équivalente. C'est une def de stratégie à la papa, comme ensemble
de parties déterministes clos par préfixe. Mais pour ce que j'en vois, ils ne
s'en servent que pour caractériser la bisimilarité des états dans les systèmes
de transitions. Notamment ils ne cherchent pas à démontrer l'équivalence, ou le
fait que c'est une coalgèbre finale. Et pire: ils n'ont pas de coup silencieux.
*Donc*: ptet on pourrait dire que la def ici est une reformulation constructive
de la leur, où (1) on modélise les ensembles de branches clos par préfixes comme
des arbres, ok, banal, et (2) on introduit une notion de coup silencieux pour
modéliser l'absence de réponse à un coup comme une divergence?]

#guil[Ça serait chouette de pouvoir prouver ça! Ça permettrait d'expliciter
le lien avec la présentation standard des straégies en sémantique des jeux.]

#lemma[System Unrolling][
  Together, $game.stratA_G th R$ and $game.stratP_G th R$ form the state families
  of the final transition system over $G$ with output $R$, as witnessed by
  the following _unrolling maps_, assuming $S cl strat.t_G th R$.

  $ itree.unrollA cl S .strat.stp => game.stratA_G th R \
    itree.unrollP cl S .strat.stn => game.stratP_G th R \
    \
    itree.unrollA th s := \
    pat(itree.obs := kw.case th S .strat.play th s \
    pat(
            cs("inj"_1) th r      & := itree.retF th r,
            cs("inj"_2) th s      & := itree.tauF th (itree.unrollA th s),
            cs("inj"_3) th (m, s) & := itree.visF th m th (itree.unrollP th s))) \
    /*itree.unrollA th s :=
      pat(itree.obs := kw.case th S .strat.play th s
        pat(cs("inj"_1) th r := itree.retF th r,
            cs("inj"_2) th s := itree.tauF th (itree.unrollA th s),
            cs("inj"_3) th (m, s) := itree.visF th m th (itree.unrollP th s))) \
    (itree.unrollA th s) .itree.obs th kw.wit S .strat.play th s \
    quad | cs("inj"_1) th r := itree.retF th r \
    quad | cs("inj"_2) th s' := itree.tauF th (itree.unrollA th s') \
    quad | cs("inj"_3) th (m , s') := itree.visF th m th (itree.unrollP th s') \ */
    itree.unrollP th s th m := itree.unrollA th (S .strat.coplay th s th m)
    $

  $cs("inj"_1)$, $cs("inj"_2)$ and $cs("inj"_3)$ denote the obvious injections
  into the ternary coproduct. These functions can be shown to be the
  computational part of the unique coalgebra morphism between $S$ and
  strategies.
] <def-unroll>

#guil[I am struggling to understand this lemma,
what is a state family of the final transition system ?]

#tom[Attention! On n'a même pas défini les morphismes entre systèmes de
transitions...]
#tom[La systaxe $(itree.unrollA th s) .itree.obs th kw.wit S .strat.play th s$
m'est inconnue, et est un peu obscure, alors que pourtant ce qu'il faut faire
est clair. J'imagine laborieusement que ça veut dire $itree.unrollA th s :=
"match" S .strat.play th s "with"...$? Ça sera ptet introduit kek part?]

#tom[Et aussi, ça serait bien de rendre explicite que c'est une def
coinductive.]

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
support for coinductive records (such as @def-itree) and for cofixpoints, or
coinductive definitions (such as @def-unroll). However, these features---in
particular cofixpoints---are at times brittle, because type theory typically relies on a
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
fully clear #peio[ref multi-clocked guarded TT].

#guil[I don't think the connection between sized types and guarded recursive
types has been worked out.] #tom[Mais donc c'est quoi le pb? Et ta
recommandation ici?]
#guil[De citer un article sur les sized types plutot que sur les multi-clocked 
guarded type theory.]
We will take an entirely
different route, building coinduction for ourselves, _inside_ type theory.
Indeed, as demonstrated by Damien Pous's coq-coinduction
library~#mcite(<Pous16>, supplement: [https://github.com/damien-pous/coinduction]),
powerful coinductive constructions and reasoning principles for propositional
types are derivable in the presence of impredicativity.
#tom[Pourquoi la font de coq-coinduction est-elle si petite?]
#yann[J'ai l'impression que cette fin de paragraphe suggère que tu réimplémentes une librairie de coind plutôt que tu utilises celle de Damien]

=== Coinduction with Complete Lattices

The basis of coq-coinduction is the observation that with impredicativity,
#base.Prop forms a complete lattice. In fact, not only #base.Prop, but also
predicates $X -> base.Prop$ or relations $X -> Y -> base.Prop$, our case of
interest for bisimilarity. By the #nm[Knaster]-#nm[Tarski] theorem~#mcite(<Tarski55>) one can obtain the
greatest fixed point $nu f := or.big { x | x lt.tilde f th x }$ of any monotone
endo-map $f$ on the complete lattice.
#yann[Ref de KT]

This is only the first part of the story. Indeed this will provide us with the
greatest fixed point $nu f$, in our case, bisimilarity, but the reasoning
principles will be cumbersome. At first sight, the only principle available is the
following one.

#centering(inferrule(
  [$x lt.tilde f th x$],
  [$x lt.tilde nu f$]
))

Programming solely with this principle is painful, much in the same way as
manipulating inductive types solely using eliminators, instead of using
pattern-matching and recursive functions. Thankfully, in the context of
bisimulations, a line of work has developed a theory of _enhanced_
bisimulations, in which the premise is weakened to $x lt.tilde f th (g th x)$---
bisimulation _up-to $g$_---for some _compatible_ $g$, which must verify $g
compose f lt.tilde f compose g$. 
#guil[Ça vaudrait le coup d'indiquer que tu utilise le pointwise order sur les 
fonctions.]
#tom[Attention, la compatibilité n'est pas
nécessaire, si?] #guil[+1, je pense qu'il vaudrait mieux introduire la notion
de enhanced bisimulation sans parler de compatibilité, puis d'indiquer
qu'il existe des cadres génériques pour montrer que ces techniques up-to sont
sound: compatibility, respectfulness. Un des points importants de ces notions
est qu'elles sont stables par composition.]
#yann[Je suis d'accord oui, autant définir tranquillement un up-to sound et parler des bonnes propriétés de clôture des fonctions compatibles en citant la littérature. J'ai écrit une version de ça qui vaut ce qu'elle vaut en Section 4.1 de ce papier si tu veux : https://perso.ens-lyon.fr/yannick.zakowski/papers/ctrees-jfp.pdf]
#yann[A forciori vis à vis du companion on exploite que toute fonction sous le companion est sound, ce qui contient par définition toutes les fonctions compatibles, mais pas que !]
 This eases bisimilarity proofs where, for
example, the relation between states is only preserved by the transition
functions up-to transitive closure, provided the transitive closure has been
proven compatible.
#yann[Pas complètement clair pour moi quelle clôture précise tu veux dire par là. Tu veux dire une bisimulation up-to bisimilarity?]

Satisfyingly, the least upper bound of all compatible functions is still
compatible. It is called the _companion_ of $f$,#yann[(citation Coinduction all the way up)] written $t_f$, and moreover
satisfies $t_f bot th approx nu f$ #guil[Il me semble que $approx$ n'a pas été introduit]. 
This enables working with the following
generalized principle.

#centering(inferrule(
  [$x lt.tilde f th (t_f th x)$],
  [$x lt.tilde nu f$]
))

In this way, one delays until actually required in the proof the choice and use
of any particular enhancement $g lt.tilde t_f$.#yann[Techniquement ça se passe aussi bien que cela aussi parce que le companion contient l'identité, f lui-même, et son carré notamment, pour vraiment pouvoir sortir des up-to unitaires à la volée pendant la preuve.] This theory based on the
companion is the one used in the Coq formalization of this thesis. However,
since I started writing the formalization, an even more practical solution,
#nm[Schäfer] and #nm[Smolka]'s _tower induction_~#mcite(<SchaferS17>), has
been merged into coq-coinduction. However, I did not have the time to
port my Coq development to the new version. I will nonetheless present it
here and use it in the rest of the thesis.

Tower induction rests upon the inductive definition of the tower predicate $tower.t_f$,
whose elements can be understood as all the transfinite iterations of $f$,
starting from $top$. In other words, $tower.t_f$ characterizes the transfinite approximants
of the greatest fixed point of $f$.

For more easily working with predicates, we will use some notations. For any
predicate $P$ we will write $x in P$ instead of $P th x$ and $forall th x in P
-> ...$ instead of $forall th {x} -> P th x -> ...$

#tom[Formulation bizarre: le tower predicate, c'est $t_f$?]
#yann[Je ne crois pas non, $t_f$ est le companion. Le companion peut être caractérisé en terme de la chaine, mais cette caractérisation n'est pas mentionnée ici. On passe plutôt à une autre construction donnant des principes de raisonnements très similaires mais présentés différemment.]

#definition[Tower][
  Given a complete lattice $X$ and a monotone endo-map $f cl X -> X$, the
  _$f$-Tower_ is an inductive predicate defined as follows.

  $ kw.dat th tower.t_f cl X -> base.Prop kw.whr \
    pat(tower.tb th {x} cl x in tower.t_f -> f th x in tower.t_f,
        tower.tinf th {T} cl (forall th x in T -> x in tower.t_f) -> (and.big T) in tower.t_f) $
] <def-tower> 
  
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

#guil[Je trouve que la présentation par règles d'inférences est beaucoup plus lisible.]

#yann[Je pense qu'il faut surtout clarifier que c'est un apparté sans conséquence, et le positionner comme c'est fait en fin de section peut-être plus en amont. Le lien avec le companion n'est pas fait ici, et n'est pas nécessaire: le point essentiel de la tower est d'avoir (yet another après knaster-tarski, parameterized coinduction, companion, ...) une construction alternative du gfp, avec un support pour de bon principes de raisonnement. En particulier, là où le companion amenait avec sa construction :
1. un up-to companion lui-même valid et permettant d'accéder à toute fonction sous le companion durant une preuve par coinduction.
2. deux méthodes de preuve de up-to : par compatibilité, ou via le companion d'ordre supérieur;
Et bien la tower amène avec sa propre construction (gfp f = inf (tower f)):
1. un up-to lui-même permettant d'accéder à toute fonction qui respecte tous les éléments de la chaine;
2. une méthode de preuve de up-to simple et uniforme : la tower induction, i.e., prouve moi que ton prédicat est clôt par f et par infimum (i.e., les deux constructeurs/règles d'inférence de la tour)
Globalement la théorie est plus simple, et l'usage relativement plus simple puisque tout s'exprime directement en terme de jolies instances proper, sans jongler entre les deux niveaux de companion.

Et certes le companion peut être charactérisé en ces termes, mais en pratique cet aspect importe peu il me semble, sauf pour récupérer certaines preuves existantes.
]

#theorem[Tower Induction][
  Given a complete lattice $X$, a monotone endo-map $f cl X -> X$ and an inf-closed
  predicate $P cl X -> base.Prop$, the following _tower induction principle_ is true.

  #inferrule(
    [$forall th x in tower.t_f -> P th x -> P th (f th x)$],
    [$forall th x in tower.t_f -> P th x$],
    suppl: tower.tind
  )
] <thm-tower-ind>
#proof[
  Assuming that $P$ is inf-closed and that the premise is valid, i.e.,

  $ K cl forall th {T} -> T subset.eq P -> P th (and.big T) \
    H cl forall th {x} -> x in tower.t_f -> P th x -> P th (f th x), $

  define the following by induction.

  $ tower.tind cl forall th {x} -> x in tower.t_f -> P th x $
  #v(-0.5em)
  $ & tower.tind th (tower.tb t)   && := H th t th (tower.tind th t) \
    & tower.tind th (tower.tinf s) && := K th (kw.fun th p |-> tower.tind th (s th p)) $
  #v(-2em)
]

#lemma[Tower Properties][
  Given a complete lattice $X$ and a monotone endo-map $f cl X -> X$,
  for all $x in tower.t_f$ the following statements are true.

  1. $f th x lt.tilde x$
  2. $forall th y -> y lt.tilde f th y -> y lt.tilde x$ 
] <lem-tower-props>
#proof[Both by direct tower induction on the statement.]

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
  2.
     - $tower.nu f lt.tilde f th (tower.nu f)$ #sym.space.quad By $tower.tb$ and (1), we
       have $f th (tower.nu f) in tower.t_f$. Conclude by definition of $tower.nu$ as
       an infimum.
     - $f th (tower.nu f) lt.tilde tower.nu f$ #sym.space.quad By (1) we and @lem-tower-props (1).
  3. By (1) and @lem-tower-props (2).
  #v(-2em)
]

In @lem-tower-fix, (2) and (3) are pretty clear: they prove that $tower.nu f$
is indeed the greatest fixed point of $f$. On the other hand, (1) might seem
like a technical lemma, however it is just as important, if not more. Indeed,
knowing that $tower.nu f$ is part of the tower---i.e., that it is itself a
transfinite approximation of the greatest fixed point---enables to directly
apply tower induction (@thm-tower-ind) to prove properties about $tower.nu f$.

#tom[Je comprends pas le (2), tu peux détailler un poil?]

#peio[Better?]

And this is it! I really want to stress the fact that this is the entirety of the
mathematical content of this theory of coinduction, and yet it
provides an exceedingly versatile and easy-to-use theorem. It is easily shown
to subsume the tools provided by the companion construction and by parametrized
coinduction~#mcite(<HurNDV13>). The coq-coinduction library follows-up with
some helpers for deriving inf-closedness of predicates, the definition of the
most useful instances of complete lattices and some generic duality and
symmetry arguments. #nm[Schäfer] and #nm[Smolka]~#mcite(<SchaferS17>) follow-up by
deriving the companion and then provide a case study on strong bisimilarity in
the Calculus of Communicating Processes (CCS).

=== Strong Bisimilarity

#peio[intro nulle, citer @Levy11] Equipped with this new construction of
coinductive fixed points we will apply them, in the complete lattice of relations.#yann[Peut-être sans importance, mais le lattice en question est plus précisément celui des relations indexées sur une paire de type family fixées (comme tu le définies ci-dessous)]
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

$ ar iteq(R^rel.r) ar cl
  forall th {i} -> itree.t_Sigma th R^1 th i
                -> itree.t_Sigma th R^2 th i
                -> base.Prop. $

#guil[Ça serait plus clair d'utiliser $X$ et $Y$ plutôt que 
$R^1$ et $R^2$ au dessus, pour être consistant avec la suite.]

We start with some preliminary notation for our indexed relations.

#definition[Family Relation][
  Given $I cl base.Type$ and two families $X, Y cl base.Type^I$, the set of
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
    [$ & ar^rel.revS cl rel.irel th X th Y -> rel.irel th Y th X \
       & R^rel.revS th a th b := R th b th a $],
    [$ & ar rel.seqS ar cl rel.irel th X th Y -> rel.irel th Y th Z -> rel.irel th X th Z \
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

#guil[Tu pourrais expliquer ici que pour définir la bisimulation forte 
sur les ITrees indexés, tu utilise le fait qu'ils sont définis comme
la colagèbre finale du foncteur $itree.F_Sigma$, et que tu vas donc
d'abord définir le lifting de ce foncteur aux relations.
Et pourquoi pas mettre une petite ref sur la définition de bisimulation
dans la théorie des coalgèbres.]

#tom[Dans la def ci-dessous, ça me met de la charge cognitive superflue d'avoir
$R^1$ et $R^2$ qui ne sont pas des relations. Tu pourrais ptet les appeler
$A^i$, comme "answer"?] 
#peio[Le pb c'est que j'utilise $R$ partout comme paramètre des itree (dès @sec-itree).
C'est pour "return type".. ]

#definition[Action Relator][
Given $Sigma cl icont.t th I$, an output relation $R^rel.r cl rel.irel th R^1 th
  R^2$, and a parameter relation $X^rel.r cl rel.irel th X^1 th X^2$, the
  _action relator over $Sigma$_ of type

  $ itree.RS th R^rel.r th X^rel.r
      cl rel.irel th (itree.F_Sigma th R^1 th X^1) th (itree.F_Sigma th R^1 th X^2) $

  is defined by the following data type.

  $ kw.dat itree.RS th R^rel.r th X^rel.r th {i} kw.whr \
    pat(itree.retR th {r^1 th r^2} th (r^rel.r cl R^rel.r th r^1 th r^2)
          cl itree.RS th R^rel.r th X^rel.r th (itree.retF th r^1) (itree.retF th r^2),
        itree.tauR th {t^1 th t^2} th (t^rel.r cl X^rel.r th t^1 th t^2)
          cl itree.RS th R^rel.r th X^rel.r th (itree.tauF th t^1) (itree.tauF th t^2),
        itree.visR
          th {q th k^1 th k^2}
          th (k^rel.r cl (r cl Sigma .icont.rsp th q) -> X^rel.r th (k^1 th r) (k^2 th r)) \
          quad cl itree.RS th R^rel.r th X^rel.r th (itree.visF th q th k^1) (itree.visF th q th k^2)) $
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
] <def-interaction-lattice>

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

This completes the basic theory of strong bisimulation: we have defined it and
proved its most important properties in @lem-sbisim-props, namely that when
$R^rel.r$ is well-behaved, not only it is an equivalence relation, but
bisimulation proofs can work up-to reflexivity, symmetry and transitivity.

#tom[Le @lem-sbisim-props ne parle pas directement des bisims, il parle de
$tower.t$. Est-ce que tu saurais rendre le lien plus clair à ce stade? ]
#guil[+1]

=== Weak Bisimilarity

As  previously hinted at, we wish to characterize a second notion of
bisimilarity, which would gloss over the precise number of silent #itree.tauF
moves of the two considered interaction trees. While strong bisimilarity will
play the role of (extensional) equality between trees, that is, a technical
tool, weak bisimilarity will play the role of a semantic equivalence.

To define weak bisimilarity, we will follow a similar route to strong bisimilarity, 
reusing the action relator, but when defining the monotone endo-map, we will insert
a gadget, allowing to skip over a finite number of silent moves. Let us define this
gadget. For readability, we will define a shorthand for trees where the top layer of
actions has been exposed:

#tom[Environment notation?]
$ itree.tp_Sigma th R := itree.F_Sigma th R th (itree.t_Sigma th R) $

#definition[Eating Relation][
  Given $Sigma cl icont.t th I$ and $R cl base.Type^I$, define the _eating relation_
  $itree.eat_Sigma^R cl rel.irel th (itree.tp_Sigma th R) th (itree.tp_Sigma th R)$ as follows.

  $ kw.dat th itree.eat_Sigma^R th {i} := \
    pat(itree.eatR th {t} cl itree.eat_Sigma^R th t th t,
        itree.eatS th {t_1 th t_2} cl itree.eat_Sigma^R th (t_1 .itree.obs) th t_2
         -> itree.eat_Sigma^R th (itree.tauF th t_1) th t_2) $

  We define the following shorthands:
  #let xx = $itree.eat_Sigma^R$
  $ itree.eatlr th := xx \
    itree.eatrl th := xx^rel.revS $
]

#tom[A nouveau je suis gêné par les conventions de nommage. Est-ce qu'on ne
pourrait pas appeler $A$ (par exemple...) les elements des $itree.F_Sigma th R
th X$? Comme ça, par ex, pour $itree.eatS$ on aurait $itree.eat_Sigma^R th (t
         .itree.obs) th A -> itree.eat_Sigma^R th (itree.tauF th t) th A$]

#tom[Il manque ici aussi une description intuitive de $itree.eat$.]

#guil[On est d'accord qu'un des point clé de $itree.eat$ c'est d'être défini par induction ?]

#lemma[
  For all $Sigma$ and $R$, the eating relation $itree.eat_Sigma^R$ is reflexive and
  transitive.
]
#proof[By direct induction.]

#definition[Weak Bisimilarity][ Given $Sigma cl icont.t th I$, we define the
  _weak bisimulation map over $Sigma$_ as the following monotone endo-map on the
  interaction relation lattice over $Sigma$ (@def-interaction-lattice). 
  
  #tom[Je me rends compte ici que le nom "interaction relation lattice" n'est
  pas ouf, pcq il ne m'évoque plus rien. Que pourrait être un bon nom? C'est
  quoi ce $rel.lat_Sigma$, au fond? C'est le treillis (paramétrique en le type
  des réponses) des relèvements de relations des réponses aux arbres
  d'interaction, c'est bien ça? Proposition: lattice of parametric relation
  liftings. ]

  #let xx = [$itree.eat_Sigma^R$]

  $ itree.wb_Sigma cl rel.lat_Sigma -> rel.lat_Sigma \
    itree.wb_Sigma th x th R^rel.r th t^1 th t^2 := \
      quad (cnorm(itree.eatlr) rel.seqS itree.RS th R^rel.r th (x th R^rel.r)
            rel.seqS cnorm(itree.eatrl)) th (t^1 .itree.obs) th (t^2 .itree.obs) $

#tom[Pareil, il manque une description intuitive.]

  We define heterogeneous and homogeneous _weak bisimilarity_ as follows.

  $ a itweq(R^rel.r) b := tower.nu th itree.wb_Sigma th R^rel.r th a th b \
    a de(approx) b := a itweq(rel.diagS) b $
]

#lemma[
  Given $Sigma cl icont.t th I$, for all $x in tower.t_(itree.wb_Sigma)$, the
  following statements hold.

  #let xx = [$R^rel.r$]

  $ R^rel.r_1 lt.tilde R^rel.r_2 -> x th R^rel.r_1 & lt.tilde x th R^rel.r_2 \
    rel.diagS & lt.tilde x th rel.diagS \
    (x th R^rel.r)^rel.revS & lt.tilde x th xx^rel.revS $

  In particular the weak bisimilarity $de(approx)$ is reflexive and symmetric.
] <lem-wbisim-props>
#proof[
  By direct tower induction, as for @lem-sbisim-props.
]

#tom[Bon, ok, mais on sait pas quel est le statut de ces propriétés... J'imagine
qu'intuitivement ces des propriétés de la bisim faible, surtout vue la phrase
ci-dessous, mais c'est pas clair pour moi en quel sens. ]

Notice that in the previous lemma, comparing with @lem-sbisim-props, we have
left out the statement regarding sequential composition of relations. Indeed it
is well-known that weak bisimulation up-to transitivity is not a valid proof
technique~#mcite(<PousS11>). However, we would still like to prove that weak
bisimilarity is transitive!
#tom[Une ref vers une preuve qu'on sait déjà que ça l'est?]
#guil[Je n'arrive pas à comprendre le lien
entre le "statement regarding sequential composition of relations" du 
@lem-sbisim-props, et la strong bisimulation up-to transitivity.]

#lemma[ Given $Sigma cl icont.t th I$ and $R^rel.r cl rel.irel th R th R$, if
  $R^rel.r$ is transitive, then so is $itweq(R^rel.r)$. ] 
  
#proof[ Pose the following shorthands, respectively for "one step
  synchronization then weak bisimilarity" and for one-step unfolding of weak
  bisimilarity.

  #tom[Environnement notation ?]

  #peio[rework symbols]
  #let sync = de(crel(math.attach(sym.approx, tr: "s")))
  #let weak = de(crel(math.attach(sym.approx, tr: "w")))
  #let eat = itree.eatlr
  #let eatr = itree.eatrl

  $ sync "" & := itree.RS th R^rel.r th itweq(R^rel.r) \
    weak "" & := cnorm(eat) rel.seqS cnorm(sync) rel.seqS cnorm(eatr) $

  We prove the following statements by direct induction on the eating relation
  for all $a, b, c$.
  
  1. $a eat itree.tauF th b sync c -> a sync c$
  2. $ a sync itree.tauF th b eatr c -> a sync c$

  #tom[On sait pas si tu vas prouver 1 et 2 ou passer à la suite. Ptet dire "we then observe..."? Bon, la preuve est un peu trop imbitable, je saute.]

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
    lemma 5. with lemma 6.
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

#lemma[Up-to Strong Bisimilarity][
  Given $Sigma cl icont.t th I$ and $R^rel.r cl rel.irel th R th R$, if $R$ is transitive,
  for all $x in tower.t_(itree.wb_Sigma)$,

  $ cnorm(iteq(R^rel.r)) rel.seqS x th R^rel.r rel.seqS cnorm(iteq(R^rel.r))
    lt.tilde x th R^rel.r $
]
#proof[
  Let us define the following shorthand.

  #peio[rework symbols]
  #let strong = de(crel(math.attach(sym.approx.eq, tr: "s")))
  #let sync = crel(math.attach(de(sym.approx), tr: de("s"), br: "x"))
  #let weak = crel(math.attach(de(sym.approx), tr: de("w"), br: "x"))
  #let eat = itree.eatlr
  #let eatr = itree.eatrl

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

  $ a & strong & b #h(0.6em) & eat    x_1 & sync x_2 & eatr  &  c #h(0.6em) & strong & d & \
    a & eat    & y_1  & strong x_1 & sync x_2 & strong&  y_2 & eatr   & d & quad "by 1. and 2." $

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

== Monad Structure <sec-itree-monad>

#peio[manque fmap]
An important structure available on interaction trees is that they form a monad.
Indeed, as they are parametrized by an _output_ family $R$, a strategy with
output $R$ can be considered as an impure computation returning some $R$.  Its
_effects_ will be to perform game moves and wait for an answer. While at first
sight---considering only the goal of representing game strategies---such an
output might seem unnecessary, the compositionality offered by monads, that is,
sequential composition, is tremendously useful to construct and reason on
strategies piece wise.

The monad structure on interaction trees takes place in the family category
$base.Type^I$ and its laws hold both w.r.t. strong bisimilarity and weak
bisimilarity. One way to view this is to say that I will define _two_ monads.
However, in line with my choice of using intensional type theory, I will first
define a _pre-monad_ structure, containing only the computationally relevant
operation and then provide two sets of laws.

In fact, in @def-itree, we have already defined the "return" operator,
$itree.ret$, which can be typed as follows.

$ itree.ret th {X} cl X => itree.t_Sigma th X $

Let us define the "bind" operator, which works by tree grafting.

#definition[Interaction Tree Bind][ 
  #margin-note[ Note that defining $itree.subst_f$ _with $f$ fixed_ is not a
    mere stylistic consideration.  Indeed, what it achieves, is to pull the
    binder for $f$ out of the coinductive definition. This enables the syntactic
    guardedness checker to more easily understand subsequent coinductive
    definitions making use of the bind operator. To the best of my knowledge,
    this trick was first used in the InteractionTree
    library~#num-cite(<XiaZHHMPZ20>). In general, it is always fruitful to take
    as many binders as possible out of a cofixpoint definition.
  ] Let $Sigma cl icont.t th I$. For any given $X, Y cl base.Type^I$ and $f cl X =>
  itree.t_Sigma th Y$, define _interaction tree substitution_ as follows.
  $ itree.subst_f cl itree.t_Sigma th X => itree.t_Sigma th Y \
    itree.subst_f th t :=
    pat(itree.obs := kw.case t .itree.obs \
      pat(itree.retF th x := (f th x) .itree.obs,
          itree.tauF th t := itree.tauF th (itree.subst_f th t),
          itree.visF th q th k := itree.visF th q th (kw.fun th r. th itree.subst_f th (k th r)))) $

  Then, define the _interaction tree bind_ operator as

  $ ar itree.bind ar th {X th Y th i} cl itree.t_Sigma th X th i -> (X => itree.t_Sigma th Y) -> itree.t_Sigma th Y th i \
    t itree.bind f := itree.subst_f th t $
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

$ ar rel.iarr ar cl rel.irel th X_1 th X_2 -> rel.irel th Y_1 th Y_2 -> rel.irel th (X_1 => Y_1) th (X_2 => Y_2) $
#v(-0.5em)
$ (R rel.iarr S) th f th g := forall th {i th x_1 th x_2}
 -> R th {i} th x_1 th x_2 -> S th {i} th (f th x_1) th (g th x_2) $
#tom[C'est texto le même que le précédent, il manque sans doute des $i$...]

$ rel.forall cl (forall th {i} -> rel.rel th (X_1 th i) th (X_2 th i)) -> rel.rel th (forall th {i} -> X_1 th i) th (forall th {i} -> X_2 th i) \
  (rel.forall th R) th f th g := forall th {i} -> R th (f th {i}) th (g th {i}) $

#tom[J'aurais dû me poser cette question avant, mais la notation $forall$ est-elle utilisée partout? Est-ce qu'il n'y a pas des endroits où tu utilises la syntaxe Agda? De plus, ici tu utilises un mix de la notation Agda et de la notation traditionnelle. D'après une brève inspection, ça ne semble pas très consistent. Mon classement perso pour le $forall$: 1. tradi, 2. Agda, 3. le mix ci-dessus.]

#tom[Et aussi, les énoncés avec $rel.forall$ sont un peu durs à lire, pcq on ne quantifie sur rien. Est-ce que ptet $integral^r$ marcherait mieux?]

Moreover we will write $rel.forall th A$ for $rel.forall th (kw.fun th {i}. th A)$.

#tom[Ci-dessous, c'est pas bon, j'essaie de corriger mais chuis pas sûr.] 

#lemma[ITree Monad Monotonicity][  Given $Sigma cl icont.t th I$, for any
  $X^rel.r$ and $Y^rel.r$ and for any $x cl rel.lat_Sigma$ such that either $x in
itree.sb_Sigma$ or $x in itree.wb_Sigma$, the following holds.

  1. $itree.ret xrel(X^rel.r rel.arr x th X^rel.r) itree.ret$
  2. $(ar itree.bind ar) xrel(rel.forall th x th X^rel.r rel.arr (X^rel.r rel.iarr x th Y^rel.r) rel.arr x th Y^rel.r) (ar itree.bind ar)$

  As a consequence, return and bind respect both strong and weak bisimilarity:
  3. $itree.ret xrel(X^rel.r rel.arr cnorm(iteq(X^rel.r))) itree.ret$
  4. $itree.ret xrel(X^rel.r rel.arr cnorm(itweq(X^rel.r))) itree.ret$
  5. $(ar itree.bind ar) xrel(rel.forall th cnorm(iteq(X^rel.r)) rel.arr (X^rel.r rel.iarr cnorm(iteq(Y^rel.r))) rel.arr cnorm(iteq(Y^rel.r))) (ar itree.bind ar)$
  6. $(ar itree.bind ar) xrel(rel.forall th cnorm(itweq(X^rel.r)) rel.arr (X^rel.r rel.iarr cnorm(itweq(Y^rel.r))) rel.arr cnorm(itweq(Y^rel.r))) (ar itree.bind ar)$
] <lem-up2bind>

#tom[C'est marrant, 1 et 2 ressemblent à des lois de monades pour $x$, c'est connu?]
#peio[C'est que c'est de la parametricité, du coup c'est normal (on a un ret relationel
  au dessus des 2 ret et un bind relationel au dessus des 2 bind). En vrai
  c'est les lois de compat du relator $x$ avec la monade, il faut que j'en parle plus. ]
#proof[

  1. Assuming $X^rel.r th x_1 th x_2$, we have $itree.sb_Sigma th x th X^rel.r
    th (itree.ret th x_1) th (itree.ret th x_2)$, which by @lem-tower-props
    entails $x th X^rel.r th (itree.ret th x_1) th (itree.ret th x_2)$. The
    proof for $x in itree.wb_Sigma$ is similar, using reflexivity of
    $itree.eat_Sigma^(R^rel.r)$.
  2. By tower induction on the statement. For $x in itree.sb_Sigma$ it is direct
     by unfolding and dependent pattern matching.
     For $x in itree.wb_Sigma$, use the following fact.
     $ t_1 itree.eatlr t_2 -> (t_1 itree.bind f) itree.eatlr (t_2 itree.bind f) $
  3--6. By direct application of 1--2, using @lem-tower-fix.
]

While perhaps not very impressive, the last lemma is very important. Points 3--6
prove that return and bind are well-defined as operators on the setoids of
strongly- and weakly-bisimilar strategies#guil[Tu n'as jamais parlé de setoid avant]. But more importantly, Point 2 proves
that, during a coinductive proof, in order to relate two sequential
compositions, it suffices to first relate the prefixes and then, pointwise, the
continuations. This fact is sometimes called "bisimulation up-to bind".

#lemma[ITree Monad Laws][
  Given $Sigma cl itree.t_Sigma$, for all $x cl X th i$, $t cl itree.t_Sigma th
  X th i$, $f cl X => itree.t_Sigma th Y$ and $g cl Y => itree.t_Sigma th Z$
  the following statements are true.

  1. $(itree.ret th x itree.bind f) itree.eq f th x$
  2. $(t itree.bind itree.ret) itree.eq t$
  3. $(t itree.bind f) itree.bind g itree.eq t itree.bind (f itree.kbind g)$
]
#tom[Attention, $itree.kbind$ undef!]
#proof[
  1. By one-step unfolding.
  2. By direct tower induction.
  3. By direct tower induction.
  #v(-2em)
]
#tom[Bon, j'ai pas assez de tower-fu pour savoir déplier ces instructions. Pour le 3, par exemple, il faut prendre quel prédicat? Faire un ou deux cas faciles ici aiderait ptet à suivre plus loin.]

This concludes the monadic theory of interaction trees. We will make some use of the
so-called "do notation", to write, e.g.,

$ kw.do x <- t; th y <- f th x; th g th y $

instead of

$ t itree.bind (kw.fun th x. th f th x itree.bind (kw.fun th y. th g th y)) $

$ t itree.bind funpat(short: #true, x |-> th f th x itree.bind funpat(short: #true, y |-> th g th y)) $

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


== Iteration Operators <sec-iter>

Interaction trees~#mcite(<XiaZHHMPZ20>) were originally introduced to encode
arbitrary---i.e., possibly non-terminating---computation. As such, apart from
monadic operators, they support _iteration operators_, which intuitively allow
one to write arbitrary "while" loops. Pioneered by Calvin #nm[Elgot] in the setting
of fixed points #tom[Homog: fixed points vs fixpoints] in algebraic
theories~#mcite(<Elgot75>), iteration in monadic computations enjoys a vast
literature. Recalling that a monadic term $a cl M th X$ can be understood as an
"$M$-term" with variables in $X$ #guil[Tu veux dire qu'on peut voir
$M$ comme une forme de signature?], the idea is to define systems of recursive
equations as morphisms

$ f cl X -> M th (X + Y), $

intuitively representing the system

$ x_1 & itree.weq f th x_1 \
  x_2 & itree.weq f th x_2 \
      & th dots.v \
  x_n & itree.weq f th x_n, $

#guil[Est-ce-que chaque $f th x_i$ ne peut utiliser que $x_i$
et pas les autres $x_j$ ? Ça me semble étrange.]

where each $f th x_i$ is an $M$-term mentioning either recursive variables $x_i
cl X$ or fixed parameters $y_i cl Y$. A _solution_ is then a mapping $s cl X ->
M th Y$ assigning to each "unknown" in $X$ an $M$-term mentioning only
parameters in $Y$. A solution must obviously satisfy the original equation
system, which in categorical language may be stated as follows.

$ s th x
  #h(1.4em) itree.weq #h(1.4em)
  f th x itree.bind
      funpat(gap: #0em,
          base.inj1 th x & |-> th s th x,
          base.inj2 th y     & |-> th itree.ret th y) $

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
some $x_i approx x_j$, has a _unique_ solution. The following variants have been defined:

- _iterative theories_, for terms in finitary algebraic theories~#mcite(dy:
  -4em, <Elgot75>),
- _iterative algebras_, for algebras associated to such theories~#mcite(dy: -2em, <Nelson83>),
- _completely iterative monads_, for _ideal_ monads, where there is a way to
    make sense of guardedness~#mcite(dy: -2.5em, <AczelAMV03>).
- _completely iterative algebras_, for functor algebras, with an adapted notion of _flat_
  equation system~#mcite(dy: -1em, <AdamekMV04>),

Absence of the prefix "completely" denotes the fact that only finitary equations are solved.
]

#tom[L'ordre choisi ici n'est pas clair, est-ce de plus général?]


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
of the "uniformity" axiom. The prefix "complete" has the same meaning as before.
]

More recently, several works have tried to unify the above two families, by
axiomatizing abstract _guardedness criteria_, for which guarded equations have a
coherent choice of solution~#mcite(<GoncharovRP17>)~#mcite(dy: 4em,
<MiliusL17a>). This criterion may be syntactic as in the first family, or
vacuous (every equation is considered guarded) as in the second
family. The iteration operator may then be axiomatized to be coherent in the
style of iteration or #nm[Elgot] monads, and uniqueness of solutions may be framed as
the most restrictive of these coherence conditions. #tom[La phrase précédente
n'est pas claire, je pense. ] For the type theory practitioner seeking a modern
account, I recommend in particular #nm[Goncharov] et al.~#num-cite(<GoncharovRP17>),
which also features much appreciated graphical depictions of the coherence laws.

#tom[Ouf! On se retrouve à la fin d'un paragraphe d'into fleuve, sans du tout savoir ce qui nous attend pour cette partie...]

=== Unguarded Iteration

In the original interaction tree library~#mcite(<XiaZHHMPZ20>), an iteration
_operator_ has been devised, which constructs fixed points of arbitrary equation
systems up to weak bisimilarity. This makes the interaction tree monad
quotiented by weak bisimilarity into a complete #nm[Elgot] monad.

For readability, let us introduce two helpers for copairing. First the usual one:
given $f cl X => itree.t_Sigma th A$ and $g cl Y => itree.t_Sigma th A$, define
$[f,g] cl (X + Y) => itree.t_Sigma th A$ by


$ de([bk(f), bk(g)]) := funpat(base.inj1 th x & |-> f th x,
                  base.inj2 th y & |-> g th x) $

$ de([bk(f), bk(g)]) th (base.inj1 th x) & := f th x \
  [f, g] th (base.inj2 th y) & := g th x $

given $f cl X => itree.tp_Sigma th A$ and $g
  cl Y => itree.tp_Sigma th A$ #margin-note[ Please note the one-step unfolding
  in the codomain!#tom[codomain?! y a une typo ici ou dans le codomaine?]
  #guil[c'est le codomaine de $f$ et $g$ non ?]
  Moreover, let us emphasise that this definition pattern-matches on its
  argument lazily, i.e. only _after_ being observed.  Indeed, a general trick to
help satisfy guardedness is to copattern-match on $.itree.obs$ as early as
possible.  ], define the following copairing of arrows $f itree.copr g cl (X +
Y) => itree.t_Sigma th A$ by

#tom[J'aime pas la notation pour le copairing, pcq traditionnellement on utilise
les symboles d'opérateurs sur les flèches comme agissant à la fois côté domaine
et codomaine, genre $f+g cl A + B -> C + D$.]

$ (f itree.copr g) th r :=
    pat(itree.obs := kw.case r \
      pat(base.inj1 th x & := f th x,
          base.inj2 th y & := g th y)) $


#definition[Interaction Tree Iteration][
  Let $Sigma cl icont.t th I$. Given an equation $f cl X => itree.t_Sigma th (X
  + Y)$, define its _iteration_ coinductively as follows.

  $ itree.iter_f cl X => itree.t_Sigma th Y \
    itree.iter_f th x := f th x itree.bind ((kw.fun th t |-> itree.tauF (itree.iter_f th t)) itree.copr itree.retF) $
] <def-iter>

#lemma[Iter Fixed Point][ \
  Given $Sigma cl icont.t th I$, for all $f cl X =>
  itree.t_Sigma th (X + Y)$, $itree.iter_f$ is a weak fixed point of $f$, i.e.,
  the following holds.

  #let bk(it) = text(fill: black, it)
  $ itree.iter_f th x
    itree.weq
    f th x itree.bind
        funpat(gap: #0em,
               base.inj1 th x & |-> th itree.iter_f th x,
               base.inj2 th y & |-> th itree.ret th y) $
]
#proof[
  By straightforward tower induction, using the up-to bind principle (@lem-up2bind).
]

Furthermore, we prove the following monotonicity statement for iteration.

#lemma[Iter Monotonicity][ \
  Given $Sigma cl icont.t th I$, for all $X^rel.r cl rel.irel th X^1 th X^2$ and
  $Y^rel.r cl rel.irel th Y^1 th Y^2$, the following statements holds.

  1. $ itree.iter xrel((X^rel.r rel.iarr iteqn(X^rel.r + Y^rel.r)) rel.arr (X^rel.r rel.iarr iteqn(Y^rel.r))) itree.iter $
  2. $ itree.iter xrel((X^rel.r rel.iarr itweqn(X^rel.r + Y^rel.r)) rel.arr (X^rel.r rel.iarr itweqn(Y^rel.r))) itree.iter $
] <lem-iter-mon>
#proof[
  By straightforward tower induction, using the up-to bind principle (@lem-up2bind).
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
#tom[C'est aussi le passage à la bisim forte qui gagne, non?]

=== Guarded Iteration

A general trend in the research on iteration operators is the observation that,
very often, the unguarded iteration operator of, e.g., an #nm[Elgot] monad, may be
shown to somehow derive from an underlying guarded iteration operator enjoying
unique fixed points, with the former monad typically being a quotient of the
latter.  With interaction trees, we find ourselves exactly in this situation.
Indeed, as we will see, every equation system is weakly bisimilar to a guarded
equation. Our previous unguarded iteration operator can then be seen as
constructing the unique fixed point of this new guarded equation, up to strong
bisimilarity.#margin-note[In hindsight, this is rather unsurprising since we
work in a total programming language: tautologically, only uniquely defined
objects can ever be defined. #tom[Mmm... what?!] #yann[Pas mieux que Tom.]] Without further ado, let us
define this guarded iteration operator.

#definition[Guardedness][ Let $Sigma cl icont.t th I$. An action is _guarded in
  $X$_ if it satisfies the following (proof-relevant) predicate.

  $ kw.dat itree.actguard th {X th Y th A th i} cl itree.F_Sigma th (X + Y) th A th i -> base.Type kw.whr \
    pat(itree.gret th {y} & cl itree.actguard th (itree.retF th (base.inj2 th y)),
        itree.gtau th {t} & cl itree.actguard th (itree.tauF th t),
        itree.gvis th {q th k} & cl itree.actguard th (itree.visF th q th k)) $

  Furthermore, an itree is _guarded in $X$_ if its observation is:
  
  #tom[Je crois pas que t'aies parlé d'itree dans le texte jusqu'ici. Tu devrais
ptet dire "strategy"?]

  $ itree.guard th {X th Y th i} cl itree.t_Sigma th (X + Y) th i -> base.Type \
    itree.guard th t := itree.actguard th t .itree.obs . $

  And, finally, guardedness of equations is defined pointwise:

  $ itree.eqguard th {X th Y th i} cl (X => itree.t_Sigma th (X + Y)) -> base.Type \
    itree.eqguard th f := forall th {i} th {x cl X th i} -> itree.guard th (f th x) . $
] <def-guarded>

#lemma[Unique Guarded Fixed Points][
  Given $Sigma cl icont.t th I$ and a guarded equation $f cl X =>
  itree.t_Sigma th (X + Y)$, for any two fixed points $s_1, s_2$ of
  $f$ w.r.t. strong bisimilarity, i.e., such that for all $x$ and $i = 1, 2$ we have

  $ s_i th x
    itree.eq
    f th x itree.bind
        funpat(gap: #0.2em,
        base.inj1 th x & |-> th s_i th x,
        base.inj2 th y & |-> th itree.ret th y) quad , $
  then for all $x$, $s_1 th x itree.eq s_2 th x$.
] <lem-gfix-uniq>
#proof[
  #yann[Tu as des fois des curly, des fois des squares brackets pour tes match.]
  By tower induction. Apply both fixed point hypotheses. The goal is now to prove
    $ (f th x itree.bind
        funpat(gap: #0em,
        base.inj1 th x & |-> th s_1 th x,
        base.inj2 th y & |-> th itree.ret th y)) \
    quad quad xrel(itree.sb_Sigma th c th rel.diagS) \
    (f th x itree.bind
        funpat(gap: #0em,
        base.inj1 th x & |-> th s_2 th x,
        base.inj2 th y & |-> th itree.ret th y))
  $

  for some $c$ the chain #tom[quantifier sur $c$ plus explicitement, ou mieux,
  l'introduire juste après le "by tower induction"]. By inspecting the first
  step of $f th x$, by guardedness we obtain a synchronization and it suffices
  to prove

  $ (t itree.bind
        funpat(gap: #0em,
        base.inj1 th x & |-> th s_1 th x,
        base.inj2 th y & |-> th itree.ret th y))
    xrel(c th rel.diagS)
    (t itree.bind
        funpat(gap: #0em,
        base.inj1 th x & |-> th s_2 th x,
        base.inj2 th y & |-> th itree.ret th y))
  $

  for some interaction tree $t$. The coinduction hypothesis states
  $ forall th x -> s_1 th x xrel(c th rel.diagS) s_2 th x, $

  we can conclude using up-to bind (@lem-up2bind). 
]

#definition[Guarded Iteration][
  Let $Sigma cl icont.t th I$. Given an equation $f cl X =>
  itree.t_Sigma th (X + Y)$ with guardedness witness $H cl itree.eqguard th f$,
  we define _guarded iteration_ by the following mutually defined coinductive
  functions.

  $ itree.giter cl X => itree.t_Sigma th Y \
    itree.giter x := \
    pat(itree.obs := kw.case (f th x) .itree.obs | H th x \
    pat((itree.retF th (base.inj1 x)) & th (!) & #hide($:=$),
        (itree.retF th (base.inj2 y)) & th p  & := itree.retF th y,
        (itree.tauF th t)             & th p  & := itree.tauF th (t itree.bind ()),
        (itree.visF th q th k)        & th p  & := itree.visF th q th (kw.fun th r |-> th g th (k th r)))) $

  $ itree.gstep_(f,H) cl (itree.t_Sigma (X + Y) => itree.t_Sigma th Y) -> (X => itree.tp_Sigma th Y) \
    itree.gstep_(f,H) th g th x := kw.case (f th x) .itree.obs | H th x \
    pat((itree.retF th (base.inj1 x)) & th (!) & #hide($:=$),
        (itree.retF th (base.inj2 y)) & th p  & := itree.retF th y,
        (itree.tauF th t)             & th p  & := itree.tauF th (g th t),
        (itree.visF th q th k)        & th p  & := itree.visF th q th (kw.fun th r |-> th g th (k th r))) $

  #yann[Je crois que tu as enlevé l'instance précédente où Tom avait mentionné ne pas connaitre la notation Agda de raffinement des matchs dépendents, mais du coup le problème doit être décalé à ici. Il faudrait peut-être introduire la notation à un moment, ou juste ajouter une phrase ici pour aider au déchiffrement.]

  We then define the following coinductive auxiliary function.
  #margin-note[
    In fact the two definitions $itree.giter^de("aux")$ and $itree.giter$ can be seen as
    two mutually defined coinductive functions. However, I have refrained
    from using mutual coinduction, for the simple reason that Coq does not
    support it. Instead, I have presented a version where the definition of $itree.giter$
    is inlined in $itree.giter^de("aux")$. Doing the reverse, and
    skipping $itree.giter^de("aux")$ altogether, is not possible because Coq
    does not recognize it as syntactically guarded! I am curious to see what Agda's
    guardedness checker thinks of this... #tom[Incompréhensible pour moi, et je pense que je devrais comprendre. Comment Coq reconnait-il que  $itree.giter^de("aux")$? Il fait une étape de $beta$?]
  ]

  $ itree.giter^de("aux")_(f,H) cl itree.t_Sigma th (X + Y) => itree.t_Sigma th Y \
    itree.giter^de("aux")_(f,H) th t := t itree.bind (itree.gstep_(f,H) th itree.giter^de("aux")_(f,H) itree.copr itree.retF)
  $

  Finally, we define the _guarded iteration_ as follows.

  $ itree.giter_(f,H) cl X => itree.t_Sigma th Y \
    itree.giter_(f,H) := itree.gstep_(f,H) th itree.giter^de("aux")_(f,H) $

  We will omit the guardedness witness $H$ when clear from context.
] <def-giter>

#tom[Environnement remarque?]
While a bit scary, the above definition of $itree.gstep$ is simply mimicking the first
step of a "bind" on $f th x$, and thanks to the added information from guardedness,
it is able to only trigger subsequent computation in a guarded fashion. Recall that
for unguarded iteration, this guardedness was achieved artificially, by wrapping the
whole call in a silent step.

#theorem[Guarded Fixed Point][
  Let $Sigma cl icont.t th I$. For any guarded equation $f cl X =>
  itree.t_Sigma th (X + Y)$, $itree.giter_f$ is the unique fixed point of
  $f$ w.r.t. strong bisimilarity.
] <lem-giter-fix>
#proof[
  Since by @lem-gfix-uniq guarded fixed points are unique w.r.t. strong
  bisimilarity, it suffices to show that it is indeed a fixed point.
  We generalize to the following statement.

  $ itree.giter^de("aux")_f th t
    itree.eq t itree.bind
        kw.fun text(colors.kw, cases(gap: #0.2em,
        bk(base.inj1 th x. th itree.giter_f th x),
        bk(base.inj2 th y. th itree.ret th y))) $

  It is proven by direct tower induction, using up-to bind.
]

We have thus exhibited interaction trees (considered up to strong bisimilarity)
as a completely iterative monad. Let us now link this to unguarded iteration.

#tom[Le point 1 du lemme suivant me semble louche. Si je prends $X = 1$, $Y = 2$
et pour $f$ le contre-exemple du papier, alors toute map $1 -> itree.t_Sigma 2$
est solution, donc je vois pas trop comment ça peut marcher. Je rate un truc?]
#yann[Je suis d'accord, ça m'a l'air faux.]

#lemma[
  Given $Sigma cl icont.t th I$ and an equation $f cl X =>
  itree.t_Sigma th (X + Y)$

  1. If $s$ is a fixed point of $f$ w.r.t. strong bisimilarity, then $s
     itree.weq itree.iter_f$.
  2. Let $f' th x := f itree.bind (itree.tauF itree.copr itree.retF)$. Then,
     $f'$ is guarded and $itree.giter_f' th x itree.eq itree.iter_f th x$.  ]
<lem-iter-giter> #proof[Both by straightforward tower induction.]

=== Eventually Guarded Iteration

Equipped with this new guarded iteration, we finally obtain our powerful
uniqueness of fixed points. This principle will provide us with a big hammer,
very useful for hitting nails looking like $itree.giter_f th x itree.eq t th x$.
However, being guarded is quite a strong requirement! Notably, our equation of
interest in this thesis, the one defining interaction of OGS strategies and counter-strategies, has no hope of being
guarded. However, observe that if there is a finite chain $x_1 ↦ x_2 ↦
... ↦ x_n ↦ t$, such that $t$ is guarded, then after $n$ iteration
step, $x_1$ will be mapped to a guarded $t$. The iteration starting from $x_1$
is then still uniquely defined. This was already noted by #nm[Adámek],
#nm[Milius] and #nm[Velebil]~#mcite(<AdamekMV10>) with their notion of
_grounded_ variables. However, a clear definition and study of equations
containing only grounded variables, or _eventually guarded equations_ as I call
them, is still novel to the best of my knowledge. In fact, in future work it
might be fruitful to consider this in the setting of~#mcite(<GoncharovRP17>) as
a generic relaxation of any abstract guardedness criterion. #tom[Hyphen moisis
dans la marge ci-contre!]

#definition[Eventual Guardedness][ Let $Sigma cl icont.t th I$ and $f cl X =>
  itree.t_Sigma th (X + Y)$. An interaction tree is _eventually guarded w.r.t.
  $f$_ if it verifies the following inductive predicate $itree.evguard_f$,
  defined by mutual induction as follows.

  $ kw.dat itree.actevguard_f th {i} cl itree.tp_Sigma th (X + Y) th i -> base.Type kw.whr \
    quad itree.evg th {t} cl itree.actguard th t -> itree.actevguard_f th t \
    quad itree.evs th {x} cl itree.evguard_f th (f th x) -> itree.actevguard_f th (itree.retF th (base.inj1 th x)) $

  $ itree.evguard_f th {i} cl itree.t_Sigma th (X + Y) th i -> base.Type \
    itree.evguard_f th t := itree.actevguard_f th t .itree.obs $

  An equation is _eventually guarded_ if it is pointwise eventually guarded
  w.r.t. itself.

  $ itree.eqevguard th {X th Y th i} cl (X => itree.t_Sigma th (X + Y)) -> base.Type \
    itree.eqevguard th f := forall th {i} th (x cl X th i) -> itree.evguard_f th (f th x) $
] <def-guarded>

#tom[Le lemme ci-dessous doit être raté, on n'a pas encore défini $itree.eviter$. J'essaie de corriger mais tu vérifies, Peio, ok?]
#lemma[Uniqueness of Eventually Guarded Fixed Points][
  Given $Sigma cl icont.t th I$ and $f cl X => itree.t_Sigma th (X + Y)$ such that
  $f$ is eventually guarded, for any fixed points $g$ and $h$ of $f$ w.r.t.
  strong bisimilarity, for all $x$, we have $g th x itree.eq h th x$.
] <lem-evfix-uniq>
#proof[
  By tower induction, then by induction on the eventual guardedness proof.
]

To construct eventually guarded fixed points, we will reduce them to the problem
of computing a guarded fixed point. Indeed by definition, any eventually guarded
equation can be pointwise unrolled into a guarded one.

#definition[Unrolling][ Let $Sigma cl icont.t th I$. Given $f cl X =>
  itree.t_Sigma th (X + Y)$ and eventually guarded $t$ w.r.t. $f$, define the
  _unrolling of $t$_ as the following inductive definition.

  $ itree.evunroll_f th {i} th (t cl itree.tp_Sigma th (X + Y) th i) cl itree.actevguard_f th t -> itree.tp_Sigma th (X + Y) th i $
  #v(-0.4em)
  $ & itree.evunroll_f th (itree.retF th (base.inj1 th x)) th && (itree.evs th p) & := & itree.evunroll_f th (f th x).itree.obs th p \
    & itree.evunroll_f th (itree.retF th (base.inj2 th y)) th && p & := & itree.retF th (base.inj2 th y) \
    & itree.evunroll_f th (itree.tauF th t) th && p & := & itree.tauF th t \
    & itree.evunroll_f th (itree.visF th q th k) th && p & := & itree.visF th q th k $

  Moreover, define the following _pointwise unrolling_ of $f$.

  $ itree.equnroll_f cl itree.eqevguard th f -> (X => itree.t_Sigma th (X + Y)) \
    (itree.equnroll_f th H th x) .itree.obs := itree.evunroll_f th (f th x).itree.obs th (H th x) $
]

#lemma[Unroll Guarded][
  Given $Sigma cl icont.t th I$ and $f cl X => itree.t_Sigma th (X + Y)$ such that
  $H cl itree.eqevguard th f$, then $itree.equnroll_f th H$ is guarded.
]
#proof[By direct induction.]

#definition[Eventually Guarded Iteration][
  Given $Sigma cl icont.t th I$ and $f cl X => itree.t_Sigma th (X + Y)$ such that
  $H cl itree.eqevguard th f$, define the _eventually guarded iteration of $f$_ as follows.

  $ itree.eviter_(f,H) cl X => itree.t_Sigma th Y \
    itree.eviter_(f,H) := itree.giter_(itree.equnroll th f th H)$
]

It now remains to verify that this construction is indeed a fixed point
of $f$ (in addition to being a fixed point of the unrolled equation).

#theorem[Eventually Guarded Fixed Point][
  Given $Sigma cl icont.t th I$ and $f cl X => itree.t_Sigma th (X + Y)$ such that
  $f$ is eventually guarded, then $itree.eviter_f$ is the unique fixed point of $f$ w.r.t.
  strong bisimilarity.
] <thm-eviter-fix>

#proof[ By @lem-evfix-uniq, eventually guarded fixed points are unique w.r.t.
  strong bisimilarity, so it suffices to prove that $itree.eviter_f$ is a fixed
  point of $f$. We first observe that eventual guardedness is provably
  irrelevant:

  $ forall th (p, q cl itree.evguard_f th t) -> p = q. $

  This observation will help us to change the eventual guardedness witness, on which
  computation of the unrolling depends. 
  
  Next, we observe by one step unfolding, and using the previous observation,
  that whenever we have

  $ (f th x_1) .itree.obs = itree.retF th (base.inj1 th x_2), $

  then the following also holds:

  $ itree.eviter_f th x_1 itree.eq itree.eviter_f th x_2. $

  Then, prove the goal by one-step unfolding and case analysis.
]

Since @lem-iter-giter links any strong fixed point of $f$ with the usual unguarded
iteration $itree.iter_f$, we already know that for an eventually guarded equation $f$,
$itree.eviter_f itree.weq itree.iter_f$. This concludes our study of eventually
guarded iteration. In fact, @thm-eviter-fix is the crucial building block that our
correctness proof of OGS will rest upon, and it concludes this chapter.

#peio[Et delay alors?]

=== Categorical Structure

In order to make (half-)games into a proper category, we need to define
morphisms. We define them as "translations" between moves, coherent with
respect to positions.

#definition[Half-Game Morphism][
  Given $I, J cl base.Set$ and $A, B cl game.hg th I th J$, a _morphism between $A$ and $B$_
  is given by the following record.
  $ & kw.rec th game.hsim th A th B kw.whr \
    & quad game.hstr {i} cl A.game.mv th i -> B.game.mv th i \
    & quad game.hscoh {i} th (m cl A.game.mv th i) cl B.game.nx th (game.hstr m) = A.game.nx th a $
]
#definition[Game Morphism][
  Given $I^+, I^- cl base.Set$ and $A, B cl game.g th I^+ th I^-$, a _morphism
  between $A$ and $B$_ is given by the following record.
  $ & kw.rec th game.sim th A th B kw.whr \
    & quad game.scli cl game.hsim th A.game.client th B.game.client \
    & quad game.ssrv cl game.hsim th B.game.server th A.game.server $
]

For each pair of sets of positions, we now have two categories of half-games
and games. The construction of half-games is functorial on the sets of positions,
as witnessed by the following reindexing.

#definition[Half-Game Reindexing][
  Given two functions $f cl I_2 -> I_1$ and $g cl J_1 -> J_2$ and a half-game
  $A cl game.hg th I_1 th J_2$, we define the game $[ f angle.r A angle.l g ] cl
  game.hg th I_2 th J_2$ as follows.
  $ & [ f angle.r A angle.l g ] .game.mv th i := A.game.mv th (f th i) \
    & [ f angle.r A angle.l g ] .game.nx th m := g th (A.game.nx th m) $
]

Reindexing extends to a functor 
As identity and composition laws for reindexing hold up to definitional
equality (assuming $eta$ equality of functions), this reindexing extends
half-games into a strict functor $game.hg cl base.Set^"op" -> base.Set ->
base.Cat$.

#definition[Game Reindexing][
  Given two functions $f^+ cl I^+_2 -> I^+_1$ and $f^- cl I^-_1 -> I^-_2$ and a
  game $A cl game.g th I^+_1 th I^-_1$, we define the game $[ f^+ angle.r A
  angle.l f^- ] cl game.g th I^+_2 th I^-_2$ as follows.
  $ & [ f^+ angle.r A angle.l f^- ] .game.client := [ f^+ angle.r A.game.client angle.l f^- ] \
    & [ f^+ angle.r A angle.l f^- ] .game.server := [ f^- angle.r A.game.server angle.l f^+ ] $
]

=== A Couple Constructions



=== Comparison

*Transition Systems over Games* #sym.space.quad The definition of games we have ended up with (@hg) was in fact already present
in the litterature, namely as _discrete games_ in Paul Levy and Sam Staton's
"Transition systems over games"~#mcite(<LevyS14>). My work is very much in line
with this paper and many more references to it will appear throughout this
chapter. Much like me, their motivation is to construct _transition systems_
over these games, something I will call _strategies_. The main difference with
their work, is that they rapidely introduce a categorical generalization, where
the positions $I^+$ and $I^-$ are not sets but categories. In this
generalizations, my half-games can be reworded as functors $A -> "Fam" th B$.
These can be assembled into the hom-categories of a bicategory
which~#mcite(<LackS02>, supplement: [pp.~261--264]) proves biequivalent to the
bicategory of two-dimensional partial maps, i.e. spans of small categories
where the left leg is a discrete op-fibration.

There is a bit more to say to the biequivalence with spans. Indeed, in our case
too, half-games can be assembled into a bicategory where objects are sets and
hom-categories are half-games. I will call the 


This bicategory is again biequivalent to the
bicategory of spans of sets. And in fact, in type theory spans are known to be
encoded by proof-relevant relations.
Moreover, relations are well-known in the game semantics litterature to form
the basis of numerous models of linear logic~#mcite(<HylandS99>).
As such, one could ask the question: why
did I not take half-games to be given by some $M cl I -> J -> base.Set$?


#definition[Extension of a Half-Game][
  Given $E cl game.hg th I th J$, we define respectively the _active_ and
  _passive_ extension functors $E game.extA -$ and $E game.extP -$
  of type $base.Set^I -> base.Set^J$ by:
  $ & (E game.extA X) th j := (m cl game.mv_E th j) times X th (game.nx_E th m) \
    & (E game.extP X) th j := (m cl game.mv_E th j) -> X th (game.nx_E th m) $
]


== Indexed Interaction Trees <sec-itree>

Hello Interaction trees~#mcite(<XiaZHHMPZ20>)

#definition[Indexed Container][
  Given $I, J cl base.Set$ an _event structure_, or _indexed container with input $I$ and output $J$_
  is a record defined as follows.
  $ & kw.rec th icont.t th I th J th kw.whr \
    & quad icont.qry cl I -> base.Set \
    & quad icont.rsp th {i cl I} : icont.qry th i -> base.Set \
    & quad icont.nxt th {i cl I} th {q cl icont.qry th i} cl icont.rsp th q -> J
  $
]

#definition[Extension of an Indexed Container][
  The _extension_ of an indexed container $E cl icont.t th I th J$ is a functor
  $icont.ext_E cl base.Set^J -> base.Set^I$ given by the following definition.
  $ & kw.rec th icont.ext_E th X th i th kw.whr \
    & quad icont.eqry cl E.icont.qry th i \
    & quad icont.ekon cl (r cl E.icont.rsp th icont.eqry) -> X th (E.icont.nxt th r) $
]

#definition[Interation Step Functor][
  Given an indexed container $E cl icont.t th I th I$
  we define the functor $itree.F_E cl base.Set^I -> base.Set^I -> base.Set^I $ by
  $ & kw.dat th itree.F_E th R th A th i th kw.whr \
    & quad itree.retF th (r cl R th i) \
    & quad itree.tauF th (t cl A th i) \ 
    & quad itree.visF th (e : icont.ext_E th A th i) $
]

#definition[Interaction Coalgebra][
  Given an indexed container $E cl icont.t th I th I$, an interaction coalgebra
  is a record defined by:
  $ & kw.cls th itree.coalg_E th R th (S cl base.Set^I) th kw.whr \
    & quad itree.out cl S => itree.F_E th R th S $
]

#definition[Interation Tree][
  Given an indexed container $E cl icont.t th I th I$,
  the parametrized family of _interaction trees with events $E$_, $itree.t_E cl
  base.Set^I -> base.Set^I$ is given by the following coinductive type:
  $ & kw.rec th itree.t_E th R th i th kw.whr \
    & quad itree.obs cl itree.F_E th R th (itree.t_E th R) th i $

  It has a natural interaction coalgebra structure.
  $ & kw.ins th itree.coalg_E th R th (itree.t_E th R) \
    & quad itree.out := itree.obs $
]

=== Monad Structure <sec-itree-monad>

#definition[Generalized Substitution][
  $ & itree.subst inst(itree.coalg_E th R_1 th S) th (k cl R_1 => itree.t_E th R_2) cl S => itree.t_E th R_2 \
    & (itree.subst th k th s) .itree.obs kw.wit s .itree.out \
    & quad | itree.retF r := k th r \
    & quad | itree.tauF t := itree.tauF (itree.subst th k th t) \
    & quad | itree.visF (e, th m) := itree.visF (e, th lambda r. itree.subst th k th (m th r)) $
]

//#definition[]


=== Bisimilarity <sec-itree-bisim>

#lorem(10)#margin-note[#lorem(20)] #lorem(10)

== The Case of Iteration <sec-iter>

=== Iteration Operators and their Axioms

=== (Eventual) Guardedness

== From Containers to Games <sec-hgames>

=== In Search of Symmetry

=== Transition Systems over Games


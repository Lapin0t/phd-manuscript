#import "/lib/all.typ": *

= Coinductive Game Strategies

As we have seen, Operational Game Semantics, and more generally interactive
semantics, rest upon a dialogue following particular rules, a so-called game.
The main task in this chapter will be to properly define what is meant by a
"game", "strategy", "transition system", and to provide basic building blocks
for manipulating them. This chapter thus takes a step back and temporarly puts
on hold our concerns about programming language semantics, in order to
introduce tools, to concretely represent games and strategies in type theory.
These tools are in part novel, but consist mostly of natural extensions of
pre-existing devices.

== A Matter of Computation

At heart, a strategy for a given two player game is an automaton of some kind,
in the loose sense that it has some internal state, a memory, and alternates
between two kinds of transitions, the ones where the strategy chooses a move to
play and the ones where it reacts to a move---any possible move---made by a
hypothetic opponent. In the classical literature on automata, but also in most
of the literature specifically dedicated to game semantics, these transitions
are typically modelled by _relations_, which in type theory would translate as
binary predicates. While perfectly doable, this approach has a serious
drawback: computability. In type theory, there is a very clear distinction
between a functional relation and an actual function and one cannot go from the
former to the latter. As such, going with relations to represent transitions

WIP, pas très satisfaisant.

Aussi présenter:

- hancock interaction structures
- interaction trees
- capretta delay monad
- coinductive resumption monad

== Indexed Interaction Trees

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

=== Monad Structure

#definition[Generalized Substitution][
  $ & itree.subst inst(itree.coalg_E th R_1 th S) th (k cl R_1 => itree.t_E th R_2) cl S => itree.t_E th R_2 \
    & (itree.subst th k th s) .itree.obs kw.wit s .itree.out \
    & quad | itree.retF r := k th r \
    & quad | itree.tauF t := itree.tauF (itree.subst th k th t) \
    & quad | itree.visF (e, th m) := itree.visF (e, th lambda r. itree.subst th k th (m th r)) $
]

//#definition[]


=== Bisimilarity

#lorem(10)#margin-note[#lorem(20)] #lorem(10)

== The Case of Iteration

=== Iteration Operators and their Axioms

=== (Eventual) Guardedness

== From Containers to Games

=== In Search of Symmetry

#definition[Half-Game][
  Given $I, J cl base.Set$ a _half-game with input $I$ and output $J$_
  is a record defined as follows.
  $ & kw.rec th game.hg th I th J th kw.whr \
    & quad game.mv cl J -> base.Set \
    & quad game.nx th {j cl J} cl game.mv th j -> I $
]

#definition[Extension of a Half-Game][
  Given $E cl game.hg th I th J$, we define respectively the _active_ and
  _passive_ extension functors $E game.extA -$ and $E game.extP -$
  of type $base.Set^I -> base.Set^J$ by:
  $ & kw.rec (E game.extA X) th j th kw.whr \
    & quad game.emv cl game.mv_E th j \
    & quad game.sleep cl X th (game.nx_E th game.emv) \
    & \
    & (E game.extP X) th j := (m : game.mv_E th j) -> X th (game.nx_E th m) $
]

=== Transition Systems over Games

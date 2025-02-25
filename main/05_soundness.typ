#import "/lib/all.typ": *

= OGS Correctness Proof <ch-proof>

In @ch-ogs we have constructed the OGS model, interpreting configurations of a
language machine into OGS strategies. Then we have given the correctness
theorem (@thm-correctness), stating that when two configurations are equivalent in the OGS model
(i.e., when they have weakly bisimilar strategies), then they are _substitution
equivalent_, the concretization of observational equivalence for language
machines. The current chapter is now devoted to providing the actual proof of
this statement.

For the entirety of this chapter, we will globally assume all of the hypotheses
of the correctness theorem. Hence we assume given

- a scope structure $ctx.scope_T th S$,
- a binding family $O cl ctx.bfam th S th T$,
- a substitution monoid of values $V cl base.Type^(S,T)$ with decidable variables
- a substitution module over values of configurations $C cl base.Type^S$
- a language machine $M cl ogs.machine th O th V th C$ which respects substitution
  and which has finite redexes,
- a final scope $Omega cl S$.

Spelled out more formally, we assume given elements of the following typeclasses.
#block(inset: (x: 0.5em), mathpar(
  $sub.mon th V$, $sub.decvar th V$, $sub.mod_V th C$, $ogs.submachine th M$, $ogs.finred th M$
))

== Proof Outline

We have already somewhat hinted at the proof strategy and the most important
lemmas in various places. Let us recapitulate the blueprint. To prove the correctness,
we will do a detour on composition, as indeed correctness follows
from two properties of composition, _congruence_ and _adequacy_.

#definition[Congruence for Composition][
  Weak bisimilarity is a _congruence_ for composition if for all $Psi cl ctx.ctxc th S$,
  $s^+_1, s^+_2 cl ogs.stratA th Omega th Psi$ and $s^- cl ogs.stratP th
  Omega th Psi$, the following property holds.

  $ s^+_1 itree.weq s^+_2 -> (s^+_1 game.par s^-) itree.weq (s^+_2 game.par s^-) $
] <def-compo-congr>

#definition[Adequacy of Composition][
  The composition operator is _adequate_ if for all $Gamma cl S$, $c cl C th Gamma$
  and $gamma cl Gamma asgn(V) Omega$, the following property holds.

  $ ogs.evalo th c[gamma] itree.weq (ogsinterpA(c) game.par ogsinterpP(gamma)) $
]

Congruence is quite straightforward to prove, it is yet another instance of
our hard to read and boring relational statements! The most important
task is the proof of adequacy. The idea to prove adequacy boils down to two
arguments: first we show that $kw.fun th c th gamma |-> ogs.evalo th c[gamma]$
is a fixed point of the composition equation and second we show that the
composition equation is eventually guarded, hence has unique fixed points. At
this point however, $ogs.evalo$ being a fixed point of composition does not
make much sense, since the composition equation operates on pairs of OGS
strategies while $ogs.evalo$ takes a configuration and an assignment. To fix
this issue we will make two patches, respectively bringing composition and
$ogs.evalo$ to a common meeting point: pairs of machine strategy states.

First, we will define a second composition equation, called _machine composition_,
operating not on _opaque_ OGS strategies, 
but specifically on pairs of active and passive states of the
machine strategy. The definition will be essentially the same, but instead of
peeling off layers of a coinductive tree to obtain the next moves, we will call
the $strat.play$ and $strat.coplay$ functions of the big-step system.

Second, notice that in the function $kw.fun th c th gamma |-> ogs.evalo th
c[gamma]$, the two arguments $c$ and $gamma$ are special cases respectively of
active and passive machine strategy states (more specifically _initial_
states). We will thus generalize this function to arbitrary pairs of active and
passive machine strategy states. Intuitively, this function will _zip_ together
the telescopic environments of the two states, then substitute the active state's
configuration by the resulting assignment and finally apply $ogs.evalo$.

More precisely, to conclude adequacy we will show that
- _machine composition_ is strongly bisimilar to composition,
- _zip-then-eval-to-obs_ is a strong fixed point of _machine composition_,
- _machine composition_ is eventually guarded.

== Machine Strategy Composition

Recall that in @def-compo-eqn we formalized the composition equation as a map of
type
$ "Arg" -> delay.t th (O^ctx.named th Omega + "Arg") $
where the arguments
$ "Arg" := ogs.stratA th Omega ogs.join ogs.stratP th Omega $
consisted of pairs of an active strategy $s^+ cl ogs.stratA th Omega th Psi$ and
a passive strategy $s^- cl ogs.stratP th Omega th Psi$, both over the same
interleaved scope $Psi$. To specialize composition to the machine strategy, we
will simply swap out $ogs.stratA th Omega$ and $ogs.stratP th Omega$ for active
and passive machine strategy states.

#definition[Machine Strategy Composition][
  First, define the _arguments_ of the machine strategy composition as follows.

  $ ogs.mcarg := ogs.mstrat_M.strat.stp ogs.join ogs.mstrat_M.strat.stn $

  Then, define the _machine strategy composition equation_ as follows.

  $ ogs.mcompeq cl ogs.mcarg -> delay.t th (O^ctx.named th Omega + ogs.mcarg) \
    ogs.mcompeq th (s^+ ctx.cute s^-) := de("aux") itree.fmap ogs.mstrat_M.strat.play th s^+ \
    quad kw.where \
    quad pat(de("aux") th (base.inj1 th r)      & := base.inj1 th r,
             de("aux") th (base.inj2 th (m, k)) & := base.inj2 th ((ogs.mstrat_M.strat.coplay th s^- th m) ctx.cute k))
    $

  Finally, define the _machine strategy composition_ as the following iteration.

  $ ogs.mcomp cl ogs.mcarg -> delay.t th (O^ctx.named th Omega) \
    ogs.mcomp := itree.iter_(ogs.mcompeq) $
]

We then link this new composition of machine strategies with the more general one,
introduced in the previous chapter.

#lemma[Machine Composition and Composition][
  For any $Psi cl ctx.ctxc th S$, $s^+ cl ogs.mstrat_M.strat.stp th Psi$ and
  $s^- cl ogs.mstrat_M.strat.stn th Psi$ the following property holds.

  $ ogs.mcomp th (s^+ ctx.cute s^-) itree.eq (itree.unrollA_(ogs.mstrat_M) th s^+ game.par itree.unrollP_(ogs.mstrat_M) th s^-) $
] <lem-compo-mcompo>
#proof[
  As both sides are constructed by (unguarded) iteration, this lemma is proven
  by an application of @lem-iter-mon. In other words, we show that their
  respective equation systems operate in lockstep, with some relation on their
  argument being preserved. More precisely, define the
  following relation between the arguments of compositions and machine composition.

  $ R cl ogs.mcarg -> ogs.stratA th Omega ogs.join ogs.stratP th Omega -> base.Prop \
    R th (s^+_1 ctx.cute s^-_1) th (s^+_2 ctx.cute s^-_2) := \
    quad (itree.unrollA_(ogs.mstrat_M) th s^+_1 = s^+_2) base.prod (itree.unrollP_(ogs.mstrat_M) th s^-_1 th = s^-_2) $

  Then, for any $a cl ogs.mcarg$ and $b cl ogs.stratA th Omega ogs.join ogs.stratP th Omega$,
  we prove that $R th a th b -> (ogs.mcompeq th a) iteq(cnorm(=) de(+^rel.r) cnorm(R)) (ogs.compeq th b)$.

  Succinctly, the above proposition is proven by inspecting the head of the
  configuration part of the active state $a$. In case it plays
  #itree.retF, the conclusion is direct, while for #itree.tauF the
  conclusion is by coinduction.

  Then, by @lem-iter-mon we have $R th a th b -> (ogs.mcomp th a) itree.eq
  (ogs.comp th b)$, and we obtain the result by instantiating the relation
  witness $R th a th b$ by $(base.refl, base.refl)$.
]

Finally, before moving on, we will prove a variant of the $ogs.evalsub$ law
of language machines respecting substitution. It is a special case which will
be particularly useful at several points.

#lemma[Evaluation under Shifted Substitution][
  For any $c cl C th (Omega ctx.cat Gamma)$ and $sigma cl Gamma asgn(V) Omega$,
  the following proposition holds.

  $ ogs.eval th c[sub.var,sigma]
    itree.eq pat(((i ctx.cute o), gamma) <- ogs.eval th c th ";", 
                  kw.case th ctx.vcat th i,
                  pat(base.vlft th j & := itree.ret th ((j ctx.cute o), gamma[sub.var,sigma]),
                       base.vrgt th j & := ogs.eval th (ogs.apply th (sigma th j) th o th gamma[sub.var,sigma])))
  $
] <lem-evalsub-shift>
#proof[
  By $ogs.evalsub$, unfolding the definition of $ogs.emb$, we have the following.

  $ ogs.eval th c[sub.var,sigma]
    itree.eq
    pat(((i ctx.cute o), gamma) <- ogs.eval th c th ";",
        ogs.eval th (ogs.apply th ([sub.var,sigma] th i) th o th gamma[sub.var,sigma])) $

  The right-hand sides of both the lemma and the equivalence above start by
  binding $ogs.eval th c$. 
  Hence by monotonicity of bind (@lem-up2bind) it suffices to relate their
  continuations. Introduce some normal form $((i ctx.cute o), gamma)$. By case on $ctx.vcat th i$.
  - If $ctx.vcat th i := ctx.vcatl th j$, then $[sub.var,sigma] th i := sub.var th j$. Conclude
    by $ogs.evalnf$, showing that $ogs.eval th (ogs.apply th (sub.var th j) th o th
    gamma[sub.var,sigma]) itree.eq itree.ret th ((j ctx.cute o), gamma[sub.var, sigma]).$
  - If $ctx.vcat th i := ctx.vcatr th j$, then $[sub.var,sigma] th i := sigma th j$ and
    we conclude by reflexivity. #qedhere
]

== Evaluation as a Fixed Point of Machine Composition

After defining the machine strategy composition, the next step is to generalize
$kw.fun th c th gamma |-> ogs.evalo th c[gamma]$ to active and passive machine
strategy states and then show that the obtained function is a fixed point of our
newly defined composition. Our goal is to define a function of the following type.

$ ogs.zipev cl ogs.mcarg -> delay.t th (O^ctx.named th Omega) $

We start by defining the following zipping of telescopic environments.
Recall how in @def-tele-collapse we defined the _collapsing_ of telescopic
environments into usual assignments. Here the process is relatively similar,
but instead of only _one_ telescopic environment, we are here given _two_,
which nicely mesh into one together.

#definition[Zipping Map][
  The _left-to-right and right-to-left zipping maps_ of type

  $ ar ogs.zrl ar th {Psi} cl ogs.teleA th Psi -> ogs.teleP th Psi -> ogs.catE th Psi asgn(V) Omega \
    ar ogs.zlr ar th {Psi} cl ogs.teleA th Psi -> ogs.teleP th Psi -> ogs.catO th Psi asgn(V) Omega $

  are defined by mutual induction as follows.

  $ & ogs.tnilA     & ogs.zrl & ogs.tnilP           && := [] \
    & (a ogs.tconA) & ogs.zrl & (b ogs.tconP gamma) && := [b ogs.zlr a, gamma[sub.var, b ogs.zrl a] ] \
    \
    & ogs.tnilA     & ogs.zlr & ogs.tnilP           && := [] \
    & (a ogs.tconA) & ogs.zlr & (b ogs.tconP gamma) && := b ogs.zrl a \ $
]

#remark[
  Intuitively, #ogs.zrl is concerned with providing hereditarily substituted values for every
  variable introduced by the currently passive player (i.e., the RHS), while #ogs.zlr provides
  hereditarily substituted values for every variable introduced by the currently active
  player (i.e., the LHS). It is thus normal that only #ogs.zrl does any real work: since
  the LHS is always the currently active side, it did not play the last move and thus did
  not store anything at the top of its environment.
]

Before going further, let us prove the crucial property relating the zipping of two telescopic
environments and their respective collapse. Recall that the collapsing functions have the
following types.

$ ogs.collA cl ogs.teleA th Psi -> ogs.catO Psi asgn(V) (Omega ctx.cat ogs.catE Psi) \
  ogs.collP cl ogs.teleP th Psi -> ogs.catE Psi asgn(V) (Omega ctx.cat ogs.catO Psi) $

#lemma[Zip Fixed Point of Collapse][
  Given $Psi cl ctx.ctxc th S$, for any $a cl ogs.teleA th Psi$ and $b cl
  ogs.teleP th Psi$, the following two statements hold.

  1. $(ogs.collA a)[sub.var, a ogs.zrl b] approx a ogs.zlr b$
  2. $(ogs.collP b)[sub.var, a ogs.zlr b] approx a ogs.zrl b$
] <lem-zip-coll-fix>
#proof[
  The two statements are proven simultaneously, by induction on $Psi$, by inspecting
  $a$ and $b$. While they are slightly tedious, the calculations are purely equational
  manipulations of assignments, based on substitution monoid laws.
]

Finally, we can define the function we wanted and prove that it is a fixed point of
composition.

#definition[Zip-then-evaluate][
  The _zip-then-evaluate_ map is defined as follows.

  $ ogs.zipev cl ogs.mcarg -> delay.t th (O^ctx.named th Omega) \
    ogs.zipev th ((c , a) ctx.cute b) := ogs.evalo th c[sub.var, a ogs.zrl b] $
]

#theorem[Zip-then-evaluate Fixed Point][
  Zip-then-evaluate is a fixed point of the machine strategy composition equation w.r.t.
  strong bisimilarity, i.e., for all $x cl ogs.mcarg$, the following property holds.

  $ (ogs.zipev th x)
    itree.eq
    (ogs.mcompeq th x itree.bind kw.fun pat(
        base.inj1 th r & := itree.ret th r,
        base.inj2 th y & := ogs.zipev th y,
    )) $
] <lem-zipev-fix>
#proof[
  Let us consider the composition argument $((c, a) ctx.cute b)$. We will
  reason equationally, simplifying both sides to the same computation.

  Starting from the left-hand side, we rewrite as follows.

  $ &          &&  ogs.zipev th ((c, a) ctx.cute b)                      quad & \
    & itree.eq &&  base.fst itree.fmap ogs.eval c[sub.var, a ogs.zrl b] quad & #[(def.)] \
    & itree.eq &&  base.fst itree.fmap pat(((i ctx.cute o), gamma) <- ogs.eval th c th ";", 
                      kw.case th ctx.vcat th i,
                      pat(base.vlft th j & := itree.ret th ((j ctx.cute o), gamma[sub.var,a ogs.zrl b]),
                          base.vrgt th j & := ogs.eval th (ogs.apply th (rho th j) th o th gamma[sub.var,a ogs.zrl b]))) #h(1.5em) & #[(@lem-evalsub-shift)] \
    & itree.eq &&  pat(((i ctx.cute o), gamma) <- ogs.eval th c th ";", 
                      kw.case th ctx.vcat th i,
                      pat(base.vlft th j & := itree.ret th (j ctx.cute o),
                          base.vrgt th j & := ogs.evalo th (ogs.apply th ((a ogs.zrl b) th j) th o th gamma[sub.var,a ogs.zrl b]))) & #[(monad)] \
  $

  The last computation above is now simple enough. We will remember it and seek
  to obtain the same starting from the right-hand side of the theorem
  statement. To ease the unfolding of definitions, first pose the following
  shorthands.

  $ f := kw.fun pat(base.inj1 th r      & := base.inj1 th r,
                    base.inj2 th (m, k) & := base.inj2 th ((ogs.mstrat_M.strat.coplay th b th m) ctx.cute k)) $

  $ kappa := kw.fun pat(
        base.inj1 th r & := itree.ret th r,
        base.inj2 th y & := ogs.zipev th y) $

  Starting from the right-hand side, we rewrite as follows.

  $ &          &&  ogs.mcompeq th x itree.bind pat(base.inj1 th r & := itree.ret th r,
                                                   base.inj2 th y & := ogs.zipev th y) & \
    & itree.eq &&  (f itree.fmap ogs.mstrat_M.strat.play th (c, a)) itree.bind kappa   & #[(def.)] \
    & itree.eq &&  ogs.mstrat_M.strat.play th (c, a) itree.bind (kappa compose f)     & #[(monad)] \
    & itree.eq &&  pat(
                x <- pat(
        ((i ctx.cute o), gamma) <- ogs.eval th c th ";",
        kw.case (ctx.vcat th i) \
        pat(
          base.vlft th j & := itree.ret th (base.inj1 th (j ctx.cute o)),
          base.vrgt th j & := itree.ret th (base.inj2 th ((j ctx.cute o), (a ogs.tconP gamma))))
        ),
                kappa th (f th x))     & #[(def.)] \
    & itree.eq && pat(
        ((i ctx.cute o), gamma) <- ogs.eval th c th ";",
        kw.case (ctx.vcat th i) \
        pat(
          base.vlft th j & := kappa th (f th (base.inj1 th (j ctx.cute o))),
          base.vrgt th j & := kappa th (f th (base.inj2 th ((j ctx.cute o), (a ogs.tconP gamma))))
        )) & #[(monad)] \
    & itree.eq && pat(
        ((i ctx.cute o), gamma) <- ogs.eval th c th ";",
        kw.case (ctx.vcat th i) \
        pat(
          base.vlft th j & := itree.ret th (j ctx.cute o),
          base.vrgt th j & := ogs.zipev th (ogs.mstrat_M.strat.coplay th b th (j ctx.cute o) ctx.cute (a ogs.tconP gamma))
        )) & #[(def.)] \
  $

  At this point, our two rewriting chains almost match up, with only the second branch
  of the respective case split differing. More precisely, both computations
  start by binding $ogs.eval th c$, so that by @lem-up2bind it suffices to
  prove the continuations pointwise bisimilar. Then, we eliminate $ctx.vcat th
  i$. In case of $ctx.vcatl th j$ we conclude by reflexivity. We now turn to the
  $ctx.vcatr th j$ case. What is left is to prove is

  $          & ogs.evalo th (ogs.apply th ((a ogs.zrl b) th j) th o th gamma[sub.var,a ogs.zrl b]))) \
    itree.eq & ogs.zipev th (ogs.mstrat_M.strat.coplay th b th (j ctx.cute o) ctx.cute (a ogs.tconP gamma)). $

  First pose the following two "administrative" renamings (from the definition of the machine strategy $strat.coplay$ function).

    $ rho_1 := [ctx.rcatl, ctx.rcatr[ctx.rcatl]] \
      rho_2 := ctx.rcatr[ctx.rcatr]. $

  Then, we start rewriting from the right-hand side.

  $
    &          && ogs.zipev th (ogs.mstrat_M.strat.coplay th b th (j ctx.cute o) ctx.cute (a ogs.tconP gamma)) & \
    & itree.eq && ogs.zipev th ((ogs.apply th (ogs.collP b th j)[rho_1] th o th rho_2, b ogs.tconA) ctx.cute (a ogs.tconP gamma)) & #[(def.)] \
    & itree.eq && ogs.evalo th (ogs.apply th (ogs.collP b th j)[rho_1] th o th rho_2)[sub.var, (b ogs.tconA) ogs.zrl (a ogs.tconP gamma)) & #[(def.)] \
    & itree.eq && ogs.evalo th (ogs.apply th (ogs.collP b th j)[rho_1] th o th rho_2)[sub.var, a ogs.zlr b, gamma[sub.var, a ogs.zrl b]]) & #[(def.)] \
  $
  Pose $sigma := [sub.var, a ogs.zlr b, gamma[sub.var, a ogs.zrl b]]$ and continue as follows.
  $
    & itree.eq && ogs.evalo th (ogs.apply th (ogs.collP b th j)[rho_1][sigma] th o th rho_2[sigma])) & #[($ogs.appsub$)] \
    & itree.eq && ogs.evalo th (ogs.apply th (ogs.collP b th j)[sub.var,a ogs.zlr b] th o th gamma[sub.var, a ogs.zrl b])) quad & #[(sub laws)] \
    & itree.eq && ogs.evalo th (ogs.apply th ((a ogs.zrl b) th j) th o th gamma[sub.var, a ogs.zrl b])) & #[(@lem-zip-coll-fix)]
  $

  This concludes our proof: although tedious, it simply rests upon:
  - passing a substitution under an evaluation using $ogs.evalsub$ (in @lem-evalsub-shift),
  - passing a substitution under an application using $ogs.appsub$,
  - the use of @lem-zip-coll-fix to fuse collapsing and zipping,
  - and a series of basic rewriting steps using the monad laws of #delay.t and
    the categorical structure of assignments. #qedhere
]

== Eventual Guardedness of Machine Composition

Now that we know that $ogs.zipev$ is a fixed point of the machine strategy
composition equation, we can conclude adequacy of composition if we know that
the machine strategy composition equation has unique fixed points. We will deduce
this from the fact that the equation is eventually guarded.

Recall that in this precise case, eventual guardedness means that every so many
synchronization events of composition, we will stumble upon a silent step of
one of the two strategies (i.e., a reduction step of their configuration). The
number of synchronizations necessary to see such a reduction step is bounded by
two imbricated arguments. First, by the finite redex property of the language
machine, after some amount of synchronizations _where the observed value is not
a variable_, we will find a reduction step. Second, by a visibility-like
condition, after some amount of synchronizations, we will observe a value that
is not a variable.

More precisely, the "visibility-like" argument states that if some variable $i$
is associated in a telescopic environment to some variable $j$, then the
_depth_ of $j$ is strictly smaller than the depth of $i$, where the depth
denotes the number of moves after which the variable was introduced. Let us define
this.

#definition[Variable Depth][
  Define the _positive and negative depth functions_ by mutual induction as follows.

  $ ogs.depthA th Psi th {alpha} cl ogs.catE Psi ctx.var alpha -> base.nat $
  #v(-0.5em)
  $ & ogs.depthA th ctx.nilc             && th i := kw.case th (ctx.vemp th i) th [] \
    & ogs.depthA th (Psi ctx.conc Gamma) && th i := kw.case th (ctx.vcat th i) $
  #v(-0.5em)
  $ pat(ctx.vcatl th i & := ogs.depthP th Psi th i,
        ctx.vcatr th i & := 1 + ctx.lenc th Psi) $

  $ ogs.depthP th Psi th {alpha} cl ogs.catO Psi ctx.var alpha -> base.nat $
  #v(-0.5em)
  $ & ogs.depthP th ctx.nilc             && th i := kw.case th (ctx.vemp th i) th [] \
    & ogs.depthP th (Psi ctx.conc Gamma) && th i := ogs.depthA th Psi th i $
]

#lemma[Depth Decreases][
  The depth of a variable stored in a telescopic environment is strictly smaller than its
  index. More precisely, the following two statements are true.
  1. Given an environment $a cl ogs.teleA th Psi$ and variables $i cl ogs.catE
     Psi ctx.var alpha$ and $j cl ogs.catO Psi ctx.var alpha$ such that $ogs.collA a th i = sub.var th (ctx.rcatr th j)$, then
     $ ogs.depthP th j < ogs.depthA th i $
  2. Given an environment $a cl ogs.teleP th Psi$ and variables $i cl ogs.catO
     Psi ctx.var alpha$ and $j cl ogs.catE Psi ctx.var alpha$ such that $ogs.collP a th i = sub.var th (ctx.rcatr th j)$, then
     $ ogs.depthA th j < ogs.depthP th i $
] <lem-depth-decreases>
#proof[
  The two statements are proven simultaneously, by direct induction on the
  graph of the depth function at $i$.
]

We can now prove eventual guardedness.

#theorem[Composition Eventually Guarded][
  The machine strategy composition equation $ogs.mcompeq$ is eventually guarded.
] <lem-compo-guarded>
#proof[
  More formally, the goal is to prove $itree.eqevguard th ogs.mcompeq$, i.e.,
  $ (a cl ogs.mcarg) -> itree.evguard_ogs.mcompeq th (ogs.mcompeq th a). $

  Introducing and fully destructing the argument $a$ as $((c, sigma^+) ctx.cute sigma^-)$, obtain $c cl C th (Omega ctx.cat ogs.catE Psi)$,
  $sigma^+ cl ogs.teleA th Psi$ and $sigma^- cl ogs.teleP th Psi$. As $ogs.mcompeq$ starts
  by evaluating $c$, lets look at the first step of $ogs.eval th c$:
  - If it is a #itree.tauF step, we directly conclude by guardedness (#itree.evg).
  - If it is a return $itree.retF th ((i ctx.cute o), gamma)$ where $i$ belongs to the final scope $Omega$, the composition returns and
    we conclude again by guardedness (#itree.evg).
  - In the last case, where $ogs.eval th c$ returns as above, with $i$ a non-final
    variable, we arrive at the core of the proof and continue as follows.

  Recapitulating, we can now forget about $c$, we still have $sigma^+$ and $sigma^-$ and we
  now have $i cl ogs.catE Psi ctx.var alpha$, $o cl O.ctx.oper th alpha$ and $gamma cl O.ctx.dom th o asgn(V) (Omega ctx.cat ogs.catE Psi)$.
  Our goal is now to prove

  $ itree.evguard_ogs.mcompeq \ quad (itree.ret th (base.inj2 th ((ogs.apply th
    (ogs.collP sigma^- th i)[rho_1] th o th rho_2) , th th sigma^-) ctx.cute
    (sigma^+ ogs.tconP gamma))) $

  with the usual culprits $rho_1 := [ctx.rcatl, ctx.rcatr[ctx.rcatl]]$ and $rho_2 := ctx.rcatr[ctx.rcatr]$.

  Proceed first by well-founded induction on $(alpha, o)$ (using the finite
  redex hypothesis $ogs.finred$), and then by well-founded induction on the
  depth of $i$. This does not change the proof goal but simply introduces two
  induction hypotheses.

  As obviously the current computation is not guarded, first apply $itree.evs$
  to unfold one more step of the equation, obtaining the following goal

  $ itree.evguard_ogs.mcompeq th (ogs.mcompeq th \ quad ((ogs.apply th
    (ogs.collP sigma^- th i)[rho_1] th o th rho_2) , th th sigma^-) ctx.cute
    (sigma^+ ogs.tconP gamma)). $

  Then, by case on whether or not $v := ogs.collP sigma^- th i$ is a variable ($sub.isvardec$).

  - If $v$ is some variable $j cl (Omega ctx.cat ogs.catO Psi) ctx.var alpha$,
    the $ogs.apply$ expression is in fact the embedding of the normal form
    $((rho_1 th j ctx.cute o), rho_2)$. Thus, by $ogs.evalnf$ we know its evaluation.
    Then by case on $ctx.vcat th j$:
    - If $j cl Omega ctx.var alpha$, the composition ends with
      $(j ctx.cute o)$, thus is guarded.
    - If $j cl ogs.catO Psi ctx.var alpha$, then by @lem-depth-decreases,
      $ogs.depthP th j < ogs.depthA th i$. Taking the next context increment into
      account by moving from $Psi$ to $Psi ctx.conc O.ctx.dom th o$, we deduce
      $ogs.depthA th (ctx.rcatl th j) < ogs.depthP th i$ and conclude by the
      innermost induction hypothesis.
  - If $v$ is not a variable, pose $c := ogs.apply th v[rho_1] th o th rho_2$ and inspect
    the first step of $ogs.eval th c$.
    - If it is a $itree.tauF$ move, then the composition is guarded.
    - If it is a $itree.retF th ((k ctx.cute o'), delta)$, then, by case on $ctx.vcat th k$.
      If $k$ is a final move then composition is guarded. Else $k$ is non-final and we
      conclude by applying the outermost induction hypothesis, as indeed $o' ogs.badinst o$.
      #qedhere
]

== Conclusion

Now that the core properties are proven (@lem-zipev-fix and
@lem-compo-guarded), what is left to do is mostly to combine them in the right
way to deduce adequacy. Still, to finish up and deduce correctness we have left
out one benign step described in the proof outline: congruence of weak
bisimilarity for composition (@def-compo-congr). Let us prove it now.

#lemma[Congruence for Composition][
  For all $Psi cl ctx.ctxc th S$, $s^+_1, s^+_2 cl ogs.stratA th Omega th Psi$
  and $s^- cl ogs.stratP th Omega th Psi$, the following property holds.

  $ s^+_1 itree.weq s^+_2 -> (s^+_1 game.par s^-) itree.weq (s^+_2 game.par s^-) $
] <lem-compo-congr>
#proof[
  The proof is very similar to @lem-compo-mcompo and is mostly an application
  of monotonicity of iteration (@lem-iter-mon). Define the following relation
  on $"Arg" := ogs.stratA th Omega ogs.join ogs.stratP th Omega$

  $ R cl "Arg" -> "Arg" -> base.Prop \
    R th (s^+_1 ctx.cute s^-_1) th (s^+_2 ctx.cute s^-_2) := (s^+_1 itree.weq s^+_2) base.prod (forall th r -> s^-_1 th r itree.weq s^-_2 th r). $

  It is easy to show that $R$ is preserved by the composition equation, then, by
  application of @lem-iter-mon the result follows.
]

#theorem[Adequacy of Composition][
  For all $Gamma cl S$, $c cl C th Gamma$ and $gamma cl Gamma asgn(V) Omega$,
  the following property holds.

  $ ogs.evalo th c[gamma] itree.weq (ogsinterpA(c) game.par ogsinterpP(gamma)) $
] <lem-compo-adequacy>
#proof[
  Embedding $c$ and $gamma$ respectively to initial active and initial passive
  states of the machine strategy, by definition we have
  $ ogs.evalo th c[gamma] itree.eq & ogs.zipev th ((c[ctx.rcatr], (ogs.tnilP ogs.tconA)) ctx.cute (ogs.tnilA ogs.tconP gamma[ctx.rcatl])) $

  By @lem-evfix-uniq and @lem-compo-guarded, the machine strategy composition equation has
  unicity of strong fixed points, hence by @lem-zipev-fix, $ogs.zipev$ is pointwise
  strongly bisimilar to its _eventually guarded iteration_. Continuing the above chain
  we obtain the following.

  $ ogs.evalo th c[gamma] itree.eq & itree.eviter_ogs.mcompeq th ((c[ctx.rcatr], (ogs.tnilP ogs.tconA)) ctx.cute (ogs.tnilA ogs.tconP gamma[ctx.rcatl])) $

  By @lem-eviter-iter, the eventually guarded iteration is pointwise weakly bisimilar
  the unguarded iteration, i.e., $ogs.mcomp$. We obtain the following.

  $ ogs.evalo th c[gamma] itree.weq & ogs.mcomp th ((c[ctx.rcatr], (ogs.tnilP ogs.tconA)) ctx.cute (ogs.tnilA ogs.tconP gamma[ctx.rcatl])) $

  Finally we conclude by using @lem-compo-mcompo to bridge between machine
  strategy compositions and opaque composition.

  $ ogs.evalo th c[gamma] itree.weq & ogsinterpA(c) game.par ogsinterpP(gamma) $
  #v(-2em)
]

We finally prove OGS correctness w.r.t. contextual equivalence (@thm-correctness).
#proof[
  Given $c_1, c_2 cl C th Gamma$ such that $ ogsinterpA(c_1) itree.weq ogsinterpA(c_2), $ for any
  $gamma cl Gamma asgn(V) Omega th th $ we have

  $ ogs.evalo th c_1[gamma] & itree.weq (ogsinterpA(c_1) game.par ogsinterpP(gamma)) quad quad & #[(@lem-compo-adequacy)] \
                          & itree.weq (ogsinterpA(c_2) game.par ogsinterpP(gamma)) & #[(@lem-compo-congr)] \
                          & itree.weq ogs.evalo th c_2[gamma] & #[(@lem-compo-adequacy)] $
  #v(-2em)
]

To conclude this chapter, and with it the proof of the central result of this
thesis, let me say a couple words about its significance. First of all, OGS
models which are sound with respect to observational equivalence have already been
published, some in fact for instances which we do not cover here, such as, say,
impure languages with references~#mcite(<Laird07>)#mcite(dy: 2em, <JaberM21>). As such, although there is some
progress in providing a generic proof for all languages which are expressible
as language machines, I believe that the core contribution is in the way we
streamline the correctness proof, hopefully making it accessible to a broader
community. There are two novelties which contribute to this.

First, by working with an abstract _language machine_, we can more precisely
see and isolate which parts of the proofs are generic and which parts are
language specific. This has led us to formalize precise requirements, as well
as recognize previously hidden details, such as the finite redex hypothesis.

Second, while the decomposition into an adequacy and congruence proof for
composition is common, in published articles, adequacy is typically proven
monolithically. The method provided here further decomposes adequacy into two
independent arguments, each quite informative on its own.

@lem-zipev-fix provides what we can think of as the core semantical
argument for adequacy: one step of composition does not change the result
obtained by syntactically substituting the two machine strategy states and
evaluating the obtained language configuration. Satisfyingly, the proof is
quite direct and relatively free of administrative headaches: it is simply a
sequence of rewriting step.

Knowing this, one should not be blamed for thinking it is enough to conclude
adequacy. After all, if one composition step leaves the final result unaltered,
why should it be any different after an infinite number of steps, i.e., full
composition? But arbitrary fixed points of partial computations can behaved
surprisingly. Thus, a second argument, @lem-compo-guarded, concentrates the
technical justification of the informal reasoning: the composition
equation is "nice" enough and thus enjoys unicity of fixed points.

I hope that this separation between the high-level argument and the tedious
technical justification demystifies the adequacy proof, and enables a better
understanding of it by non specialists. In particular, it opens up an
intermediate level of explanation of the OGS correctness in which @lem-zipev-fix
is detailed but where unicity is taken for granted, leaving @lem-compo-guarded
to the specialist.

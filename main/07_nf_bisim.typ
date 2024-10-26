#import "/lib/all.typ": *

= Normal Form Bisimulations <ch-nf-bisim>

Operational game semantics is intimately linked to another slightly older
family of coinductive constructions: normal form bisimulations. Stemming from
work on program equivalence, normal form bisimulation #peio[who coined it?] is
an umbrella term for the program equivalence induced by several related
constructions such as #nm[Böhm] trees, #nm[Levy]-#nm[Longo] trees, #nm[Lassen]
trees, and other constructions tailored to a variety of settings #peio[ref]. In
this short chapter, we introduce our own variant of normal form bisimulation,
for a given language machine. Then, we show how the interpretation from language
configurations to OGS strategies can be factorized through _normal form
strategies_. Thanks to this, we deduce a correctness theorem, stating---as for
OGS---that any two _normal form bisimilar_ language configurations are
_substitution equivalent_.

#remark[
  Be advised that at the time of writing these lines, the constructions and
  proofs contained in this chapter are only sketched in the Coq artifact. As we will
  see the proofs are not particularly challenging, but my focus for the
  code was to clean up and comment OGS correctness and language machine
  instances. You can check the #link("https://github.com/lapin0t/ogs")[online
  repository]#margin-note(link("https://github.com/lapin0t/ogs")) to see
  if this has been fixed by the time you are reading.
]

== Normal Form Bisimulations in a Nutshell

In all normal form (NF) bisimulations constructions, the main idea is to
associate to each program a possibly infinite tree. Here, we will call these
trees _normal form strategies_, i.e., strategies for the _normal form game_.
This induces a notion of program equivalence which holds whenever two programs
have bisimilar associated strategies: _normal form bisimilarity_.

These infinite trees are determined by reducing the program to a normal form
for some given reduction strategy---most usually some kind of head-reduction.
The "head" of the normal form gives us the node of the tree, and the children
are obtained by coinductively applying the same process to the subterms. By now
this kind of splitting of normal forms into a head and a sequence of subterms
should ring a bell... Although OGS and NF bisimulations have historically been
introduced in reverse order, we can use our readily available knowledge of the
OGS game to provide a very succint and precise description of the normal form
game. The NF game is no more than a restriction of the OGS game, where the
server is only allowed to query the variables introduced by the last client
move.

Reusing our existing infrastructure of binding families and named observations,
we express the NF game quite similarly to the OGS game, simply changing the
game positions and transition functions. Because the allowed server moves are
dictated by the last client move, we only need to remember the client scope
throughout the game. As such, client positions consist of a single scope
$Gamma$, containing the variables the client is allowed to observe, while
server positions consist of two scopes $(Gamma, Delta)$, containing the
variables that respectively the server and the client are allowed to query.

#definition[NF Game][
  Assuming a scope structure $ctx.scope_T th S$, given a binding family $O cl
  ctx.bfam_T th S$, the _normal form (NF) game_ is defined as follows.

  $ nf.g cl game.g th S th (S base.prod S) kw.whr \
    pat(game.client := \
          pat(game.mv th Gamma := O^ctx.named th Gamma,
              game.nx th {Gamma} th o := (ctx.domnm th o, Gamma)),
        game.server := \
          pat(game.mv th (Gamma, Delta) := O^ctx.named th Gamma,
              game.nx th {Gamma, Delta} th o := Delta ctx.cat ctx.domnm th o),
       ) $
]

We can then define active and passive normal form strategies with respect to a
final scope $Omega$, as for OGS strategies.

#definition[NF Strategies][
  Assuming a scope structure $ctx.scope_T th S$, given a binding family $O cl
  ctx.bfam_T th S$ and a scope $Omega cl S$, _active and passive normal form strategies over $O$ with
  final scope $Omega$_ are defined as follows.

  $ nf.stratA th Omega th Gamma := game.stratA_nf.g th (kw.fun th Gamma |-> O^ctx.named th Omega) th Gamma \
    nf.stratP th Omega th Gamma th Delta := game.stratP_nf.g th (kw.fun th Gamma |-> O^ctx.named th Omega) th (Gamma, Delta) $
]

#remark[
  Note that $nf.stratP th Omega$ is isomorphic to an assignment type. Indeed,
  define "unary" passive strategies as follows.

  $ de("NF"^1_bk(O)) th Omega th Gamma th alpha := (o cl O.ctx.Oper th alpha) -> nf.stratA th Omega th (Gamma ctx.cat O.ctx.dom o) $

  Then, $nf.stratP th Omega th Gamma th Delta$ is isomorphic to $Gamma
  asgn(de("NF"^1_bk(O)) th Omega th) Delta$, as witnessed by the following two
  functions, definitionally inverse to each other.

  $ & de("into") th s^- th i th o && := s^- th (i ctx.cute o) \
    & de("from") th sigma th (i ctx.cute o) && := sigma th i th o $

  In light of this, we will extend standard assignment notations to passive strategies,
  in particular for the terminal arrow and the copairing.

  #mathpar(block: true, spacing: 2em,
    $ [] cl nf.stratP th Omega th ctx.emp th Delta \
      [] := de("from") th [] $,
    $ [k_1, k_2] cl nf.stratP th Omega th (Gamma_1 ctx.cat Gamma_2) th Delta \
      [k_1, k_2] := de("from") th [de("into") th k_1, de("into") th k_2] $)
]

Given a language machine with renamings, we now construct the strategy associated to
any given language configuration. Once again, it is merely a simplified version of
the OGS machine strategy: it proceeds by evaluating the current language configuration
to compute the next move, and using the application map to respond to queries.

#definition[NF Strategy][
  Given a language machine $M cl ogs.machine th O th V th C$ with renamings,
  i.e., such that $sub.pren th V$ and $sub.ren th C$ hold, given a final scope
  $Omega cl S$, the _NF machine strategy_ is the big-step system defined as follows.
  $ nf.mstrat th M cl strat.bs_nf.g th (kw.fun th Gamma |-> O^ctx.named th Omega) \
    nf.mstrat th M := \
    pat(
      strat.stp th Gamma := C th (Omega ctx.cat Gamma),
      strat.stn th (Gamma, Delta) := Gamma asgn(V) (Omega ctx.cat Delta),
      strat.play th c := kw.do \
        quad ((i ctx.cute o), gamma) <- ogs.eval th c th ";" \
        quad kw.case (ctx.vcat th i) \
        quad pat(
          ctx.vcatl th i & := itree.ret th (base.inj1 th (i ctx.cute o)),
          ctx.vcatr th j & := itree.ret th (base.inj2 th ((j ctx.cute o), gamma)),
        ),
      strat.coplay th gamma th (i ctx.cute o) :=
        ogs.apply th (gamma th i)[rho_1] th o th rho_2 ,
    ) \
    \
    rho_1 := [ctx.rcatl, ctx.rcatr[ctx.rcatl]] \
    rho_2 := ctx.rcatr[ctx.rcatr] $
] <def-nf-mstrat>

#definition[NF Interpretation, NF Bisimulation][
  Given a language machine $M cl ogs.machine th O th V th C$ with renamings,
  i.e., such that $sub.pren th V$ and $sub.ren th C$ hold, given a final
  scope $Omega cl S$, the _NF interpretation_ is obtained
  by unrolling the NF machine strategy.

  $ nfinterpA(ar) th {Gamma} cl C th Gamma -> nf.stratA th Omega th Gamma \
    nfinterpA(c) := itree.unrollA_(nf.mstrat th M) th c[ctx.rcatr] $

  Furthermore, two configurations $c_1, c_2 cl C th Gamma$ are _normal form bisimilar_
  whenever $nfinterpA(c_1) itree.weq nfinterpA(c_2)$.
] <def-nf-bisim>

== Relating NF strategies and OGS strategies

We have described the NF game and the analogue of the OGS machine strategy,
i.e., the "infinite normal form tree" semantics for language machines. To
deduce correctness of NF bisimulation from our OGS correctness theorem, we now
need to relate NF strategies and OGS strategies. In fact we will prove a little
bit more than what is strictly necessary to deduce correctness.

First, since the NF game is very similar to the OGS game, simply allowing less
server moves, it is easy to restrict an OGS strategy to an NF strategy.

#definition[OGS to NF][
  Assuming a scope structure $ctx.scope_T th S$, given a binding family $O cl
  ctx.bfam_T th S$ and a scope $Omega cl S$, define the _restriction from OGS
  to NF strategies_ by coinduction as follows.

  $ nf.ogs2nfA th {Psi} cl ogs.stratA th Omega th Psi -> nf.stratA th Omega th (ogs.catE Psi) \
    nf.ogs2nfA th s := \
    pat(itree.obs := kw.case s .itree.obs \
      pat(itree.retF th r & := itree.retF th r,
          itree.tauF th t & := itree.tauF th (nf.ogs2nfA th t),
          itree.visF th q th k & := itree.visF th q th (kw.fun th (i ctx.cute o) |-> nf.ogs2nfA th (k th (ctx.rcatr th i ctx.cute o))))) \
    $
]

Yet the most interesting direction is the other one: embedding NF strategies into OGS
strategies. In the OGS game, the server is also allowed to query older variables, which,
on the face of it, an NF strategy does not know how to handle. However, every variable
was once new! So if we remember all the continuations of the NF strategy along the way,
we can accumulate enough information to respond to any OGS server queries, restarting
the relevant old continuation. In order to do so, we will first need a small helper to
weaken the scope of NF strategies.

#definition[NF Strategy Renaming][
  Assuming a scope structure $ctx.scope_T th S$, given a binding family $O cl
  ctx.bfam_T th S$ and a scope $Omega cl S$, define the _active and passive NF strategy
  renamings_ by mutual coinduction as follows.

  $ nf.renA th {Omega th Gamma_1 th Gamma_2} cl nf.stratA th Omega th Gamma_1 -> Gamma_1 ctx.ren Gamma_2 -> nf.stratA th Omega th Gamma_2 \
    nf.renA th s th rho := \
    pat(itree.obs := kw.case s .itree.obs \
        pat(itree.retF th r & := itree.retF th r,
            itree.tauF th t & := itree.tauF th (nf.renA th t th rho),
            itree.visF th (i ctx.cute o) th k & := itree.visF th (rho th i ctx.cute o) th (nf.renP th k th rho))
    ) \
    \
    nf.renP th {Omega th Gamma th Delta_1 th Delta_2} cl nf.stratP th Omega th Gamma th Delta_1 -> Delta_1 ctx.ren Delta_2 -> nf.stratP th Omega th Gamma th Delta_2 \
    nf.renP th k th rho th m := nf.renA th (k th m) th [rho dot ctx.rcatl, ctx.rcatr] $

  This defines two renaming structures, on $nf.stratA th Omega$ and $nf.stratP th Omega th Gamma$.
]

#definition[NF to OGS][
  Assuming a scope structure $ctx.scope_T th S$, given a binding family $O cl
  ctx.bfam_T th S$ and a scope $Omega cl S$, define as follows the _active and
  passive embedding from NF strategies to OGS strategies_.

  $ nf.nf2ogsA th {Omega th Psi} cl nf.stratA th Omega th (ogs.catE Psi) -> nf.stratP th Omega th (ogs.catO Psi) th (ogs.catE Psi) -> ogs.stratA th Omega th Psi \
    nf.nf2ogsA th s th italic("ks") := \
    pat(itree.obs := kw.case th s.itree.obs \
      pat(itree.retF th r & := itree.retF r,
          itree.tauF th t & := itree.tauF th (nf.nf2ogsA th t th italic("ks")),
          itree.visF th m th k & := itree.visF th m th (nf.nf2ogsP th [italic("ks"), k]))
    ) \
    \
    nf.nf2ogsP th {Omega th Psi} cl nf.stratP th Omega th (ogs.catE Psi) th (ogs.catO Psi) -> ogs.stratP th Omega th Psi \
    nf.nf2ogsP th italic("ks") th m := nf.nf2ogsA th (italic("ks") th m) th italic("ks")[ctx.rcatr] $

  Finally, define the following shorthand, embedding NF strategies to OGS strategies over an
  initial position.

  $ nf.nf2ogs th {Omega th Gamma} cl nf.stratA th Omega th Gamma -> ogs.stratA th Omega th (ctx.nilc ctx.conc Gamma) \
    nf.nf2ogs th s := nf.nf2ogsA th s th [] $
]

== Normal Form Bisimulation Correctness

We can now show that the OGS interpretation can be factorized through the NF interpretation.

#theorem[OGS Through NF Factorization][
  Given a language machine $M cl ogs.machine th O th V th C$ with renamings
  and a final
  scope $Omega cl S$, the OGS interpretation factorizes through the NF interpretation.
  More precisely, for any $c cl C th Gamma$, the following property holds.

  $ ogsinterpA(c) game.eqA nf.nf2ogs th (nfinterpA(c)) $
] <thm-ogs-nf-facto>
#proof[
  The only trick required to prove this is to generalize the statement to arbitrary OGS
  game positions and machine strategy states. We prove that for any $Psi cl
  ctx.ctxc th S$, $c cl C th (Omega ctx.cat ogs.catE Psi)$ and $e cl
  ogs.teleA th Psi$ the following property holds.

  $ & itree.unrollA_(ogs.mstrat th M) th (c ctx.cute e) \
    game.eqA & nf.nf2ogsA th (itree.unrollA_(nf.mstrat th M) th c) th (itree.unrollP_(nf.mstrat th M) th (ogs.collA e)) $

  This statement is proven by direct coinduction. The result follows by taking
    $Psi := ctx.nilc ctx.conc Gamma$, $c' := c[ctx.rcatr]$ and $e := []$.
]

In order to finally prove NF bisimulation correctness, we still need to show
that $nf.nf2ogs$ is monotone with respect to weak bisimilarity.
However, because we have used NF strategy renaming in the definition of $nf.nf2ogsA$, we
will first need an up-to-renaming reasoning principle for NF strategies.

#lemma[NF Bisimulation Up-to Renaming][
  Assuming a scope structure $ctx.scope_T th S$, a binding family $O cl
  ctx.bfam_T th S$ and a scope $Omega cl S$, then $nf.renA th {Omega}$ is
  monotone w.r.t. any member of the strong bisimulation tower and of
  the weak bisimulation tower, i.e., for any

  #box($ x in tower.t_(itree.sb_nf.g) quad quad "or" quad quad x in tower.t_(itree.wb_nf.g), $)

  the following property holds.

  $ nf.renA th {Omega} xrel(rel.forall th {Gamma_1 th Gamma_2} -> x th cnorm(approx)  rel.arr cnorm(approx) rel.arr x th cnorm(approx)) nf.renA th {Omega} $
] <lem-nf-ren-mono>
#proof[
  Although slightly scary, both statement are proven by direct tower induction.
]

In fact, it should be no surprise that a bunch of other monotonicity properties
also hold. Although we will only really use (2) for correctness, proving the
other ones is just as easy.

#lemma[NF Monotonicity][
  #let ks1 = $italic("ks"_1)$
  #let ks2 = $italic("ks"_1)$
  Assuming a scope structure $ctx.scope_T th S$, a binding family $O cl
  ctx.bfam_T th S$, the following monotonicity properties hold.
  #peio[introduire $game.eqA$ et $game.eqP$]

  1. $nf.nf2ogsA xrel(cnorm(game.eqA)  rel.arr cnorm(game.eqP)  rel.arr cnorm(game.eqA)) nf.nf2ogsA$
  2. $nf.nf2ogsA xrel(cnorm(game.weqA) rel.arr cnorm(game.weqP) rel.arr cnorm(game.weqA)) nf.nf2ogsA$
  3. $nf.ogs2nfA xrel(cnorm(game.eqA)  rel.arr cnorm(game.eqA))  nf.ogs2nfA$
  4. $nf.ogs2nfA xrel(cnorm(game.weqA) rel.arr cnorm(game.weqA)) nf.ogs2nfA$
] <lem-nf-mono>
#proof[
  All by direct coinduction, with (1) and (2) using @lem-nf-ren-mono.
]

We can now prove the normal form bisimulation correctness theorem.

#theorem[NF Correctness][
  Assming the same set of hypotheses as OGS correctness (@thm-correctness), NF bisimulations
  are correct w.r.t. substitution equivalence, i.e., for any $c_1, c_2 cl C th Gamma$, the
  following statement holds.

  $ nfinterpA(c_1) game.weqA nfinterpA(c_2) -> c_1 ogs.subeq c_2 $
]
#proof[
  Assume $c_1$ and $c_2$ such that $nfinterpA(c_1) game.weqA nfinterpA(c_2)$. By @thm-correctness
  it is sufficient to prove $ogsinterpA(c_1) game.weqA ogsinterpA(c_2)$.

  $ ogsinterpA(c_1) th th & game.eqA nf.nf2ogs th (nfinterpA(c_1)) quad quad quad & #[(@thm-ogs-nf-facto)] \
                    & game.weqA nf.nf2ogs th (nfinterpA(c_2)) & #[(@lem-nf-mono (2))] \
                    & game.eqA ogsinterpA(c_2) & #[(@thm-ogs-nf-facto)] $
  #v(-2em)
]

The above correctness theorem concludes our treatment of normal form
bisimulations. There is definitely more to explore, in particular a more
precise comparison of the two games 

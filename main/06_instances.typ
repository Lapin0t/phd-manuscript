#import "/lib/all.typ": *

= OGS Instances

In @ch-ogs we have seen a language-generic OGS construction, parametrized by an
abstract notion of language machine. We have even seen a shiny theorem,
correction for this model w.r.t. substitution  equivalence, our variant of
observational equivalence. Hopefully some intuitions from the introduction
helped understand these abstract constructions, but it is now time to look at
some concrete examples. In this chapter we try to show a small but
representative collection of calculi that are covered by our abstract theorem.
We start with two calculi neatly fitting the language machine presentation, a
very simple one for warming up, Jump-with-Argument (@sec-inst-jwa) and a quite
featureful one, polarized #short.uuc (@sec-inst-mumu). Then, in @sec-inst-nd,
we give some more details on the "named term" construction sketched in the
introduction. Indeed, some languages such as #short.llc do not directly make
sense as language machines, mostly because the notion of _configuration_ and
our peculiar choice of normal form representation are alien to their standard
presentation. In order to treat them idiomatically, we provide a more fitting
axiomatization of such languages, comprising terms, values and evaluation
contexts and we then show how to derive a language machine from this new
axiomatization, in a sort of lightweight CPS transform. We then use this
refined axiomatization to instanciate OGS with pure untyped #short.llc,
demonstrating how untyped calculi are handled.

== Jump-with-Argument <sec-inst-jwa>

=== Syntax

Jump-with-Argument (JWA) was introduced by #nm[Levy]~#mcite(<Levy04>) as a
target for his _stack passing style_ transform of Call-By-Push-Value
(CBPV). As such, it is a minimalistic language with first-class
continuations centered around so-called _non-returning commands_: an ideal
target for our first language machine. We will assume some familiarity with the
language and refer the reader to #nm[Levy]~#num-cite(<Levy04>) as a more gentle
entry point. In fact we also direct the interested reader to two existing
constructions of normal form bisimulation and OGS construction for increasingly
featureful variants of JWA by #nm[Levy] and
#nm[Lassen]~#mcite(<LassenL07>)#mcite(dy: 3em, <LassenL08>). This is typed
language, so as is usual, there is some leeway regarding which types are
included. As we are aiming for simplicity, we will only look at a
representative fragment featuring three types of values: booleans $jwa.base$,
continuations $jwa.neg A$ and pairs $A jwa.prod B$.

The language consists of two judgments: commands and values. Commands play the
role of the configurations of an abstract machine, and are only parametrized by
a scope. They are of three kinds: sending a value to a continuation (the
eponymous "jump with argument"), splitting a value of product type into its
two components and case splitting on a boolean. Values are parametrized by a
scope and a type and can be either a variable, a continuation abstraction, a
pair or a boolean. Let us present its syntax by an intrinsically typed and scoped
representation inside type theory.

#definition[Syntax][JWA types are given by the following data type.

#mathpar(block: true,
$ kw.dat jwa.typ cl base.Type \
  pat(
    jwa.base cl jwa.typ,
    jwa.neg ar cl jwa.typ -> jwa.typ,
    ar jwa.prod ar cl jwa.typ -> jwa.typ -> jwa.typ,
  ) $
)

Define the two syntactic judgments by the following two mutually inductive data types.

$ kw.dat th ar jwa.jcmd cl ctx.ctxc th jwa.typ -> base.Type \
  kw.dat th ar jwa.jval ar cl ctx.ctxc th jwa.typ -> jwa.typ -> base.Type $

We will also use the shorthands $jwa.cmd := ar jwa.jcmd$ and $jwa.val := ar
jwa.jval ar$ when it is more practical. The constructors are as follows.

#mathpar(block: true, spacing: 1em,
  inferrule($x cl Gamma ctx.varc A$, $jwa.vvar th x cl Gamma jwa.jval A$),
  inferrule("", $jwa.vyes cl Gamma jwa.jval jwa.base$),
  inferrule("", $jwa.vno cl Gamma jwa.jval jwa.base$, suppl: h(4em)),
  inferrule(
    ($c cl Gamma ctx.conc A jwa.jcmd$),
    $jwa.vlam c cl Gamma jwa.jval jwa.neg A$
  ),
  inferrule(
    ($v cl Gamma jwa.jval A$, $w cl Gamma jwa.jval B$),
    $jwavpair(v, w) cl Gamma jwa.jval A jwa.prod B$
  ),
  inferrule(
    ($v cl Gamma jwa.jval jwa.base$, $c_1 cl Gamma jwa.jcmd$, $c_2 cl Gamma jwa.jcmd$),
    $jwacasein(v, c_1, c_2) cl Gamma jwa.jcmd$
  ),
  inferrule(
    ($v cl Gamma jwa.jval A$, $k cl Gamma jwa.jval jwa.neg A$),
    $v jwa.capp k cl Gamma jwa.jcmd$
  ),
  inferrule(
    ($v cl Gamma jwa.jval A jwa.prod B$, $c cl Gamma ctx.conc A ctx.conc B jwa.jcmd$),
    $jwaletin(v, c) cl Gamma jwa.jcmd$
  ),
)
#margin-note(dy: -7em)[
  Note that we do not include the standard $jwaxxletin(v,c)$ command, as it can be simply derived
  as $v jwa.capp jwa.vlam c$.
]
]

#lemma[Substitution][
  JWA values form a substitution monoid, and JWA commands form a substitution
  module over it. Moreover, $jwa.val$ has decidable variables. In other
  words, the following typeclasses are inhabited: $sub.mon th jwa.val$,
  $sub.mod th jwa.val jwa.cmd$ and $sub.decvar th jwa.val$.
] <lem-jwa-sub>
#proof[
  Although quite tedious, these constructions are entirely
  standard~#mcite(<FioreS22>)#mcite(dy: 1.8em, <AllaisACMM21>). One essentially starts by
  mutually defining the renaming structures on commands and values, unlocking the definition
  of the weakening operation necessary for substitution. Then, on top of this,
  one mutually defines the monoid and module structures. The proofs of the laws as similarly
  layered.
]

=== Patterns and Negative Types

The next logical step is the definition of the evaluation. Informally the reduction rules
are defined on commands as follows.

$ v jwa.capp jwa.vlam c & quad ~> quad c[sub.var,v] \
  jwaletin(jwavpair(v, w), c) & quad ~> quad c[sub.var,v,w] \
  jwacasein(jwa.vyes, c_1, c_2) & quad ~> quad c_1 \
  jwacasein(jwa.vno, c_1, c_2) & quad ~> quad c_2 $
#margin-note(dy: -6em)[
  Note the usage of the assignments $[sub.var,v]$ and $[sub.var,v,w]$ for
  substituting only the top variables, leaving the rest unchanged (with the
  identity assignment $sub.var$).
]

However, recall that in a language machine, the evaluator should return a normal
form configuration, which is to be expressed using a binding family of
_observations_. As the definition of observations is central and essentially
decides the shape that the OGS model will take, let us take a small step back.

Recall from the introduction that in OGS models, depending on their type, some
values are "given" to the opponent as part of a move, while some other are
"hidden" behind fresh variables. We did not, however, worry about this
distinction at all during our generic development, as we simply assumed there
was a set of types $T$ and worked on top of that. This discrepancy is simply
explained: what the generic construction considers as _types_ should not be
instanciated to all of our language's types, but only the ones that are
interacted with, i.e., the "hidden" types.

Most eloquently described in the case of CBPV~#mcite(<Levy04>), this split
occurs between types that have dynamic behavior, the _computation types_ and
the ones that have static content, the _value types_. For concision we will
call them respectively _negative_ and _positive_ types. Although the concrete
assignment of types to either category can be somewhat varied, obtaining models
with different properties, for JWA it is most natural to decide that
continuations are negative types and that all the other are positive.

#definition[Negative Types][
The definition of JWA negative types is based on a predicate picking out
the continuation types.

#mathpar(block: true,
block[$ jwa.isneg cl jwa.typ -> base.Prop $
#v(-0.8em)
$ & jwa.isneg th jwa.base && := base.bot \
  & jwa.isneg th jwa.neg A && := base.top \
  & jwa.isneg th (A jwa.prod B) && := base.bot $],
block(height: 6em, align(horizon,
    $ jwa.ntyp := base.int_jwa.typ jwa.isneg \
      jwa.nctx := base.int_(ctx.ctxc th jwa.typ) (ctx.all th jwa.isneg) $))
)
]
#remark[
  Note that to manipulate the above contexts and types, we will make great use
  of the _subset scope_ structure introduced in @def-subset-scope.

  Further, as $jwa.isneg$ is trivially decidable, we will allow ourselves a bit
  of informality by using $jwa.neg A$ as a negative type, instead of the more
  correct $(jwa.neg A, base.tt)$. Moreover, we will do as if elements of $jwa.ntyp$
  could be pattern-matched on, with the sole pattern being $jwa.neg A$, although
  technically this has to be justified with a
  _view_~#mcite(<McBrideM04>)#mcite(dy: 2em, <Allais23>).
]

#lemma[Restricted Values and Commands][
  The family of values and commands restricted to negative scopes and types defined as

  $ (kw.fun th Gamma th alpha |-> jwa.val th Gamma .base.fst th alpha .base.fst) cl base.Type^(jwa.nctx,jwa.ntyp) \
    (kw.fun th Gamma |-> jwa.cmd th Gamma .base.fst) cl base.Type^jwa.nctx $

  again form respectively a substitution monoid and a substitution module. We will
  overload the notations $jwa.val$ and $jwa.cmd$ for both the unrestricted and restricted
  families. Similarly we will drop the projections $base.fst$ and implicitely treat negative
  types and scopes as normal ones.
]
#proof[By #sym.eta\-expansion of the records and functions witnessing the unrestricted structures.]

For these negative types, i.e., continuations, we need to devise a notion of
observation which will make up the content of the OGS moves. The only sensible
thing to do with a continuation $jwa.neg A$ is to send it a something of type
$A$, and as our goal is to hide continuations from moves, this something should
be void of any continuation abstraction. This can be recognized as the set of
_ultimate patterns_ of type $A$, i.e., maximally deep patterns of type $A$.

#definition[Ultimate Patterns and Observations][
  Define the inductive family of ultimate patterns $kw.dat th jwa.pat cl jwa.typ -> base.Type$
  with the following constructors.

  #v(-1em)
  #mathpar(block: true, spacing: 0em,
    inferrule($$, $jwa.pyes cl jwa.pat th jwa.base$),
    inferrule($$, $jwa.pno cl jwa.pat th jwa.base$),
    inferrule($$, $jwa.plam_A cl jwa.pat th jwa.neg A$),
    //inferrule($p cl jwa.pat th A$, $jwa.pinl th p cl jwa.pat th (A jwa.sum B)$),
    //inferrule($p cl jwa.pat th B$, $jwa.pinr th p cl jwa.pat th (A jwa.sum B)$),
    inferrule(($p cl jwa.pat th A$, $q cl jwa.pat th B$), $jwappair(p, q) cl jwa.pat th (A jwa.prod B)$),
  )

  Define their _domain_ by the following inductive function.

  $ jwa.dom th {A} cl jwa.pat th A -> ctx.ctxc th jwa.ntyp $
  #v(-0.8em)
  $ & jwa.dom th jwa.plam_A   && := ctx.nilc ctx.conc jwa.neg A \
    & jwa.dom th jwa.pyes && := ctx.nilc \
    & jwa.dom th jwa.pno && := ctx.nilc \
    & jwa.dom th jwappair(p, q) && := jwa.dom p ctx.catc jwa.dom q $

  Finally define _observations_ as the following binding family.

  $ jwa.obs cl ctx.bfam th jwa.nctx th jwa.ntyp \
    jwa.obs := pat(
      ctx.Oper th jwa.neg A & := jwa.pat th A,
      ctx.dom th p & := jwa.dom th p
    ) $
]

The first thing to do with ultimate patterns is to show how to embed them into values.

#definition[Ultimate Pattern Embedding][
  Ultimate patterns can be embedded into values, as witnessed by the following
  inductive function.

  $ jwa.p2v th {A} th (p cl jwa.pat th A) : jwa.dom th p jwa.jval A $
  #v(-0.8em)
  $ & jwa.p2v th jwa.plam_A   && := jwa.vvar ctx.topc \
    & jwa.p2v th jwa.pyes && := jwa.vyes \
    & jwa.p2v th jwa.pno && := jwa.vyes \
    & jwa.p2v th jwappair(p, q) && := jwavpair((jwa.p2v th p)[ctx.rcatl], (jwa.p2v th q)[ctx.rcatr]) $
]

The next step is to do the reverse: given a value whose scope is entirely negative (as will happen
during the OGS game), split it into an ultimate pattern and a filling assignment.

#remark[The fact that
  we only do this in negative scopes is important as we will be able to refute the case of, e.g.
  a variable of type $jwa.base$. Indeed, assuming a scope structure $ctx.scope_T
  th S$ and a predicate $P cl base.Prop^T$, define the following function,
  "upgrading" a type into a proof that it verifies $P$, provided we know that it
  is a member of a $P$-subscope.

  $ ctx.eltupg th {Gamma cl base.int_S th (ctx.all th P)} th {x} cl Gamma .base.fst ctx.var x -> P th x \
    ctx.eltupg th i := Gamma .base.snd th i $
]

#definition[Value Splitting][
  Define the following functions, splitting values in negative context into a pattern and an
  assignment over its domain.

  $ jwa.v2p th {Gamma cl jwa.nctx} th (A cl jwa.typ) cl Gamma jwa.jval A -> jwa.pat th A $
  #v(-0.8em)
  $ & jwa.v2p th jwa.base th && (jwa.vvar th i) && := base.exfalso th (ctx.eltupg th i) \
    & jwa.v2p th jwa.base th && jwa.vyes      && := jwa.pyes \
    & jwa.v2p th jwa.base th && jwa.vno      && := jwa.pno \
    & jwa.v2p th jwa.neg A  th && v      && := jwa.plam_A \
    & jwa.v2p th (A jwa.prod B) th && (jwa.vvar th i) && := base.exfalso th (ctx.eltupg th i) \
    & jwa.v2p th (A jwa.prod B) th && jwavpair(v, w) && := jwappair(jwa.v2p th A th v, jwa.v2p th B th w) $

  $ jwa.v2a th {Gamma cl jwa.nctx} th A th (v cl Gamma jwa.jval A) cl jwa.dom th (jwa.v2p th v) asgn(jwa.val) Gamma $
  #v(-0.8em)
  $ & jwa.v2a th jwa.base th && (jwa.vvar th i) && := base.exfalso th (ctx.eltupg th i) \
    & jwa.v2a th jwa.base th && jwa.vyes      && := [] \
    & jwa.v2a th jwa.base th && jwa.vno      && := [] \
    & jwa.v2a th jwa.neg A  th && v      && := [ th v th ] \
    & jwa.v2a th (A jwa.prod B) th && (jwa.vvar th i) && := base.exfalso th (ctx.eltupg th i) \
    & jwa.v2a th (A jwa.prod B) th && jwavpair(v, w) && := [ th jwa.v2a th A th v, jwa.v2a th B th w th ] $
]

Before moving on towards evaluation, we can prove our first interesting lemma,
namely that splitting a value and refolding it yields the same value unchanged and
that this splitting is unique.

#lemma[Refolding][
  The following statements holds.

  1. For all $Gamma cl jwa.nctx$, $A cl jwa.typ$ and $v cl Gamma jwa.jval A$,
    $ (jwa.p2v th (jwa.v2p th v))[jwa.v2a th v] = v. $
  2. For all $Gamma cl jwa.nctx$, $A cl jwa.typ$, $p cl jwa.pat th A$ and $gamma cl jwa.dom th p asgn(jwa.val) Gamma$,
    $ (p, gamma) approx (jwa.v2p th (jwa.p2v th p)[gamma], jwa.v2a th (jwa.p2v th p)[gamma]). $

  Note the second equation lives in $(p cl jwa.pat th A) base.prod (jwa.dom th p asgn(jwa.val) Gamma)$, with
  extensional equality $approx$ here meaning equality on the first projections and pointwise equality on the
  second.
] <lem-jwa-refold>
#proof[
  Both by direct induction, following the same case pattern as $jwa.v2p$ and $jwa.v2a$. 
]

=== The JWA Language Machine

Lets recapitulate where we stand in the instanciation. We have defined the
negative types $jwa.ntyp$ and scopes $jwa.nctx$, as well as the matching
observation family $jwa.obs cl ctx.bfam th jwa.nctx th jwa.ntyp$. We have
defined values $jwa.val$ and commands $jwa.cmd$ over general types and then
restricted them to negative types and scopes. To instanciate a language
machine, this leaves us to define the evaluation and application maps, which
have the following types.

$ ogs.eval th {Gamma cl jwa.nctx} cl jwa.cmd th Gamma -> delay.t th (ctx.norm^(""jwa.obs)_jwa.val th Gamma) \
  ogs.apply th {Gamma cl jwa.nctx} th {A cl jwa.ntyp} th (v cl jwa.val th Gamma th A) th (o cl jwa.obs"".ctx.Oper th Gamma th alpha) \
    quad cl jwa.obs"".ctx.dom th o asgn(jwa.val) Gamma -> jwa.cmd th Gamma $

Let us start with the evaluation map. Although it is not really necessary, for
clarity we will implement an _evaluation step_ function, taking a command
either a normal form or to a new command to be evaluated. The evaluation map is
then simply obtained by iteration in the #delay.t monad.

#definition[Evaluation][
  Define evaluation by iteration of an evaluation step as follows.

  $ jwa.eval th {Gamma cl jwa.nctx} cl jwa.cmd th Gamma -> delay.t th (ctx.norm^(""jwa.obs)_jwa.val th Gamma) \
    jwa.eval := itree.iter th (itree.ret compose jwa.evalstep) $

  $ jwa.evalstep th {Gamma cl jwa.nctx} cl jwa.cmd th Gamma -> ctx.norm^(""jwa.obs)_jwa.val th Gamma base.sum jwa.cmd th Gamma $
  #v(-0.8em)
  $ & jwa.evalstep th (jwacasein((jwa.vvar th i), c_1, c_2)) && := base.exfalso th (ctx.eltupg th i) \
    & jwa.evalstep th (jwacasein(jwa.vyes, c_1, c_2)) && := base.inj2 th c_1 \
    & jwa.evalstep th (jwacasein(jwa.vno, c_1, c_2))  && := base.inj2 th c_2 \
    & jwa.evalstep th (v jwa.capp jwa.vvar th i)      && := base.inj1 th ((i ctx.cute jwa.v2p th v), jwa.v2a th v) \
    & jwa.evalstep th (v jwa.capp jwa.vlam c)         && := base.inj2 th c[sub.var,v] \
    & jwa.evalstep th (jwaletin((jwa.vvar th i), c))  && := base.exfalso th (ctx.eltupg th i) \
    & jwa.evalstep th (jwaletin(jwavpair(v,w), c))    && := base.inj2 th c[sub.var,v,w] \
    $
]

The next and final step is to define the application map, which is easily done. The target
type

$ jwa.apply th {Gamma cl jwa.nctx} th {A cl jwa.ntyp} th (v cl jwa.val th Gamma th A) th (o cl jwa.obs"".ctx.Oper th A) \
    quad cl jwa.obs"".ctx.dom th o asgn(jwa.val) Gamma -> jwa.cmd th Gamma $

is perhaps slightly scary, but this is largely due to the fact that $A$ is
quantified over negative types, instead of explicitely asking that it is a
continuation type. This is an artifact of the language machine axiomatization and in this
case it would be better written with the following isomorphic representation.

$ jwa.apply th {Gamma cl jwa.nctx} th {A cl jwa.typ} th (v cl jwa.val th Gamma th jwa.neg A) th (o cl jwa.pat th A) \
    quad cl jwa.dom o asgn(jwa.val) Gamma -> jwa.cmd th Gamma $

#definition[Observation Application][
  Define observation application as follows.

  $ jwa.apply th {Gamma cl jwa.nctx} th {A cl jwa.ntyp} th (v cl jwa.val th Gamma th A) th (o cl jwa.obs"".ctx.Oper th A) \
    quad cl jwa.obs"".ctx.dom th o asgn(jwa.val) Gamma -> jwa.cmd th Gamma \
    jwa.apply th {Gamma} th {jwa.neg A} th v th o th gamma := (jwa.p2v th o)[gamma] jwa.capp v $
]

We now have everything to instanciate the JWA language machine.

#definition[Language Machine][
  The JWA language machine is given by the following record.

  $ jwa.jwa cl ogs.machine th jwa.obs th jwa.val th jwa.cmd \
    jwa.jwa := pat(
      ogs.eval   & := jwa.eval,
      ogs.apply  & := jwa.apply,
      ogs.appext & := ...
    ) $

  Note that $ogs.appext$ is proven by direct application of $sub.sext$ from the
  substitution monoid structure of values.
]

By the above definition we already can already instanciate the OGS model, but
to obtain correctness w.r.t. substitution equivalence, we need to verify the
hypotheses of @thm-correctness. We are left with the two interesting
hypotheses: the core semantic argument, the JWA machine respects substitution
(@def-machine-resp-sub), and the technical side condition, that it has finite
redexes (@def-finite-redex).

#lemma[JWA Respects Substitution][
  The JWA language machine respects substitution, i.e., the following typeclass is
  inhabited: $ogs.submachine th jwa.jwa$.
] <thm-jwa-respsub>
#proof[ \
  $ogs.evalsub$ #sym.space.quad Given $Gamma, Delta cl jwa.nctx$, $c cl jwa.cmd th Gamma$ and $sigma cl Gamma asgn(jwa.val) Delta$,
  we need to prove the following.

  $ jwa.eval th c[sigma] itree.eq jwa.eval th c itree.bind kw.fun th n |-> jwa.eval th (ogs.emb th n)[sigma] $

  Proceed by coinduction and then by cases on $c$, following the elimination
  pattern of $jwa.evalstep$.

  - $jwacasein((jwa.vvar th i), c_1, c_2)$ #sym.space.quad Impossible by $base.exfalso th (ctx.eltupg th i)$.
  - $jwacasein(jwa.vyes, c_1, c_2)$ #sym.space.quad Unfold one coinductive layer of the RHS and rewrite as
    follows.
    $        & (jwa.eval th (jwacasein(jwa.vyes, c_1, c_2))[sigma] ).itree.obs quad quad & \
      = quad & (jwa.eval th (jwacasein(jwa.vyes, c_1[sigma], c_2[sigma])) ).itree.obs quad quad & #[by def.] \
      = quad & itree.tauF th (jwa.eval th c_1[sigma]) & #[by def.] $
    Similarly, after unfolding, the RHS reduces to $ itree.tauF th (jwa.eval th c_1 itree.bind kw.fun th n |-> jwa.eval th (ogs.emb th n)[sigma]). $
    The two $itree.tauF$ provide a synchronization and we conclude by coinduction hypothesis on $c_1$.
  - $jwacasein(jwa.vno, c_1, c_2)$ #sym.space.quad Same as previous case, with $c_2$.
  - $v jwa.capp jwa.vvar th i$ #sym.space.quad The LHS reduces to $jwa.eval th (v[sigma] jwa.capp sigma th i)$.
    In the RHS, the first evaluation unfolds and reduces to $itree.retF th ((i ctx.cute jwa.v2p th v), jwa.v2a th v)$,
    so that the RHS as a whole can be rewritten to $ jwa.eval th (ogs.emb th ((i ctx.cute jwa.v2p th v), jwa.v2a th v))[sigma] $
    We rewrite and conclude as follows.
    $   & (ogs.emb th ((i ctx.cute jwa.v2p th v), jwa.v2a th v))[sigma] & \
      = quad & (jwa.apply th (jwa.vvar th i) th (jwa.v2p th v) th (jwa.v2a th v))[sigma] quad & #[by def.] \
      = quad & ((jwa.p2v th (jwa.v2p th v))[jwa.v2a th v] jwa.capp (jwa.vvar th i))[sigma] quad & #[by def.] \
      = quad & (v jwa.capp (jwa.vvar th i))[sigma] quad & #[by @lem-jwa-refold] \
      = quad & v[sigma] jwa.capp (sigma th i) quad & #[by def.] $
  - $v jwa.capp jwa.vlam c'$ #sym.space.quad Unfold the LHS and rewrite as follows.
    $ & (jwa.eval th (v jwa.capp jwa.vlam c')[sigma]) .itree.obs & \
      & (jwa.eval th (v[sigma] jwa.capp jwa.vlam c'[sigma[ctx.popc],ctx.topc])) .itree.obs & \
      = quad & itree.tauF th (jwa.eval th c'[sigma[ctx.popc],ctx.topc][sub.var,v[sigma]]) quad & #[by def.] \
      = quad & itree.tauF th (jwa.eval th c'[sub.var,v][sigma]) quad & #[by sub. fusion] $
    Unfolding the RHS reduces to $ itree.tauF th (jwa.eval th c'[sub.var,v] itree.bind kw.fun th n |-> jwa.eval th (ogs.emb th n)[sigma]). $
    The two $itree.tauF$ provide a synchronization and we conclude by coinduction hypothesis on $c'[sub.var,v]$

  - $jwaletin((jwa.vvar th i), c')$ #sym.space.quad Impossible by $base.exfalso th (ctx.eltupg th i)$.
  - $jwaletin(jwavpair(v,w), c')$ #sym.space.quad Unfold the LHS and rewrite as follows.
    $ & (jwa.eval th (jwaletin(jwavpair(v,w), c'))[sigma]) .itree.obs & \
      & (jwa.eval th (jwaletin(jwavpair(v[sigma],w[sigma]), c'[sigma[ctx.popc compose ctx.popc, ctx.popc th ctx.topc, ctx.topc]]))) .itree.obs quad & #[by def.] \
      & itree.tauF th (jwa.eval th c'[sigma[ctx.popc compose ctx.popc], ctx.popc th ctx.topc, ctx.topc][sub.var,v[sigma],w[sigma]]) quad & #[by def.] \
      & itree.tauF th (jwa.eval th c'[sub.var,v,w][sigma]) quad & #[by sub. fusion] \
    $
    Unfolding the RHS reduces to $ itree.tauF th (jwa.eval th c'[sub.var,v,w][sigma] itree.bind kw.fun th n |-> jwa.eval th (ogs.emb th n)[sigma]). $
    The two $itree.tauF$ provide a synchronization and we conclude by coinduction hypothesis on $c'[sub.var,v,w]$

  This concludes $ogs.evalsub$. Although slightly tedious, it is not hard to prove. As we will
  see in other instances, the pattern is always the same: analyzing the configuration to make
  the evaluation reduce, upon hitting a redex, shift substitutions around and conclude by coinduction.
  Upon hitting a normal form, apply a refolding lemma and conclude by reflexivity.

  Thankfully the other two properties are almost trivial. $ogs.appsub$ is a
  direct application of substitution fusion.

  $        & jwa.apply th v[sigma] th o th gamma[sigma] & \
    = quad & (jwa.p2v th o)[gamma[sigma]] jwa.capp v[sigma] quad quad & #[by def.] \
    = quad & ((jwa.p2v th o)[gamma] jwa.capp v)[sigma] quad quad & #[by sub. fusion] \
    = quad & (jwa.apply th v th o th gamma)[sigma] & #[by def.] $

  $ogs.evalnf$ is proven by unicity of splitting after one-step unfolding.

  $        & (jwa.eval th (ogs.emb th ((i ctx.cute o), gamma))) .itree.obs & \
    = quad & (jwa.eval th (jwa.apply th (jwa.vvar th i) th o th gamma)) .itree.obs quad & #[by def.] \
    = quad & (jwa.eval th ((jwa.p2v th o)[gamma] jwa.capp th jwa.vvar th i)) .itree.obs quad & #[by def.] \
    = quad & itree.retF th ((i ctx.cute jwa.v2p th (jwa.p2v th o)[gamma]), jwa.v2a th (jwa.p2v th o)[gamma] quad & #[by def.] \
    = quad & itree.retF th ((i ctx.cute o), gamma) quad & #[by @lem-jwa-refold]
    $
]

#lemma[JWA Finite Redexes][
  The JWA language machine has finite redexes.
] <thm-jwa-finred>
#proof[
  Once again, we do a benign preprocessing to express the property using
  patterns instead of observations, for else the notational weight would be
  unbearable. We need to prove that the following relation is well founded.

  #inferrule(
    ($i cl Gamma ctx.var alpha_1$,
     $o_1 cl jwa.pat th alpha_1$,
     $gamma_1 cl jwa.dom th o_1 asgn(jwa.val) Gamma$,
     $v cl jwa.val th Gamma th jwa.neg alpha_2$,
     $o_2 cl jwa.pat th alpha_2$,
     $gamma_2 cl jwa.dom th o_2 asgn(V) Gamma$,
     $H_1 cl sub.isvar th v -> base.bot$,
     $H_2 cl jwa.eval th (jwa.apply th v th o_2 th gamma) itree.eq itree.ret th ((i ctx.cute o_1), gamma_1)$
    ),
    $ogs.badc th H_1 th H_2 cl o_1 ogs.badinst o_2$
  )

  Let $alpha_2 cl jwa.ntyp$ and $o_2 cl jwa.pat th alpha_2$. By the
  accessibility constructor, we need to prove that for any $alpha_1$ and $o_1
  cl jwa.pat th alpha_1$ such that $o_1 ogs.badinst o_2$, $o_1$ is
  accessible. Destruct the proof of $o_1 ogs.badinst o_2$, introduce all
  the hypotheses as above and proceed by case on $v$, as it is a continuation value,
  it can be either an abstraction or a variable. If $v := jwa.vlam th c$,
  $jwa.apply th v th o_2 th gamma$ reduces to $(jwa.p2v th o_2)[gamma]
  jwa.capp th jwa.vlam c$. This is a redex, thus its evaluation start with
  #itree.tauF and thus $H_2$ is absurd as the RHS starts with #itree.retF. If instead $v
  := jwa.vvar th i$, then $H_1$ is absurd.
]

#remark[
  The above proof of finite redex is quite remarkable: no "bad instanciation" can happen,
  and evaluating the application of a non-variable value _always_ creates a redex. "Low-level"
  languages such as JWA which are designed around first-class continuations
  usually have this stronger property.
]

This concludes the proof of the hypotheses for correctness. We may now deduce
OGS correctness for JWA. We will do it with respect to the standard final scope
$Omega := ctx.nilc ctx.conc jwa.neg jwa.base$ containing exactly one boolean
continuation. To match common practice, we also adapt the definition of substitution
equivalence to use a notion of big-step reduction $c arrow.b.double b$.

#definition[Evaluation Relation][
  For $c cl jwa.cmd th (ctx.nilc ctx.conc jwa.neg jwa.base)$ and $b cl jwa.pat th jwa.base$, define the following
  big step _evaluation relation_.

  $ c arrow.b.double b := (base.fst itree.fmap jwa.eval th c) itree.weq itree.ret th (ctx.topc ctx.cute b) $
]

#theorem[OGS Correctness][
  For all $Gamma cl jwa.nctx$ and $c_1, c_2 cl jwa.cmd th Gamma$, if
  $ogsinterpA(c_1) itree.weq ogsinterpA(c_2)$, then for all $gamma cl Gamma
  asgn(jwa.val) (ctx.nilc ctx.conc jwa.neg jwa.base)$, $ c_1[gamma] arrow.b.double jwa.pyes <-> c_2[gamma] arrow.b.double jwa.pyes. $
] <thm-jwa-correctness>
#proof[
  By @thm-correctness applied to $jwa.jwa$, with hypotheses proven in @lem-jwa-sub, @thm-jwa-respsub and @thm-jwa-finred,
  obtain $ base.fst itree.fmap jwa.eval th c_1[gamma] quad itree.weq quad base.fst itree.fmap jwa.eval th c_2[gamma]. $
  Conclude by the fact that $itree.weq$ is an equivalence relation.
  #margin-note(dy: -6em)[
    For the beauty of the game, let us say that a tiny generalization of the
    last proof step, shifting an equivalence relation around a bi-implication,
    is a very useful fact of any symmetric transitive relation $R$,
    namely that $R xrel(R rel.arr R rel.arr (<->)) R.$
  ]
]

#theorem[NF Correctness][
  For all $Gamma cl jwa.nctx$ and $c_1, c_2 cl jwa.cmd th Gamma$, if
  $nfinterpA(c_1) itree.weq nfinterpA(c_2)$, then for all $gamma cl Gamma
  asgn(jwa.val) (ctx.nilc ctx.conc jwa.neg jwa.base)$, $ c_1[gamma] arrow.b.double jwa.pyes <-> c_2[gamma] arrow.b.double jwa.pyes. $
] <thm-jwa-nf-correctness>
#proof[
  By @thm-nf-correctness applied to $jwa.jwa$, with hypotheses proven in @lem-jwa-sub, @thm-jwa-respsub and @thm-jwa-finred,
  obtain $ base.fst itree.fmap jwa.eval th c_1[gamma] quad itree.weq quad base.fst itree.fmap jwa.eval th c_2[gamma]. $
  Conclude by the fact that $itree.weq$ is an equivalence relation.
]

Note that we obtain correctness only for commands in negative contexts. This is
easily delt with, by defining an extended equivalence relation on such
commands, which first quantifies over an ultimate pattern for each type in
$Gamma cl ctx.ctxc th jwa.typ$ and asserts OGS equivalence of the configurations
substituted by the given sequence of patterns. First, let us sketch the pointwise lifting
from types to scopes of several constructs related to patterns.

#definition[Pointwise Pattern Lifting][
  Define the lifting of $jwa.pat$ and $jwa.dom$ to scopes as follows.

  $ jwa.patX cl ctx.ctxc th jwa.typ -> base.Type \
    jwa.patX th Gamma := {A cl jwa.typ} -> Gamma ctx.var A -> jwa.pat A $

  $ jwa.domX th (Gamma cl ctx.ctxc th jwa.typ) cl jwa.patX th Gamma -> jwa.nctx $
  #v(-0.8em)
  $ & jwa.domX th ctx.nilc         && th gamma := ctx.nilc \
    & jwa.domX th (Gamma ctx.conc A) && th gamma := jwa.domX th Gamma th (gamma compose ctx.popc) ctx.catc jwa.dom th (gamma th ctx.topc) $

  Further define an embedding of pattern assignments into ordinary assignments as follows.

  $ jwa.embX th {Gamma} th (gamma cl jwa.patX th Gamma) cl Gamma asgn(jwa.val) jwa.domX th gamma \
    jwa.embX th gamma th i := (jwa.p2v th (gamma th i))[de("aux") th gamma th i] $

  We only give the type of the required family of renamings $de("aux")$ as it is purely
  administrative.

  $ de("aux") th {Gamma} th (gamma cl jwa.patX th Gamma) th {A} th (i cl Gamma ctx.varc A) cl jwa.dom th (gamma th i) ctx.ren jwa.domX th gamma $
]

Using these tools we can define our OGS equivalence relation, extended to general scopes.

#definition[Extended OGS Equivalence][
  For all $Gamma cl ctx.ctxc th jwa.typ$ and $c_1, c_2 cl jwa.cmd th Gamma$
  define the _extended JWA OGS equivalence_ as follows.

  $ c_1 de(approx_"ext") c_2 := (gamma cl jwa.patX th Gamma) -> ogsinterpA(c_1[jwa.embX th gamma]) itree.weq ogsinterpA(c_2[jwa.embX th gamma]) $
]

And finally we recover correctness.

#theorem[Extended OGS Correctness][
  For all $Gamma cl ctx.ctxc th jwa.typ$ and $c_1, c_2 cl jwa.cmd th Gamma$ if
  $c_1 de(approx_"ext") c_2$, then for all $gamma cl Gamma
  asgn(jwa.val) (ctx.nilc ctx.conc jwa.neg jwa.base)$, $ c_1[gamma] arrow.b.double jwa.pyes <-> c_2[gamma] arrow.b.double jwa.pyes. $
]
#proof[
  By pointwise lifting of $jwa.v2p$ and $jwa.v2a$ applyied $gamma$, compute $alpha
  cl jwa.patX th Gamma$ and $beta cl jwa.domX th alpha asgn(jwa.val)
  (ctx.nilc ctx.conc jwa.neg jwa.base)$. By $c_1 de(approx_"ext") c_2$, we have

  $ ogsinterpA(c_1[jwa.embX th alpha]) itree.weq ogsinterpA(c_2[jwa.embX th alpha]). $

  From @thm-jwa-correctness, deduce

  $ c_1[jwa.embX th alpha][beta] arrow.b.double jwa.pyes <-> c_2[jwa.embX th alpha][beta] arrow.b.double jwa.pyes. $

  Finally by pointwise lifting of @lem-jwa-refold obtain $(jwa.embX th
  alpha)[beta] approx gamma$, which concludes.
]

#remark[
  Of course the extended correctness results would hold just as well when
  considering normal form bisimulation instead of the OGS strategy
  equivalence, by following exactly the same pattern, replacing the OGS
  interpretation by the NF strategy interpretation.
]

This concludes the instanciation of our generic framework for JWA. Arguably,
although defining the actual data takes some getting used to, the proof mostly
amounts to busywork. The only meaningful lemma to be designed and proven is the
refolding lemma. 

== Polarized #short.uuc <sec-inst-mumu>

This next instance serves as a demonstration of the limits of what is captured
by our axiomatization of language machines. Technically, the structure will not
be much different than for JWA, simply scaled up. As such, we will give a bit
less details.

The #short.uuc was introduced by #nm[Curien] and #nm[Herbelin]~#mcite(<CurienH00>)
as a term assignment for the classical sequent calculus. Its core idea is to
scrupulously follow a discipline of duality. The configurations of its
evaluator can be understood as a formal cut, i.e., a pair $uutcfg(t,e)$ of a
term $t$ producing something of type $A$ and a _coterm_ (i.e., a context) $e$,
consuming something of type $A$. These producers and consumers are truly on an
equal footing and we consolidate both into a single judgment of _generalized
terms_ indexed by "side annotated types" with $uut.tv""A$ and $uut.tk""A$
respectively denoting the type of $A$-terms and $A$-coterms. Likewise, what
is usually called "variable" (term name) and "covariable" (context name) are
consolidated into a single construction, such that the typing scopes of all
judgments also consist of side annotated types.

$uut.mu$ and $uut.mut$ are the prime constructions respectively for terms and
coterms, giving their name to the calculus. The first can be understood as a
form of call-with-current-continuation, while the second is similar to a
let-binding. More precisely, the term $uut.mu alpha cs(.)c$ captures the current coterm it
is facing, binding it to the fresh covariable $alpha$ and continuing the
execution as the configuration $c$. On the other hand, the coterm $uut.mut x
cs(.)c$ captures the current term, binding it to the fresh variable $x$ and
continuing the execution as $c$. In this form, the calculus in non-confluent
as witnessed by the following critical pair

$ c_1[alpha |-> uut.mut x cs(.)c_2] quad <~ quad uutcfg(uut.mu alpha cs(.)c_1, uut.mut x cs(.)c_2) quad ~> quad c_2[x |-> uut.mu alpha cs(.)c_1], $

depending on which of $uut.mu$ or $uut.mut$ reduces first. A simple way
to overcome this non-determinism is to bias the calculus to either
call-by-value, prioritizing #uut.mu or call-by-name, prioritizing #uut.mut.
We adopt the other standard solution, arguably more general, which is to
parametrize configurations by a _polarity_, recording whether they are
currently in call-by-value mode (#uut.pp) call-by-name mode (#uut.pn). This
_polarized_ #short.uuc thus has the ability to express both execution
strategies. In effect, each type is assigned a polarity, and the polarity of a
configuration is determined by the type on which it is cutting. The type system
is entirely symmetric with respect to polarity, so that every type former has a
dual of opposite polarity. Do not confuse the #txsc[Cbv]-#txsc[Cbn] duality of
type polarities with the producer-consumer duality of terms and coterms as the
two are entirely orthogonal!

The concrete way by which the priority of the #uut.mu or #uut.mut rule is
managed is by restricting both of their reduction rules to only apply when the
other side of the configuration is a _value_. Now pay attention because the
different dualities mingle!

- A *value of positive type* is a new syntactic category included in terms,
  _weak-head normal terms_, consisting essentially of variables and of the
  _constructors_ of this type.
- A *covalue of positive type* is simply a coterm of that type.
// LOL
#scale(x: -100%, y: -100%)[
  - A *covalue of negative type* is a new syntactic category included in
    coterms, _forcing coterms_, consisting essentially of covariables and of the
    _destructors_ of this type.
  - A *value of negative type* is simply a term of that type.
]

We hope that all the symmetries are enjoyable. The consequence is that at a
positive type, the #uut.mu reduction rule will fire across any coterm, while the #uut.mut
rule will only fire across a weak-head normal term, and symetrically at
negative types. For a more general introduction to #short.uuc, we can recommend
the tutorial by #nm[Binder] _et. al_~#mcite(<BinderTMO24>). Technically, our
polarized presentation approximately follows the one from #nm[Downen]
and #nm[Ariola]~#mcite(dy: 1.8em, <DownenA20>), obtaining a middle ground
between their #nm[System L] and #nm[System D]. Without further ado, let us jump
to the formal definition of types and syntax.

#definition[Types][
  There are two kinds, or polarities, given as follows.
  $ kw.dat uut.pol cl base.Type := uut.pp | uut.pn $

  The syntax of _open types_ is given by the inductive family
  $ kw.dat uut.xtyp th (Theta cl ctx.ctxc th uut.pol) cl uut.pol -> base.Type $
  whose constructors are given below.

  #mathpar(block: true, spacing: -0.4em,
    inferrule("", $uut.tzer cl uut.xtyp th Theta th uut.pp$),
    inferrule("", $uut.ttop cl uut.xtyp th Theta th uut.pn$),
    inferrule("", $uut.tbot cl uut.xtyp th Theta th uut.pp$),
    inferrule("", $uut.tone cl uut.xtyp th Theta th uut.pn$),
    inferrule(
      ($A cl uut.xtyp th Theta th uut.pp$, $B cl uut.xtyp th Theta th uut.pp$),
      $A uut.tten B cl uut.xtyp th Theta th uut.pp$
    ),
    inferrule(
      ($A cl uut.xtyp th Theta th uut.pn$, $B cl uut.xtyp th Theta th uut.pn$),
      $A uut.tpar B cl uut.xtyp th Theta th uut.pn$
    ),
    inferrule(
      ($A cl uut.xtyp th Theta th uut.pp$, $B cl uut.xtyp th Theta th uut.pp$),
      $A uut.tplu B cl uut.xtyp th Theta th uut.pp$
    ),
    inferrule(
      ($A cl uut.xtyp th Theta th uut.pn$, $B cl uut.xtyp th Theta th uut.pn$),
      $A uut.tand B cl uut.xtyp th Theta th uut.pn$
    ),
    inferrule($A cl uut.xtyp th Theta th uut.pn$, $uut.tdw A cl uut.xtyp th Theta th uut.pp$),
    inferrule($A cl uut.xtyp th Theta th uut.pp$, $uut.tup A cl uut.xtyp th Theta th uut.pn$),
    inferrule($A cl uut.xtyp th Theta th uut.pn$, $uut.tmin A cl uut.xtyp th Theta th uut.pp$),
    inferrule($A cl uut.xtyp th Theta th uut.pp$, $uut.tneg A cl uut.xtyp th Theta th uut.pn$),
    inferrule($A cl uut.xtyp th (Theta ctx.conc uut.pp) th uut.pp$, $uut.tmu A cl uut.xtyp th Theta th uut.pp$),
    inferrule($A cl uut.xtyp th (Theta ctx.conc uut.pn) th uut.pn$, $uut.tnu A cl uut.xtyp th Theta th uut.pn$),
    inferrule($i cl Theta ctx.varc p$, $uut.tvar th i cl uut.xtyp th Theta th p$),
  )

  Define (closed) _types_ by the shorthand $uut.typ := uut.xtyp th ctx.nilc$.
]

#lemma[Type Substitution][
  Open types #uut.xtyp form a substitution monoid. We will write $A uut.tsub B$ for the topmost
  variable substitution $A[sub.var,B]$.
]

The types of our language thus comprise the usual bunch of empty, singleton,
product and sum types, each in their positive ($uut.tzer$, $uut.tone$,
$uut.tten$, $uut.tplu$) and negative ($uut.tbot$, $uut.ttop$, $uut.tand$,
$uut.tpar$) variants. We then have the two shifts, $uut.tdw$ for _thunks_ of
a negative type and $uut.tup$ for _returners_ of a positive type, and two
negations ($uut.tmin$, $uut.tneg$), basically swapping terms and coterms.
Finally, we do not consider existential and universal quantification, but
replace them by two fixed point types, $uut.tmu$ for inductive-like types and
$uut.tnu$ for coinductive-like types. Their presence is mainly motivated by
allowing us write a combinator *Y* for general recursion and thus
obtaining a #nm[Turing]-complete language.

#remark[
  The above type variables and type substitution might raise some questions. In
  the context of a formal development, it is well-known that formalizing
  polymorphic calculi is quite involved, in particular in this
  well-typed-and-scoped style~#mcite(<ChapmanKNW19>). Moreover, our generic
  OGS construction only supports simple types. Here though, we only need to
  mention open types in passing, to express recursive types. The rest of the
  formalization will be solely concerned with closed types. Indeed, recursive
  types, in contrast to existential and universal types, do maintain a
  constant type-variable scope throughout the term syntax. In particular,
  proving OGS correctness will _not_ require _any_ law on substitution or
  renaming of types.
]

#definition[Side-Annotated Types][
  Define _side-annotated types_ $kw.dat th uut.styp cl base.Type$ by the
  following constructors.

  #mathpar(block: true,
    inferrule($A cl uut.typ p$, $uut.tv""A cl uut.styp$),
    inferrule($A cl uut.typ p$, $uut.tk""A cl uut.styp$),
  )

  Note that we will use $uut.tv$ and $uut.tk$ with very weak parsing precedence,
  allowing us to write, e.g., $uut.tv""A uut.tpar B$.

  Define side-annotated type dualization $A^uut.sneg$ as follows.

  $ (uut.tv""A)^uut.sneg := uut.tk""A \
    (uut.tk""A)^uut.sneg := uut.tv""A $
]

//#show figure.where(kind: "full-page"): context {
//  set block(width: page.width + 4.4cm)
//}

#figure(placement: top, caption: [#short.uuc Syntax],
  full-page(box(stroke: 0.5pt, outset: 4pt, radius: 2pt)[
  #mathpar(block: true, spacing: 1fr,
    inferrule(
      ($A cl uut.typ th p$, $t cl Gamma uut.jt uut.tv""A$, $e cl Gamma uut.jt uut.tk""A$),
      $uutcfgp(p, t, e) cl Gamma uut.jc$,
    ),
    inferrule(
      $c cl Gamma ctx.conc uut.tk""A uut.jc$,
      $uut.mu c cl Gamma uut.jt uut.tv""A$
    ),
    inferrule(
      $c cl Gamma ctx.conc uut.tv""A uut.jc$,
      $uut.mut c cl Gamma uut.jt uut.tk""A$
    ),
    inferrule(
      $v cl Gamma uut.jw cal(A)$,
      $uut.vw v cl Gamma uut.jt cal(A)$,
    ),
    inferrule(
      $i cl Gamma ctx.var cal(A)$,
      $uut.vvar i cl Gamma uut.jw cal(A)$,
    ),
    inferrule(
      $$,
      $uutpm(uut.tzer) cl Gamma uut.jw uut.tk""uut.tzer$,
    ),
    inferrule(
      $$,
      $uutabs(uut.ttop) cl Gamma uut.jw uut.tv""uut.ttop$,
    ),
    inferrule(
      $$,
      $uut.vtt cl Gamma uut.jw uut.tv""uut.tone$,
    ),
    inferrule(
      $c cl Gamma uut.jc$,
      $uutpm(uut.tone, c) cl Gamma uut.jw uut.tk""uut.tone$,
    ),
    inferrule(
      $c cl Gamma uut.jc$,
      $uutabs(uut.tbot, c) cl Gamma uut.jw uut.tv""uut.tbot$,
    ),
    inferrule(
      $$,
      $uut.vff cl Gamma uut.jw uut.tk""uut.tbot$,
    ),
    inferrule(
      ($w_1 cl Gamma uut.jw uut.tv""A$, $w_2 cl Gamma uut.jw uut.tv""B$),
      $uutvpair(w_1,w_2) cl Gamma uut.jw uut.tv""A uut.tten B$,
    ),
    inferrule(
      $c cl Gamma ctx.conc uut.tv""A ctx.conc uut.tv""B uut.jc$,
      $uutpm(uut.tten, c) cl Gamma uut.jw uut.tk""A uut.tten B$,
    ),
    inferrule(
      $c cl Gamma ctx.conc uut.tk""A ctx.conc uut.tk""B uut.jc$,
      $uutabs(uut.tpar, c) cl Gamma uut.jw uut.tv""A uut.tpar B$,
    ),
    inferrule(
      ($w_1 cl Gamma uut.jw uut.tk""A$, $w_2 cl Gamma uut.jw uut.tk""B$),
      $uutvcase(w_1, w_2) cl Gamma uut.jw uut.tk""A uut.tpar B$,
    ),
    inferrule(
      ($v cl Gamma uut.jw uut.tv""A$),
      $uut.vinl v cl Gamma uut.jw uut.tv""A uut.tplu B$,
    ),
    inferrule(
      ($v cl Gamma uut.jw uut.tv""B$),
      $uut.vinr v cl Gamma uut.jw uut.tv""A uut.tplu B$,
    ),
    inferrule(
      ($c_1 cl Gamma ctx.conc uut.tv""A uut.jc$, $c_2 cl Gamma ctx.conc uut.tv""B uut.jc$),
      $uutpm(uut.tplu, c_1, c_2) cl Gamma uut.jw uut.tk""A uut.tplu B$,
    ),
    inferrule(
      ($c_1 cl Gamma ctx.conc uut.tk""A uut.jc$, $c_2 cl Gamma ctx.conc uut.tk""B uut.jc$),
      $uutabs(uut.tand, c_1, c_2) cl Gamma uut.jw uut.tv""A uut.tand B$,
    ),
    inferrule(
      ($v cl Gamma uut.jw uut.tk""A$),
      $uut.vfst v cl Gamma uut.jw uut.tk""A uut.tand B$,
    ),
    inferrule(
      ($v cl Gamma uut.jw uut.tk""B$),
      $uut.vsnd v cl Gamma uut.jw uut.tk""A uut.tand B$,
    ),
    inferrule(
      $t cl Gamma uut.jt uut.tv""A$,
      $uut.vdw t cl Gamma uut.jw uut.tv""uut.tdw A$,
    ),
    inferrule(
      $c cl Gamma ctx.conc uut.tv""A uut.jc$,
      $uutpm(uut.tdw, c) cl Gamma uut.jw uut.tk""uut.tdw A$
    ),
    inferrule(
      $c cl Gamma ctx.conc uut.tk""A uut.jc$,
      $uutabs(uut.tup, c) cl Gamma uut.jw uut.tv""uut.tup A$
    ),
    inferrule(
      $t cl Gamma uut.jt uut.tk""A$,
      $uut.vup t cl Gamma uut.jw uut.tk""uut.tup A$,
    ),
    inferrule(
      $v cl Gamma uut.jw uut.tk""A$,
      $uut.vmin v cl Gamma uut.jw uut.tv""uut.tmin A$,
    ),
    inferrule(
      $c cl Gamma ctx.conc uut.tk""A uut.jc$,
      $uutpm(uut.tmin, c) cl Gamma uut.jw uut.tk""uut.tmin A$
    ),
    inferrule(
      $c cl Gamma ctx.conc uut.tv""A uut.jc$,
      $uutabs(uut.tneg, c) cl Gamma uut.jw uut.tv""uut.tneg A$
    ),
    inferrule(
      $v cl Gamma uut.jw uut.tv""A$,
      $uut.vneg v cl Gamma uut.jw uut.tk""uut.tneg A$,
    ),
    inferrule(
      $v cl Gamma uut.jw uut.tv""A uut.tsub uut.tmu A$,
      $uut.vmu v cl Gamma uut.jw uut.tv""uut.tmu A$,
    ),
    inferrule(
      $c cl Gamma ctx.conc uut.tv""A uut.tsub uut.tmu A uut.jc$,
      $uutpm(uut.tmu, c) cl Gamma uut.jw uut.tk""uut.tmu A$
    ),
    inferrule(
      $c cl Gamma ctx.conc uut.tk""A uut.tsub uut.tnu A uut.jc$,
      $uutabs(uut.tnu, c) cl Gamma uut.jw uut.tv""uut.tnu A$
    ),
    inferrule(
      $v cl Gamma uut.jw uut.tk""A uut.tsub uut.tnu A$,
      $uut.vnu v cl Gamma uut.jw uut.tk""uut.tnu A$,
    ),
    ""
  )
])) <fig-uut>

#definition[Syntax][
  The #short.uuc syntax is given by the following mutually defined inductive family of judgments,
  respectively for configurations, generalized terms and generalized weak-head normal forms.

  $ kw.dat th ar uut.jc cl uut.ctx -> base.Type \
    kw.dat th ar uut.jt ar cl uut.ctx -> uut.styp -> base.Type \
    kw.dat th ar uut.jw ar cl uut.ctx -> uut.styp -> base.Type $

  The constructors are given in @fig-uut

  Further define the following shorthands.

  $ uut.cmd := ar uut.jc \
    uut.tm := ar uut.jt ar \
    uut.wht := ar uut.jw ar $

  Define the family of generalized values as follows.

  $ uut.val cl uut.ctx -> uut.styp -> base.Type $
  #v(-0.8em)
  $ uut.val th Gamma th (uut.tv""A cl uut.typ th uut.pp) & := uut.wht th Gamma th uut.tv""A \
    uut.val th Gamma th (uut.tk""A cl uut.typ th uut.pp) & := uut.tm th Gamma th uut.tk""A \
    uut.val th Gamma th (uut.tv""A cl uut.typ th uut.pn) & := uut.tm th Gamma th uut.tv""A \
    uut.val th Gamma th (uut.tk""A cl uut.typ th uut.pn) & := uut.wht th Gamma th uut.tk""A $
]
]

#lemma[Substitution][
  #short.uuc values form a substitution monoid, and #short.uuc configurations form a substitution
  module over it. Moreover, $uut.val$ has decidable variables.
] <lem-uut-sub>
#proof[
  All by mutual induction on configurations, terms and weak head normal forms.
  This is not entirely easy, as the statements need to be proven in a
  particular order, but it is standard metatheory so we will not give further
  details.
]

=== Patterns

We will now define the infrastructure for patterns: first the _observable_
subset of side-annotated types, which will appear in the OGS game, then the
patterns, their embedding into values, and finally the splitting of values into
a pattern and a filling, together with the associated refolding lemmas. In JWA
we called the observable types "negative", but here this word is already quite
overloaded so we call them "private" instead. Recall that these are the types
that will appear in the OGS construction, as they denote syntactic objects
whose sharing between players is mediated by variables.

#definition[Private Types][
  Define private types as a subset of types given by the following predicate.

  #mathpar(block: true,
    block[
      $ uut.isneg cl uut.styp -> base.Prop $
      #v(-0.8em)
      $ uut.isneg th (uut.tv""A cl uut.typ th uut.pp) & := base.bot \
        uut.isneg th (uut.tk""A cl uut.typ th uut.pp) & := base.top \
        uut.isneg th (uut.tv""A cl uut.typ th uut.pn) & := base.top \
        uut.isneg th (uut.tk""A cl uut.typ th uut.pn) & := base.bot $
    ],
    block(height: 6em, align(horizon,
      $ uut.ntyp := base.int_uut.styp uut.isneg \
        uut.nctx := base.int_uut.ctx (ctx.all th uut.isneg) $)
    )
  )
]

With syntax, values and private (OGS) types defined we can properly start the
language machine instanciation. This starts by defining observations, and as for JWA,
we first go through the dual notion of _patterns_.

#definition[Patterns][
  Define the inductive family of ultimate patterns $kw.dat th uut.pat cl uut.styp -> base.Type$
  with the following constructors.

  #mathpar(block: true, spacing: 0em,
    inferrule(
      $A cl uut.typ th uut.pn$,
      $uutpbox(uut.pp, A) cl uut.pat th uut.tv""A$
    ),
    inferrule(
      $A cl uut.typ th uut.pp$,
      $uutpbox(uut.pn, A) cl uut.pat th uut.tk""A$
    ),
    inferrule(
      $$,
      $uut.ptt cl uut.pat th uut.tv""uut.tone$,
    ),
    inferrule(
      $$,
      $uut.pff cl uut.pat th uut.tk""uut.tbot$,
    ),
    inferrule(
      ($p_1 cl uut.pat th  uut.tv""A$, $p_2 cl uut.pat th uut.tv""B$),
      $uutppair(p_1,p_2) cl uut.pat th uut.tv""A uut.tten B$,
    ),
    inferrule(
      ($p_1 cl uut.pat th uut.tk""A$, $p_2 cl uut.pat th uut.tk""B$),
      $uutpcase(p_1, p_2) cl uut.pat th uut.tk""A uut.tpar B$,
    ),
    inferrule(
      ($p cl uut.pat th uut.tv""A$),
      $uut.pinl p cl uut.pat th uut.tv""A uut.tplu B$,
    ),
    inferrule(
      ($p cl uut.pat th uut.tv""B$),
      $uut.pinr p cl uut.pat th uut.tv""A uut.tplu B$,
    ),
    inferrule(
      ($p cl uut.pat th uut.tk""A$),
      $uut.pfst v cl uut.pat th uut.tk""A uut.tand B$,
    ),
    inferrule(
      ($p cl uut.pat th uut.tk""B$),
      $uut.psnd v cl uut.pat th uut.tk""A uut.tand B$,
    ),
    inferrule(
      $p cl uut.pat th uut.tv""A$,
      $uut.pdw p cl uut.pat th uut.tv""uut.tdw A$,
    ),
    inferrule(
      $p cl uut.pat th uut.tk""A$,
      $uut.pup p cl uut.pat th uut.tk""uut.tup A$,
    ),
    inferrule(
      $p cl uut.pat th uut.tk""A$,
      $uut.pmin p cl uut.pat th uut.tv""uut.tmin A$,
    ),
    inferrule(
      $p cl uut.pat th uut.tv""A$,
      $uut.pneg p cl uut.pat th uut.tk""uut.tneg A$,
    ),
    inferrule(
      $p cl uut.pat th uut.tv""A uut.tsub uut.tmu A$,
      $uut.pmu p cl uut.pat th uut.tv""uut.tmu A$,
    ),
    inferrule(
      $p cl uut.pat th uut.tk""A uut.tsub uut.tnu A$,
      $uut.pnu p cl uut.pat th uut.tk""uut.tnu A$,
    ),
  )

  Define their _domain_ by the function $uut.dom cl uut.pat th A -> uut.nctx$
  as follows.

  #mathpar(block: true, spacing: 1fr,
  $ & uut.dom th uutpbox(uut.pp, A) && := ctx.nilc ctx.conc uut.tv""A \
    & uut.dom th uutpbox(uut.pn, A) && := ctx.nilc ctx.conc uut.tk""A \
    & uut.dom th uut.ptt && := ctx.nilc \
    & uut.dom th uut.pff && := ctx.nilc \
    & uut.dom th uutppair(p_1, p_2) && := uut.dom th p_1 ctx.catc uut.dom th p_2 \
    & uut.dom th uutpcase(p_1, p_2) && := uut.dom th p_1 ctx.catc uut.dom th p_2 \
    & uut.dom th (uut.pinl p) && := uut.dom th p \
    & uut.dom th (uut.pinr p) && := uut.dom th p $,
  $ & uut.dom th (uut.pfst p) && := uut.dom th p \
    & uut.dom th (uut.psnd p) && := uut.dom th p \
    & uut.dom th uut.pdw p && := uut.dom th p \
    & uut.dom th uut.pup p && := uut.dom th p \
    & uut.dom th (uut.pmin p) && := uut.dom th p \
    & uut.dom th (uut.pneg p) && := uut.dom th p \
    & uut.dom th (uut.pmu p) && := uut.dom th p \
    & uut.dom th (uut.pnu p) && := uut.dom th p \
  $)
]

With patterns defined, we will define the embedding and splitting in one go, without giving
the entire definitions as they are becoming quite unwieldy.

#lemma[Value Splitting][
  Define the following functions

  $ uut.p2v th {A} th (p cl uut.pat th A) cl uut.val th (uut.dom th p) th A \
    uut.v2p th {Gamma cl uut.nctx} th {A} cl uut.val th Gamma th A -> uut.pat A \
    uut.v2a th {Gamma cl uut.nctx} th {A} th (v cl uut.val th Gamma th A) cl uut.dom th (uut.v2p th v) asgn(uut.val) Gamma, $

  characterized by the following two properties.

  1. For all $Gamma cl uut.nctx$, $A cl uut.typ$ and $v cl uut.val th Gamma th A$,
    $ (uut.p2v th (uut.v2p th v))[uut.v2a th v] = v. $
  2. For all $Gamma cl uut.nctx$, $A cl uut.typ$, $p cl uut.pat th A$ and $gamma cl uut.dom th p asgn(uut.val) Gamma$,
    $ (p, gamma) approx (uut.v2p th (uut.p2v th p)[gamma], uut.v2a th (uut.p2v th p)[gamma]). $
] <lem-uut-refold>
#proof[
  $uut.p2v$ is defined by direct induction on patterns. $uut.v2p$ is defined through the following two
  mutually inductive auxiliary functions.

  $ uut.v2p^uut.pp th {Gamma cl uut.nctx} th {A cl uut.typ th uut.pp} cl uut.wht th Gamma th uut.tv""A -> uut.pat uut.tv""A \
    uut.v2p^uut.pn th {Gamma cl uut.nctx} th {A cl uut.typ th uut.pn} cl uut.wht th Gamma th uut.tk""A -> uut.pat uut.tk""A $

  Similarly, $uut.v2a$ is defined through the following two mutually inductive auxiliary functions.

  $ uut.v2a^uut.pp th {Gamma cl uut.nctx} th {A cl uut.typ th uut.pp} th (v cl uut.wht th Gamma th uut.tv""A) \
    quad cl uut.dom th (uut.v2p^uut.pp th v) asgn(uut.val) Gamma \
    uut.v2a^uut.pn th {Gamma cl uut.nctx} th {A cl uut.typ th uut.pn} th (v cl uut.wht th Gamma th uut.tk""A) \
    quad cl uut.dom th (uut.v2p^uut.pn th v) asgn(uut.val) Gamma $

  The first property (refolding) is then obtained by similar decomposition into
  two auxiliary properties concerned with positive weak head normal terms and
  negative weak head normal coterms. The second property (unicity of
  splitting) is proven by direct induction on patterns.
]

We can finally give the #short.uuc _observations_, as patterns at the dual side-annotated type.

#definition[Observation][
  Define _observations_ as the following binding family.

  $ uut.obs cl ctx.bfam th uut.nctx th uut.ntyp \
    uut.obs := pat(
      ctx.Oper th A & := uut.pat th A^uut.sneg,
      ctx.dom th p & := uut.dom th p
    ) $
]

=== #short.uuc Language Machine

We now define the rest of the #short.uuc language machine, namely the evaluation
and application maps.

#definition[Evaluation][
  Define evaluation by iteration of an evaluation step as follows.

  #let agl = cs(sym.angle.l + th)
  #let agr = cs(th + sym.angle.r)
  #let xpp = $cs(cbin(cnorm(|)cnorm(uut.pp)cnorm(|)))$
  #let xpn = $cs(cbin(cnorm(|)cnorm(uut.pn)cnorm(|)))$

  $ uut.eval th {Gamma cl uut.nctx} cl uut.cmd th Gamma -> delay.t th (ctx.norm^(""uut.obs)_uut.val th Gamma) \
    uut.eval := itree.iter th (itree.ret compose uut.evalstep) $

  $ uut.evalstep th {Gamma cl uut.nctx} cl uut.cmd th Gamma -> ctx.norm^(""uut.obs)_jwa.val th Gamma base.sum uut.cmd th Gamma $
  #v(-0.8em)
  $ & uut.evalstep th & agl uut.mu c & xpp e         agr && := base.inj2 th c[sub.var,e] \
    & uut.evalstep th & agl t        & xpn uut.mut c agr && := base.inj2 th c[sub.var,t] \
    & uut.evalstep th & agl uut.vw v & xpp uut.mut c agr && := base.inj2 th c[sub.var,v] \
    & uut.evalstep th & agl uut.mu c & xpn uut.vw k  agr && := base.inj2 th c[sub.var,k] \
    & uut.evalstep th & agl uut.vw v & xpp uut.vw th (uut.vvar i) agr && := base.inj1 th ((i ctx.cute uut.v2p th v), uut.v2a th v) \
    & uut.evalstep th & agl uut.vw th (uut.vvar i) & xpn uut.vw k  agr && := base.inj1 th ((i ctx.cute uut.v2p th k), uut.v2a th k) \
    & uut.evalstep th & agl uut.vw th (uut.vvar i) & xpp uut.vw k  agr && := base.exfalso th (ctx.eltupg th i) \
    & uut.evalstep th & agl uut.vw v & xpn uut.vw th (uut.vvar i) agr && := base.exfalso th (ctx.eltupg th i) \
    & uut.evalstep th & agl uut.vw th uut.vtt & xpp uut.vw th uutpm(uut.tone, c) agr && := base.inj2 th c \
    & uut.evalstep th & agl uut.vw th uutabs(uut.tbot, c) & xpn uut.vw th uut.vff agr && := base.inj2 th c \
    & uut.evalstep th & agl uut.vw th uutvpair(v_1, v_2) & xpp uut.vw th uutpm(uut.tten, c) agr && := base.inj2 th c[sub.var,v_1,v_2] \
    & uut.evalstep th & agl uut.vw th uutabs(uut.tpar, c) & xpn uut.vw th uutvcase(k_1,k_2) agr && := base.inj2 th c[sub.var,k_1,k_2] \
    & uut.evalstep th & agl uut.vw th (uut.vinl th v) & xpp uut.vw th uutpm(uut.tplu, c_1, c_2) agr && := base.inj2 th c_1[sub.var,v] \
    & uut.evalstep th & agl uut.vw th (uut.vinr th v) & xpp uut.vw th uutpm(uut.tplu, c_1, c_2) agr && := base.inj2 th c_2[sub.var,v] \
    & uut.evalstep th & agl uut.vw th uutabs(uut.tand, c_1, c_2) & xpn uut.vw th (uut.vfst th k) agr && := base.inj2 th c_1[sub.var,k] \
    & uut.evalstep th & agl uut.vw th uutabs(uut.tand, c_1, c_2) & xpn uut.vw th (uut.vfst th k) agr && := base.inj2 th c_2[sub.var,k] \
    & uut.evalstep th & agl uut.vw th uut.vdw t & xpp uut.vw th uutpm(uut.tdw, c) agr && := base.inj2 th c[sub.var,t] \
    & uut.evalstep th & agl uut.vw th uutabs(uut.tup, c) & xpn uut.vw th uut.vdw e agr && := base.inj2 th c[sub.var,e] \
    & uut.evalstep th & agl uut.vw th uut.vmin v & xpp uut.vw th uutpm(uut.tmin, c) agr && := base.inj2 th c[sub.var,v] \
    & uut.evalstep th & agl uut.vw th uutabs(uut.tneg, c) & xpn uut.vw th uut.vneg k agr && := base.inj2 th c[sub.var,k] \
    & uut.evalstep th & agl uut.vw th (uut.vmu th v) & xpp uut.vw th uutpm(uut.tmu, c) agr && := base.inj2 th c[sub.var,v] \
    & uut.evalstep th & agl uut.vw th uutabs(uut.tnu, c) & xpn uut.vw th (uut.vnu th k) agr && := base.inj2 th c[sub.var,k]
  $
]

#definition[Observation Application][
  Define observation application as follows.

  $ uut.apply th {Gamma cl uut.nctx} th {A cl uut.ntyp} th (v cl uut.val th Gamma th A) th (o cl uut.obs"".ctx.Oper th A) \
    quad cl uut.obs"".ctx.dom th o asgn(uut.val) Gamma -> uut.cmd th Gamma \
    uut.apply th {Gamma} th {uut.tv""A} th v th o th gamma := uutcfgp(uut.pn, v, (uut.p2v th o)[gamma]) \
    uut.apply th {Gamma} th {uut.tk""A} th v th o th gamma := uutcfgp(uut.pp, (uut.p2v th o)[gamma], v) \ $
]

We can now define the language machine.

#definition[Language Machine][
  The #short.uuc language machine is given by the following record.

  $ uut.uut cl ogs.machine th uut.obs th uut.val th uut.cmd \
    uut.uut := pat(
      ogs.eval   & := uut.eval,
      ogs.apply  & := uut.apply,
      ogs.appext & := ...
    ) $
]

Let us now sketch the proof of the correctness hypotheses.

#lemma[#mumutl Respects Substitution][
  The #short.uuc language machine respects substitution.
] <lem-uut-resp-sub>
#proof[
  - $ogs.evalsub$ #sym.space.quad Given $Gamma, Delta cl uut.nctx$, $c cl uut.cmd th Gamma$ and $sigma cl Gamma asgn(uut.val) Delta$,
    we need to prove the following.

    $ uut.eval th c[sigma] itree.eq uut.eval th c itree.bind kw.fun th n |-> uut.eval th (ogs.emb th n)[sigma] $

    Proceed by coinduction, then pattern-match on $c$, following the splitting pattern of $uut.evalstep$. In
    case of a redex, i.e., when $uut.evalstep$ returns $base.inj2 th c'[gamma]$ for some $c'$ and $gamma$, commute $gamma$ and $sigma$
    in the LHS and conclude by coinduction hypothesis. In case of a normal form, i.e., when $uut.evalstep$ returns
    $base.inj1 th ((i ctx.cute uut.v2p th v), uut.v2a th v)$ for some $i$ and $v$, apply @lem-uut-refold(1) to
    rewrite $(ogs.emb th ((i ctx.cute uut.v2p th v), uut.v2a th v))[sigma]$ into
    either $uutcfgp(uut.pn, v[sigma], sigma th i)$ or $uutcfgp(uut.pp, sigma th i, v[sigma])$, depending on
    the polarity of the type, and conclude by reflexivity.
  - $ogs.appsub$ #sym.space.quad By direct application of substitution fusion.
  - $ogs.evalnf$ #sym.space.quad By direct application of @lem-uut-refold(2).
  #v(-1.8em)
]

#lemma[#mumutl Finite Redexes][
  The #short.uuc language machine has finite redexes
] <lem-uut-finred>
#proof[
  As for JWA, the #short.uuc verifies a stronger property than well-foundedness of
  $ogs.badinst$, namely that there for any observation $o_2$, there is no
  $o_1$ such that $o_1 ogs.badinst o_2$. In other words, applying an observation to a
  non-variable value necessarily yields a redex. This is proven by direct case-analysis
  of the value and the observation.
]

We can now conclude correctness of the OGS interpretation w.r.t. substitution equivalence.

#definition[Evaluation Relation][
  For $c cl uut.cmd th (ctx.nilc ctx.conc uut.tk""uut.tone)$, define the following
  big step _evaluation relation_.

  $ c arrow.b.double uut.ptt := (base.fst itree.fmap uut.eval th c) itree.weq itree.ret th (ctx.topc ctx.cute uut.ptt) $
]

#theorem[OGS Correctness][
  For all $Gamma cl uut.nctx$ and $c_1, c_2 cl uut.cmd th Gamma$, if
  $ogsinterpA(c_1) itree.weq ogsinterpA(c_2)$, then for all $gamma cl Gamma
  asgn(uut.val) (ctx.nilc ctx.conc uut.tk""uut.tone)$,
  $ c_1[gamma] arrow.b.double uut.ptt quad <-> quad c_2[gamma] arrow.b.double uut.ptt. $
] <thm-uut-correctness>
#proof[
  By @thm-correctness applied to $uut.uut$, with hypotheses proven in @lem-uut-sub, @lem-uut-resp-sub and @lem-uut-finred,
  obtain $ base.fst itree.fmap uut.eval th c_1[gamma] quad itree.weq quad base.fst itree.fmap uut.eval th c_2[gamma]. $
  Conclude by the fact that $itree.weq$ is an equivalence relation.
]

We will stop here and skip the NF bisimulation correctness as well as the
extended results for configurations in arbitrary (non-private) contexts $Gamma
cl uut.ctx$. If needed, these can be obtained exactly as for JWA, by patching
the OGS or NF interpretation equivalence to first quantify over patterns for
each type in $Gamma$.

== Natural Deduction Style Calculi <sec-inst-nd>

Our first two examples were centered around the concept of first-class
continuation and of an abstract machine. As such, they were quite easy to fit
into the generic framework of language machines. However, it is common for
functional languages _not_ to fit into this shape. The prime example is the
#short.llc, whose evaluator does not operate on "configurations" (a notion
which is not standard for this language), but rather on terms. Moreover, it
does not naturally have an unified notion of observation, but rather two kinds
of shapes for normal forms: calls (stuck eliminations) and returns
(values).

In concrete cases, probably the easiest way to obtain a language machine is to
use a minimal amount of cheating: instead of building a language machine for
the standard evaluator of the language at hand, we can switch to an abstract
machine presentation of the semantics. Although it is not self-evident how to
design a language machine for the #short.llc, it is relatively easy to build
one out of, say, the #nm[Krivine] machine~#mcite(<Curien91>), or the #txsc[Cek]
machine~#mcite(dy: 3em, <FelleisenF87>), following the blueprint of JWA. But
sometimes moving the goalpost is not acceptable and we would prefer to stay
with the standard evaluator. In that case, we can instead perform a lightweight
continuation passing style (#txsc[Cps]) translation, much like we sketched in the
introduction (@sec-intro-cps).

Instead of presenting this technique with a couple concrete examples, we
describe it _generically_. To do so, we replace the notion of language machine
with an axiomatization better fitting languages in the natural deduction style
of the #short.llc, which we call a _language with evaluator_. We then show how
to derive a language machine from any such language with evaluator, by way of a
formal #txsc[Cps] translation, and finally we give an example language: untyped
call-by-value #short.llc.

=== A Language With Evaluator

A language with evaluator has two main differences with a machine language.
First, we will replace the binding family of observations with two similar
structures, _eliminators_ and _patterns_, respectively representing the shape
of calls and the shape of returns. Second, we drop the family of configurations
and replace it with two new families: the terms and the evaluation contexts.

*Patterns and Eliminators* #sym.space.quad
Patterns are easily dealt with, as they can simply be specified by a binding family.
Indeed, patterns should be indexed by a type, the type of the pattern at hand, and
each pattern should have a domain, a scope listing its distinct and fresh
variables, or holes. Likewise, eliminators are typed and have a domain, listing
their arguments. But their description should also contain the _target_ of each
eliminator, designating the type of the return they are expecting. We formalize
this as a family of _bindings with target_.

#definition[Bindings With Target][
  Given $S,T cl base.Type$, a family of _bindings with targets_ is given by
  records of the following type.

  $ kw.rec th ctx.btfam th S th T kw.whr \
    pat(
      ctx.Oper cl T -> base.Type,
      ctx.dom th {alpha} cl ctx.Oper th alpha -> S,
      ctx.tgt th {alpha} cl ctx.Oper th alpha -> T
    ) $
]

*Syntactic Structure* #sym.space.quad
Terms and evaluation contexts are simpler: they are indexed sets.
Assuming a set of scopes $S$ and types $T$, terms can be represented as
a family $base.Type^(S,T)$, indexed by a scope and a type, just like values.
Evaluation contexts can be represented by a family $base.Type^(S,T,T)$,
indexed by a scope, an inner type and an outer type. Without surprise,
we will require that values form a substitution monoid and that terms and
evaluation contexts form substitution modules over values. There is however one
more syntactic operation on contexts: putting something in their hole. More
precisely, we can replace the hole by a context, yielding the _composition_ of
the two contexts, or we can alternatively replace the hole by a term, yielding
a new term. This is again a monoid-and-module situation, but of a different
kind. Our goal is thus to define _filling monoids_ and _filling modules_ and
axiomatize that evaluation contexts form a filling monoid and that terms form
a filling module over them. Note that there will be additional compatibility
conditions between the substitution structures and the filling structures.

#definition[Filling Monoid][
  Given $S,T cl base.Type$ and a family $X cl base.Type^(S,T,T)$, a _filling monoid_
  structure on $X$ is given by instances of the following typeclass.

  $ kw.cls fil.mon th X kw.whr \
    pat(
      fil.hole th {Gamma th alpha} cl X th Gamma th alpha th alpha,
      fil.fill th {Gamma th alpha th beta th iota} cl X th Gamma th beta th iota -> X th Gamma th alpha th beta -> X th Gamma th alpha th iota,
      fil.fillext cl fil.fill xrel(cnorm(approx) rel.carr cnorm(approx) rel.carr cnorm(approx)) fil.fill,
      fil.idl th {Gamma th alpha th beta} th (x cl X th Gamma th alpha th beta) cl fil.fill th fil.hole th x approx x,
      fil.idr th {Gamma th alpha th beta} th (x cl X th Gamma th alpha th beta) cl fil.fill th x th fil.hole approx x,
      fil.assoc th {Gamma th alpha th beta th iota th tau} th (x cl X th Gamma th iota th tau) th (y cl X th Gamma th beta th iota) (z cl X th Gamma th alpha th beta) \
        quad cl fil.fill th (fil.fill th x th y) th z approx fil.fill th x th (fil.fill th y th z),
    ) $
]

#remark[
  We have represented filling monoids by families $X cl
  base.Type^(S,T,T)$, where $x cl X th Gamma th alpha th beta$ should be
  thought of as an evaluation context in scope $Gamma$, with interior type
  (or hole type) $alpha$ and exterior type $beta$. Note that there is only one
  scope, and that the scope of what $x$ can be filled with is the same as what
  we will obtain as output. In other words, the above axiomatization only
  applies to notions of evaluations contexts which _do not_ capture variables.
  We could certainly complexify our above notions to encompass such capturing
  contexts, by tracking both the inner scope and the outer scope in the
  indexes, i.e., by using families $base.Type^(S,T,S,T)$. However, OGS models
  and NF bisimulations are most useful with _weak_ reductions, which indeed do not
  reduce under binders. As such, we opt for simplicity, at the cost of some
  generality.
]

#definition[Filling Module][
  Given $S,T cl base.Type$, a family $X cl base.Type^(S,T,T)$, a filling monoid
  $fil.mon th X$ and a family $Y cl base.Type^(S,T)$, a _filling module_ structure
  over $X$ on $Y$ is given by instances of the following typeclass.

  $ kw.cls fil.mod_X th Y kw.whr \
    pat(
      fil.act th {Gamma th alpha th beta} cl X th Gamma th alpha th beta -> Y th Gamma th alpha -> X th Gamma th beta,
      fil.actext cl fil.act xrel(cnorm(approx) rel.carr cnorm(approx) rel.carr cnorm(approx)) fil.act,
      fil.actid th {Gamma th alpha} th (t cl Y th Gamma th alpha) cl fil.act th fil.hole th t approx t,
      fil.actcomp th {Gamma th alpha th beta th iota} th (x cl X th Gamma th beta th iota) th (y cl X th Gamma th alpha th beta) th (t cl Y th Gamma th iota) \
        quad cl fil.act th (fil.fill x th y) th t approx fil.act th x th (fil.act th y th t),
    ) $
]

In the following we will write $fil.fill th E th F$ and $fil.act th E th t$
respectively as $E[F]$ and $E[t]$, as is standard practice. It is slightly
unfortunate that this collides with the notation for substitution, but we will
use the typing to disambiguate. We can now state the compatibility conditions
of filling structures w.r.t. substitution.

#definition[Filling Monoid With Substitution][
  Given $S,T cl base.Type$, a family $V cl base.Type^(S,T)$ with a substitution
  monoid structure $sub.mon th V$, and a family $X cl base.Type^(S,T,T)$, a
  _filling monoid structure with substitution_ on $X$ over $V$ is given by
  instances of the following typeclass.

  $ kw.cls th fil.smon_V th X kw.whr \
    pat(
      kw.ext sub.mod_V th X,
      kw.ext fil.mon th X,
      fil.fillsub th {Gamma th Delta th alpha th beta th iota} th (E cl X th Gamma th beta th iota) th (F cl X th Gamma th alpha th beta) th (gamma cl Gamma asgn(V) Delta) \
        quad cl E[F][gamma] approx E[gamma][F[gamma]],
      fil.holesub th {Gamma th Delta th alpha} th (gamma cl Gamma asgn(V) Delta) cl fil.hole_alpha [gamma] approx fil.hole_alpha
    ) $
]

#definition[Filling Module With Substitution][
  Given $S,T cl base.Type$, a family $V cl base.Type^(S,T)$ with a substitution
  monoid structure $sub.mon th V$, a family $X cl base.Type^(S,T,T)$ with
  a filling monoid structure with substitution $fil.smon_V th X$, and a family $Y cl base.Type^(S,T)$,
  a _filling module structure with substitution_ on $Y$ over $V$ and $X$ is
  given by instances of the following typeclass.

  $ kw.cls th fil.smod_(V,X) th Y kw.whr \
    pat(
      kw.ext sub.mod_V th Y,
      kw.ext fil.mod_X th Y,
      fil.actsub th {Gamma th Delta th alpha th beta} th (E cl X th Gamma th alpha th beta) th (t cl Y th Gamma th alpha) th (gamma cl Gamma asgn(V) Delta) \
        quad cl E[t][gamma] approx E[gamma][t[gamma]],
    ) $
]

*Evaluator* #sym.space.quad
The last piece of _stuff_ required to define a language with evaluator is the
family of normal forms. Recall that in a language machine, the evaluator
computes on configurations, and returns normal configurations, i.e., named observations
filled with values. Here, the our goal is to make the evaluator compute on
terms, so that we need to build a family $base.Type^(S,T)$ of normal forms based
upon the analogue of observations: patterns and eliminators. Following the intuitions
from the #short.llc, they can be of two forms.
- A decomposed value, that is, a pattern filled with values.
- A stuck elimination, that is, a variable, an elimination on it, arguments
  given by a sequence of values and an evaluation context whose hole matches the
  elimination target.

#definition[Normal Forms][
  Given a scope structure $ctx.scope_T th S$, patterns $P cl ctx.bfam th S th T$,
  eliminators $E cl ctx.btfam th S th T$, values $V cl base.Type^(S,T)$ and contexts
  $C cl base.Type^(S,T,T)$, the family of normal forms

  $ kw.dat th ctx.norm^(#h(0.1em)P,E)_(V,C) cl base.Type^(S,T) $

  is defined by the following constructors.

  #mathpar(block: true,
    inferrule(
      ($p cl P.ctx.Oper th alpha$, $gamma cl P.ctx.dom th p asgn(V) Gamma$),
      box(inset: 0.7em, $ctx.nret th p th gamma cl ctx.norm^(#h(0.1em)P,E)_(V,C) th Gamma th alpha$)
    ),
    inferrule(
      ($i cl Gamma ctx.var beta$,
      $e cl E.ctx.Oper th beta$,
      $gamma cl P.ctx.dom th p asgn(V) Gamma$,
      $k cl C th Gamma th (P.ctx.tgt th p) th alpha $),
      box(inset: 0.7em, $ctx.ncall th i th e th gamma th k cl ctx.norm^(#h(0.1em)P,E)_(V,C) th Gamma th alpha$)
    ),
  )
] <def-lang-nf>

We are now ready to give the definition of a language with evaluator. Note that the counterpart to
language machine's $ogs.apply$ is given by two maps, one for _resuming_ by giving a filled
pattern to an evaluation context, and one for _eliminating_ by applying an elimination with arguments
to a value.

#definition[Language With Evaluator][
  Given a scope structure $ctx.scope_T th S$, patterns $P cl ctx.bfam th S th T$,
  eliminators $E cl ctx.btfam th S th T$, values $V cl base.Type^(S,T)$, contexts
  $C cl base.Type^(S,T,T)$ and terms $T cl base.Type^(S,T)$, a _language with
  evaluator_ is given by records of the following type.

  $ kw.rec ogs.language_(P,E) th V th C th T kw.whr \
    pat(
      ogs.eval th {Gamma th alpha} cl T th Gamma th alpha -> delay.t th (ctx.norm^(#h(0.1em)P,E)_(V,C) th Gamma th alpha),
      ogs.resume th {Gamma th alpha th beta} th (k cl C th Gamma th alpha th beta) \
        quad (p cl P.ctx.Oper th alpha) th (gamma cl P.ctx.dom th p asgn(V) Gamma) cl T th Gamma th beta,
      ogs.elim th {Gamma th alpha} th (v cl V th Gamma th alpha) th (e cl E.ctx.Oper th p) \
        quad (gamma cl E.ctx.dom th p asgn(V) Gamma) cl T th Gamma th (E.ctx.tgt th p)
    ) $
]

We can now conclude with by stating the core hypothesis for OGS correctness, namely that
a language with evaluator respects substitution.

#definition[Language With Evaluator Respects Substitution][
  Assume a scope structure $ctx.scope_T th S$, patterns $P cl ctx.bfam th S th T$,
  eliminators $E cl ctx.btfam th S th T$, families $V$, $C$ and $T$ and a
  language with evaluator $L cl ogs.language_(P,E) th V th C th T$, such that
  moreover $sub.mon th V$, $fil.smon_V th C$ and $fil.smod_(V,C) th T$.
  Define the embedding of normal forms into terms $T$ as follows.

  $ ogs.emb cl ctx.norm^(#h(0.1em)P,E)_(V,C) th Gamma th alpha ctx.arr T $
  #v(-0.8em)
  $ & ogs.emb th (ctx.nret th p th gamma) && := L.ogs.resume th fil.hole th p th gamma \
    & ogs.emb th (ctx.ncall th i th e th gamma th k) && := k[L.ogs.elim th (sub.var th i) th e th gamma] $

  Then, the language $L$ _respects substitution_ if there is an instance of the following
  typeclass.

  $ kw.cls th ogs.sublang th L kw.whr \
    pat(
      ogs.evalsub th {Gamma th Delta th alpha} th (t cl T th Gamma th alpha) th (sigma cl Gamma asgn(V) Delta) \
        quad cl L.ogs.eval th t[sigma] itree.eq (L.ogs.eval th t itree.bind kw.fun th n |-> L.ogs.eval th (ogs.emb th n)[sigma]),
      ogs.resumesub th {Gamma th Delta th alpha th beta} th (k cl C th Gamma th alpha th beta) th p th gamma th (sigma cl Gamma asgn(V) Delta) \
        quad cl L.ogs.resume th k[sigma] th p th gamma[sigma] approx (L.ogs.resume k th p th gamma)[sigma],
      ogs.elimsub th {Gamma th Delta th alpha} th (v cl V th Gamma th alpha) th e th gamma th (sigma cl Gamma asgn(V) Delta) \
        quad cl L.ogs.elim th v[sigma] th e th gamma[sigma] approx (L.ogs.elim th v th e th gamma)[sigma],
      ogs.evalnf th {Gamma th alpha} th (n cl ctx.norm^(#h(0.1em)P,E)_(V,C) th Gamma th alpha) \
        quad cl L.ogs.eval th (ogs.emb th n) itree.eq itree.ret th n
    ) $
]

=== Untyped #short.llc

Before jumping to the translation from languages with evaluators to language
machines, let us showcase this new abstraction with an short example: untyped
call-by-value pure #short.llc.

Our first hurdle is the typing: our framework
requires typing, yet this calculus is untyped. The standard way out is a benign
change of nomenclature: an untyped system is entirely equivalent to an
un#[*i*]typed one, i.e., a system with a single type. It is however not _that_
simple. Setting $T := base.top$ and going on working with e.g., concrete scopes
$ctx.ctxc th base.top$, term judgments $de("tm") cl base.Type^(ctx.ctxc th
base.top, base.top)$ and #nm[De-Bruijn] indices is slightly unsatisfying. First
of all, $ctx.ctxc th base.top$ is isomorphic to the more idiomatic $base.nat$
and likewise, the corresponding #nm[De-Bruijn] indices $ar ctx.varc base.tt cl
base.Type^(ctx.ctxc th base.top)$ are isomorphic to $base.fin cl
base.Type^base.nat$, the finite sets. Apart from these esthetical
considerations, a more worrying technicality arises when your chosen type theory does
_not_ support #sym.eta equivalence on $base.top$. This principle
is quite important as it makes all inhabitants of $base.top$
definitionally equal, and, more importantly, all function $f cl base.top -> X$
definitionally constant. In the idealized type theory chosen for this thesis we
do assume this #sym.eta rule, but our concrete code artifact is stuck with a
theory which does not (Coq!). Once again, the flexibility of scope structures comes to
our rescue. Let us define a more idiomatic scope structure for untyped scopes.

#definition[Untyped Scopes][
  Define _finite sets_ $kw.dat th base.fin cl base.Type^base.nat$ with the following constructors.

  #mathpar(block: true,
    inferrule("", $base.ze cl base.fin th (base.su th n)$),
    inferrule($i cl base.fin th n$, $base.su th i cl base.fin th (base.su th n)$),
  )

  Further define the following helpers.

  $ base.fwkn th {m th n} cl base.fin th m -> base.fin th (m + n) $
  #v(-0.8em)
  $ & base.fwkn th base.ze && := base.ze \
    & base.fwkn th (base.su i) && := base.su th (base.fwkn th i) $

  $ base.fshft th {m th n} cl base.fin th n -> base.fin th (m + n) $
  #v(-0.8em)
  $ & base.fshft th {base.ze}   && th {n} th i && := i \
    & base.fshft th {base.su m} && th {n} th i && := base.su th (base.fshft th {m} th {n} th i) $

  Finally define _untyped scopes_ as the following instance of scope structure.

  $ ctx.untyped cl ctx.scope_base.top th base.nat \
    ctx.untyped := \
    pat(
      ctx.emp & := base.ze,
      m ctx.cat n & := n + m,
      n ctx.var x & := base.fin th n,
      ctx.rcatl & := base.fshft,
      ctx.rcatr & := base.fwkn,
      dots
    ) $
  #margin-note(dy: -11em)[
    Note that we swap $m$ and $n$ in the definition of $m ctx.cat n$. The
    reason for this is that scopes are traditionally taken to grow towards
    the right, while unary natural numbers grow towards the left, i.e.,
    addition is defined by recursion on the first argument. This is technically
    unnecessary but helps avoid unpleasant surprises during index juggling.
  ]
]

With these considerations out of the way, let us define the call-by-value #short.llc syntax and
semantics.

#definition[Syntax][
  #short.llc _terms_ are given by the data type $kw.dat th llc.term cl base.Type^base.nat$
  with the following constructors.

  #mathpar(block: true,
    inferrule($i cl base.fin th n$, $llc.var th i cl llc.term th n$),
    inferrule(
      $t cl llc.term th (base.su th n)$,
      $llc.lam th t cl llc.term th n$
    ),
    inferrule(
      ($t cl llc.term th n$, $u cl llc.term th n$),
      $t llc.app u cl llc.term th n$
    ),
  )

  #short.llc _values_ are given by the data type $kw.dat th llc.val cl base.Type^base.nat$
  with the following constructors.

  #mathpar(block: true,
    inferrule($i cl base.fin th n$, $llc.vvar th i cl llc.val th n$),
    inferrule(
      $t cl llc.term th (base.su th n)$,
      $llc.vlam th t cl llc.val th n$
    ),
  )

  Their embedding into terms is given by the following function.

  $ llc.v2t th {n} cl llc.val th n -> llc.term th n $
  #v(-0.8em)
  $ & llc.v2t th (llc.vvar th i) && := llc.var th i \
    & llc.v2t th (llc.vlam th t) && := llc.lam th t $

  #short.llc _evaluation contexts_ are given by the data type $kw.dat th llc.evc cl base.Type^base.nat$
  with the following constructors.

  #mathpar(block: true, spacing: 1fr,
    inferrule("", $llc.ehole cl llc.evc th n$),
    inferrule(
      ($t cl llc.term th n$, $k cl llc.evc th n$),
      $t llc.eappr k cl llc.evc th n$
    ),
    inferrule(
      ($k cl llc.evc th n$, $v cl llc.val th n$),
      $k llc.eappl v cl llc.evc th n$
    ),
  )

  Further define the following shorthands.

  #mathpar(block: true, spacing: 1fr,
    $llc.fterm cl base.Type^(base.nat,base.top) \
     llc.fterm th n th x := llc.term th n$,
    $llc.fval cl base.Type^(base.nat,base.top) \
     llc.fval th n th x := llc.val th n$,
    $llc.fevc cl base.Type^(base.nat,base.top,base.top) \
     llc.fevc th n th x th y := llc.evc th n$,
  )
]

#lemma[Substitution and Filling Structures][
  $llc.fval$ forms a substitution monoid, $llc.fevc$ forms a filling monoid
  with substitution over $llc.fval$, and $llc.fterm$ forms a filling module
  with substitution over $llc.fval$ and $llc.fevc$.
]
#proof[
  By standard construction.
]

Let us now define the evaluator. For once, we will design our own family for
normal forms, instead of defining patterns and eliminators and relying on the
generic $ctx.norm$ construction (@def-lang-nf), as it would be more of a hassle
to use. We will explain later how to translate from our own to the generic one.

#definition[Normal Forms][
  Define the family of normal forms $kw.dat th llc.norm cl base.Type^base.nat$ by
  the following constructors.

  #mathpar(block: true, spacing: 1fr,
    inferrule(
      $v cl llc.val th n$,
      $llc.nval th v cl llc.norm th n$
    ),
    inferrule(
      ($i cl base.fin th n$, $v cl llc.val th n$, $k cl llc.evc th n$),
      $llc.nstuck th i th v th k cl llc.norm th n$
    ),
  )
]

#definition[Evaluator][
  Define the #short.llc evaluator by the following coinductive function.

  $ llc.eval th {n} cl llc.term th n -> delay.t th (llc.norm th n) $
  #v(-0.8em)
  $ & llc.eval th (llc.var th i) && := itree.ret th (ctx.nret th (llc.vvar th i)) \
    & llc.eval th (llc.lam th t) && := itree.ret th (ctx.nret th (llc.vlam th t)) \
    & llc.eval th (t llc.app u)  && := $
  #v(-0.8em)
  $ pat(
      m <- itree.tau th (llc.eval th u) th ";",
      kw.case th m,
      pat(
        ctx.nret th v th := \
        pat(
          n <- itree.tau th (llc.eval th t) th ";",
          kw.case th n,
          pat(
            ctx.nret th (llc.vvar th i) & := itree.ret th (ctx.ncall th i th v th k) ,
            ctx.nret th (llc.vlam th a) & := itree.tau th (llc.eval th a[sub.var,v]),
            ctx.ncall th i th w th k    & := itree.ret th (ctx.ncall th i th w th (k llc.eappl v)) ,
          )
        ),
        ctx.ncall th i th v th k th := itree.ret th (ctx.ncall th i th v th (s llc.eappr k)),
      )
    ) $
]

#remark[
  There is some cheating in the above definition, as there is no chance that it will
  pass any syntactic guard checker for coinductive definition, as it full of
  monadic binds on recursive calls. Even when written "properly", that
  is, by copattern-matching on $itree.obs$ before case splitting on anything, Coq
  still does not understand it. However, we humans can observe that every recursive $llc.eval$
  call is hidden behind a $itree.tau$ step. And indeed, there is a systematic trick to
  obtain a definition _strongly bisimilar_ to the above, by adapting #nm[McBride]'s
  _General monad_ technique. We have not introduced the combinator for doing so
  in @ch-game, but it can be easily lifted from the original non-indexed
  interaction trees~#mcite(<XiaZHHMPZ20>) §4.2.
]

#remark[
  Perhaps you have noticed that we have gone for a right-to-left evaluation order (this
  was already decided at the time we wrote down the evaluation contexts). This
  choice might raise some eyebrows as it is not the standard practice, but could be
  dismissed as just a matter of taste, and indeed, why miss an oportunity to
  pay tribute to the #txsc[Zinc] not so abstract machine~#mcite(<Leroy90>)?
  However, this choice is not entirely innocent and mandates a small
  digression. Recall that our evaluator is working on _open_ terms, in stark
  contrast with the typical setting for call-by-value. See e.g.,
  #nm[Accattoli] and #nm[Guerrieri]~#mcite(<AccattoliG16>) for some
  discussion of the peculiarities of open call-by-value strategies.

  The hurdle with the left-to-right order, is that when evaluating the application $t
  llc.app u$, if $t$ reduces to a stuck normal form, it is not certain that
  this is the head variable. To convince yourself, consider the term $x
  (lambda z. z) Omega$. This would make the evaluator slightly more verbose to write
  down, with one more #kw.case expression. In fact, looking closer we can realize that our
  above evaluator is strictly speaking _not_ implementing full call-by-value.
  It is slightly more lazy, as it will happily consider $Omega (x
  (lambda y. y))$ to be in normal form. It could perhaps be dubbed weak _head_
  right-to-left call-by-value. It can be analyzed that this strategy will find
  the same stuck head variable as #nm[Lassen]'s~#mcite(<Lassen05>) _eager
  reduction_, but may converge more often.
]

Let us now define patterns and eliminators. At this point, in the previous examples,
we introduced the _negative_ or _private_ types, but as we are here in an untyped
setting where there is thus only one type, there is not much to restrict. By chance, the
_pure_ #short.llc has semantically only one kind of objects, functions, which
we are quite happy to treat as negative. It would be quite more complicated to
instanciate our generic OGS construction with an untyped #short.llc with say,
functions and booleans. Indeed, while it is not obvious at first sight, this
would make the language effectful, as treating a boolean value as a function
and applying it to an argument should trigger an exception
for "value mismatch" during evaluation.
#margin-note(dy: -2em)[
  For the particular case of exceptions, we could probably get away with
  modelling them as partiality, as we do support it thanks to the #delay.t
  monad, but conflating exceptions (i.e., the $de("Option")$ monad) with
  partiality is a rather dirty trick in constructive settings.
]

As our sole type is negative, its patterns should be entirely
trivial: they can only be a single fresh variable, that is, a placeholder whose
domain is the singleton scope $base.su th base.ze$. Eliminators are similarly
easy: the only thing one can do to a function is to apply it. There is only one (functional)
argument, so that its domain is again the singleton scope, while the target is, well,
the only type there is.

#definition[Patterns and Eliminators][
  Define #short.llc _patterns_ and _eliminators_ by the following records.

  #mathpar(block: true,
    $llc.pat cl ctx.bfam th base.nat th base.top \
     llc.pat :=
     pat(
      ctx.Oper th x & := base.top,
      ctx.dom th x th p & := base.su th base.ze
     )$,
    $llc.elim cl ctx.btfam th base.nat th base.top \
     llc.elim :=
     pat(
      ctx.Oper th x & := base.top,
      ctx.dom th x th p & := base.su th base.ze,
      ctx.tgt th x th p & := base.tt,
    )$
  )
]

We can now exhibit the isomorphism between our representation of normal forms and
the generic "split" representation $ctx.norm^(#h(0.1em)llc.pat,llc.elim)_(llc.val,llc.evc)$.

#definition[Normal Form Splitting][
  Define the following two functions, respectively splitting normal forms and folding
  them.

  $ llc.split th {n} cl llc.norm th n -> ctx.norm^(#h(0.3em)llc.pat,llc.elim)_(llc.fval,llc.fevc) th n th base.tt $
  #v(-0.8em)
  $ & llc.split th (llc.nval th v) && := ctx.nret th base.tt th [v] \
    & llc.split th (llc.nstuck th i th v th k) && := ctx.ncall th i th base.tt th [v] th k $

  $ llc.fold th {n} cl ctx.norm^(#h(0.3em)llc.pat,llc.elim)_(llc.fval,llc.fevc) th n th base.tt -> llc.norm th n $
  #v(-0.8em)
  $ & llc.fold th (ctx.nret th p th gamma) && := llc.nval th (gamma th ctx.topc) \
    & llc.fold th (ctx.ncall th i th e th gamma th k) && := llc.nstuck th i th (gamma th ctx.topc) th k $
]

#lemma[Refolding][
  $llc.split$ and $llc.fold$ form an isomorphism up to extensional equality on $ctx.norm^(#h(0.3em)llc.pat,llc.elim)_(llc.val,llc.evc)$.
] <lem-llc-refold>
#proof[By direct case analysis.]

We are finally ready to instanciate the #short.llc language with evaluator.

#definition[#short.llc Language With Evaluator][
  The #short.llc language with evaluator is given by the following record.

  $ llc.llc cl ogs.language_(llc.pat,llc.elim) th llc.fval th llc.fevc th llc.fterm kw.whr \
    pat(
      ogs.eval th t & := llc.split itree.fmap llc.eval th t,
      ogs.resume th k th p th gamma & := k[llc.v2t th (gamma th ctx.topc)],
      ogs.elim th v th e th gamma & := llc.v2t th v llc.app llc.v2t th (gamma th ctx.topc),
    ) $
]

#theorem[#short.llc respects substitutions][
  $llc.llc$ respects substitutions.
]
#proof[
First, by direct case splitting, $llc.v2t$ commutes with substitutions, i.e.
$(llc.v2t th v)[sigma] = llc.v2t th v[sigma]$. Then, prove the required properties
as follows.

- $ogs.evalsub$
- $ogs.resumesub$~ By commutation of $llc.v2t$ with substitutions, then
    application of $fil.actsub$.
- $ogs.elimsub$~ $llc.v2t$ commutes with substitutions, which concludes.
- $ogs.evalnf$ By case on the normal form.
  - For $ctx.nret th base.tt th [v]$, by case on $v$ concludes.
  - For $ctx.ncall th i th base.tt th [v] th k$, we need to prove
    $llc.eval th k[llc.var th i llc.app v] itree.eq llc.nstuck th i th v th k$.
    By induction on $k$.
    - For $k := llc.ehole$. AHHHH.....

]


=== The Named Term Translation

Our goal is now to construct a language machine out of a given language with
evaluator, and we will moreover prove that if $L$ respects substitution, then
so does the obtained language machine. To do so we apply a continuation passing
style translation. However, since we know nothing about the syntax and types of
the language, there is no clear way to model continuations. The idea is thus to
do an entirely formal translation, where we freely add types for continuations:
formally negated types. Configurations, then, consist of a pair of a continuation
variable and a term, a package which we call a _named term_. Likewise, 


Configurations are simply a pair of a continuation
variable and a term, i.e., the package of a term and its current continuation.
However, as we know very little 




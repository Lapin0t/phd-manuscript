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
$A$, and as we are now required to hide continuations, this something should be
void of any continuation abstraction. This can be recognized as the set of
_ultimate patterns_ of type $A$.

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
negative types $jwa.ntyp$ and contexts $jwa.nctx$, as well as the matching
observation family $jwa.obs cl ctx.bfam th jwa.nctx th jwa.ntyp$. We have
defined values $jwa.val$ and commands $jwa.cmd$ over general types, but it is
trivial to restrict them to negative types and contexts. To instanciate a
language machine, this leaves us to define the evaluation and application maps,
which have the following types.

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

We already have an OGS model, but to obtain correctness w.r.t. substitution
equivalence, we need to verify the hypotheses of @thm-correctness.
We are left with the two
interesting hypotheses: the core semantic argument, the JWA machine respects
substitution (@def-machine-resp-sub), and the technical side condition, that
it has finite redexes (@def-finite-redex).

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

#lemma[JWA Finite Redex][
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
continuation.

#theorem[OGS Correctness][
  For all $Gamma cl jwa.nctx$ and $c_1, c_2 cl jwa.cmd th Gamma$ if
  $ogsinterpA(c_1) itree.weq ogsinterpA(c_2)$, then for all $gamma cl Gamma
  asgn(jwa.val) Omega$, $jwa.eval th c_1[gamma] itree.weq jwa.eval th c_2[gamma]$.
] <thm-jwa-correctness>
#proof[
  By @thm-correctness, with hypotheses proven in @lem-jwa-sub, @thm-jwa-respsub and @thm-jwa-finred.
]

Note that we obtain correctness only for commands in negative contexts. This is
easily delt with, by defining an extended equivalence relation on such
commands, which first quantifies over an ultimate pattern for each type in
$Gamma cl ctx.ctxc th jwa.typ$ and asserts OGS equivalence of the configurations
substituted by the given patterns.

#definition[Extended OGS Equivalence][
  Define the lifting of $jwa.pat$ and $jwa.dom$ to scopes as follows.

  $ jwa.patX cl ctx.ctxc th jwa.typ -> base.Type \
    jwa.patX th Gamma := {A cl jwa.typ} -> Gamma ctx.var A -> jwa.pat A $

  $ jwa.domX th (Gamma cl ctx.ctxc th jwa.typ) cl jwa.patX th Gamma -> jwa.nctx $
  #v(-0.8em)
  $ & jwa.domX th ctx.nilc         && th gamma := ctx.nilc \
    & jwa.domX th (Gamma ctx.conc A) && th gamma := jwa.domX th Gamma th (gamma compose ctx.popc) ctx.catc jwa.dom th (gamma th ctx.topc) $

  Further define an embedding of pattern assignments into ordinary assignments as follows.

  $ jwa.embX th {Gamma} th (gamma cl jwa.patX th Gamma) cl Gamma asgn(jwa.val) (jwa.domX th gamma) \
    jwa.embX th gamma th i := (jwa.p2v th (gamma th i))[de("aux") th gamma th i] $

  We only give the type of the family of renamings $de("aux")$ as it is purely
  administrative.

  $ de("aux") th {Gamma} th (gamma cl jwa.patX th Gamma) th {A} th (i cl Gamma ctx.varc A) cl jwa.dom th (gamma th i) ctx.ren jwa.domX th gamma $


  Finally, for all $Gamma cl ctx.ctxc th jwa.typ$ and $c_1, c_2 cl jwa.cmd th Gamma$
  define the _extended JWA OGS equivalence_ as follows.

  $ c_1 de(approx_"ext") c_2 := (gamma cl jwa.patX th Gamma) -> ogsinterpA(c_1[jwa.embX th gamma]) itree.weq ogsinterpA(c_2[jwa.embX th gamma]) $
]

#theorem[Extended OGS Correctness][ \
  For all $Gamma cl ctx.ctxc th jwa.ntyp$ and $c_1, c_2 cl jwa.cmd th Gamma$ if
  $c_1 de(approx_"ext") c_2$, then for all $gamma cl Gamma
  asgn(jwa.val) Omega$, $jwa.eval th c_1[gamma] itree.weq jwa.eval th c_2[gamma]$.
]
#proof[
  By pointwise lifting of $jwa.v2p$ and $jwa.v2a$ on $gamma$, compute $alpha
  cl jwa.patX th Gamma$ and $beta cl jwa.domX th alpha asgn(jwa.val)
  Omega$. By $c_1 de(approx_"ext") c_2$, we have

  $ ogsinterpA(c_1[jwa.embX th alpha]) itree.weq ogsinterpA(c_2[jwa.embX th alpha]). $

  From @thm-jwa-correctness, deduce

  $ jwa.eval th c_1[jwa.embX th alpha][beta] itree.weq jwa.eval th c_2[jwa.embX th alpha][beta]. $

  Finally by pointwise lifting of @lem-jwa-refold we have $(jwa.embX th
  alpha)[beta] approx gamma$, which concludes.
]

#remark[
  Of course both the basic and the extended correctness results would hold just as
  well for normal form bisimulation instead of the OGS strategy equivalence,
  since @thm-nf-correctness reduces normal form bisimulation to OGS strategy
  equivalence generically.
]

This concludes the instanciation of our generic framework for JWA. Arguably,
although defining the actual data takes some getting used to, the proof mostly
amount to busywork. The only meaningful lemma to be designed and proven is the
refolding lemma.

== Polarized #short.uuc <sec-inst-mumu>

Our next instance serves as a demonstration of the limits of what can be
captured by our model. Technically, the structure will not be much different
than the previous one, but simply scaled up. As such, we will give a bit less
details on the tedious case splitting on the syntax.

#short.uuc is a quite featureful language, which was introduced by #nm[Curien]
and #nm[Herbelin]~#mcite(<CurienH00>) as a computational counter-part (i.e. a
term assignment) to the sequent calculus. JWA had already the feel of a low-level
language, with its commands and jumps, but in some respect #short.uuc goes a
step further. Its core idea is to define 
As an introduction to the language, we can recommend
the recent tutorial on the subject WIP #mcite(<BinderTMO24>)

== Natural Deduction Style Calculi <sec-inst-nd>

=== In

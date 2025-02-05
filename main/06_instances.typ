#import "/lib/all.typ": *

= OGS Instances <ch-instance>

In @ch-ogs we have seen a language-generic OGS construction, parametrized by an
abstract notion of language machine. We have even seen a shiny theorem,
correction for this model w.r.t. substitution  equivalence, our variant of
observational equivalence. Hopefully some intuitions from the introduction
helped understand these abstract constructions, but it is now time to look at
some concrete examples. In this chapter we try to show a small but
representative collection of calculi that are covered by our abstract theorem.
We start with two calculi neatly fitting our language machine presentation,
finally showing the driving intuitions behind our axiomatization. To warm
up we start with perhaps the simplest one: Jump-with-Argument (@sec-inst-jwa).
We then follow up with a much more featureful language, polarized #short.uuc
(@sec-inst-mumu). Then, in @sec-inst-krivine, we look at a language which for
several reasons does not look like the prototypical language machine, but still
can be twisted (rather heavily) to fit our axiomatization: pure untyped #short.llc
under weak head reduction.

#remark[
  Be advised that at the time of writing these lines, the set of example calculi
  presented in this chapter is not exactly the same as the one present in our Rocq
  artifact. Their respective features are broadly the same, and our present choice
  is guided by making this collection more comprehensive. I invite you to check the
  #link("https://github.com/lapin0t/ogs")[online
  repository]#margin-note(link("https://github.com/lapin0t/ogs")) to see
  if this has been fixed by the time you are reading.
]

== Jump-with-Argument <sec-inst-jwa>

=== Syntax

Jump-with-Argument (JWA) was introduced by #nm[Levy]~#mcite(<Levy04>) as a
target for his _stack passing style_ transform of Call-By-Push-Value
(CBPV). As such, it is a minimalistic language with first-class
continuations centered around so-called _non-returning commands_: an ideal
target for our first language machine.
We direct the interested reader to two existing
constructions of NF bisimulations and OGS-like model for increasingly
featureful variants of JWA by #nm[Levy] and
#nm[Lassen]~#mcite(<LassenL07>)#mcite(dy: 3em, <LassenL08>).
This is a typed
language, so as is usual, there is some leeway regarding which types are
included. As we are aiming for simplicity, we will only look at a
representative fragment featuring three types of values: booleans $jwa.base$,
continuations $jwa.neg A$ and pairs $A jwa.prod B$.

The language consists of two judgments: non-returning commands and values. Commands play the
role of the configurations of an abstract machine, and are only parametrized by
a scope. They are of three kinds: sending a value to a continuation (the
eponymous "jump with argument"), splitting a value of product type into its
two components and case splitting on a boolean. Values are parametrized by a
scope and a type and can be either a variable, a continuation abstraction which
binds its argument and continues as a command, a pair of values or a boolean.
Let us present its syntax by an intrinsically typed and scoped representation
inside type theory.

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

#remark[
  Among the surprising elements is probably the continuation abstraction $jwa.vlam c$.
  Intuitively it can be understood as a #sym.lambda\-abstraction, but which never returns.
  As such, its body is not a term as in #short.llc but a non-returning command.
  The "jump-with-argument" $v jwa.capp k$ can then be seen as the counter-part
  to function application, written in reverse order.
]

#lemma[Substitution][
  JWA values form a substitution monoid, and JWA commands form a substitution
  module over it. Moreover, $jwa.val$ has decidable variables. In other
  words, the following typeclasses are inhabited: $sub.mon th jwa.val$,
  $sub.mod th jwa.val jwa.cmd$ and $sub.decvar th jwa.val$.
] <lem-jwa-sub>
#proof[
  Although quite tedious, these constructions are entirely
  standard~#mcite(dy: -5.5em, <FioreS22>)#mcite(dy: -3.8em, <AllaisACMM21>). One
  essentially starts by mutually defining the renaming operation on commands
  and values, unlocking the definition of the weakening operation necessary
  for substitution. Then, on top of this, one mutually defines the
  substitution operation, giving the monoid and module structures. The proofs
  of the laws as similarly layered.
]

=== Patterns and Negative Types

The next logical step is the definition of the evaluation. Informally, the reduction rules
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

Recall from the introduction (@sec-intro-ogs) that in OGS models, depending on their type, some
values are "given" to the opponent as part of a move, while some other are
"hidden" behind fresh variables. We did not, however, worry about this
distinction at all during our generic development, as we simply assumed there
was a set of types $T$ and worked on top of that. This discrepancy is simply
explained: what the generic construction considers as _types_ should not be
instantiated to all of our language's types, but only the ones that are
interacted with, i.e., the "hidden" types.

Most eloquently described in the case of CBPV~#mcite(<Levy04>), this split
occurs between types that have dynamic behavior, the _computation types_ and
the ones that have static content, the _value types_. For concision we will
call them respectively _negative_ and _positive_ types. Although the concrete
assignment of types to either category can be somewhat varied, obtaining models
with different properties, for JWA it is most natural to decide that
continuations are negative types while booleans and pairs are positive.

#definition[Negative Types][
The definition of JWA negative types is based on a strict predicate picking out
the continuation types.

#mathpar(block: true,
block[$ jwa.isneg cl jwa.typ -> base.sProp $
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
  of informality by using $jwa.neg A$ as an element of $jwa.ntyp$, instead of the more
  correct $(jwa.neg A, base.tt)$. Moreover, we will do as if elements of $jwa.ntyp$
  could be pattern-matched on, with the sole pattern being $jwa.neg A$, although
  technically this has to be justified with a
  _view_~#mcite(<McBrideM04>)#mcite(dy: 2em, <Allais23>), adding a small amount of
  syntactic noise.
]

#lemma[Restricted Values and Commands][
  The family of values and commands restricted to negative scopes and types defined as

  $ (kw.fun th Gamma th alpha |-> jwa.val th Gamma .base.fst th alpha .base.fst) cl base.Type^(jwa.nctx,jwa.ntyp) \
    (kw.fun th Gamma |-> jwa.cmd th Gamma .base.fst) cl base.Type^jwa.nctx $

  again form respectively a substitution monoid and a substitution module, with respect
  to the subset scope structure (@def-subset-scope).

  We will overload the notations $jwa.val$ and $jwa.cmd$ for both the
  unrestricted and restricted families. Similarly we will stop writing the
  projection $base.fst$ and implicitly use it as a coercion from negative
  types and scopes to normal ones.
]
#proof[By #sym.eta\-expansion of the records and functions witnessing the unrestricted structures.]

For these negative types, i.e., continuations, we need to devise a notion of
observation which will make up the content of the OGS moves. The only sensible
thing to do with a continuation $jwa.neg A$ is to send it something of type
$A$. As our goal is to hide continuations from moves, this something should
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

#remark[
  The continuation pattern $jwa.plam_A$ should be understood intuitively as the
  pattern consisting of one fresh variable. This is comforted by the fact
  that its domain is indeed a singleton scope. More generally, the domain of
  a pattern collects the set of continuations inside a value, when seeing
  patterns as a subset of values.
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
during the OGS game, since only negative variables are exchanged), split it into an ultimate pattern and a filling assignment.

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

Lets recapitulate where we stand in the instantiation. We have defined the
negative types $jwa.ntyp$ and scopes $jwa.nctx$, as well as the matching
observation family $jwa.obs cl ctx.bfam th jwa.nctx th jwa.ntyp$. We have
defined values $jwa.val$ and commands $jwa.cmd$ over general types and then
restricted them to negative types and scopes. To instantiate a language
machine, this leaves us to define the evaluation and application maps, which
have the following types.

$ ogs.eval th {Gamma cl jwa.nctx} cl jwa.cmd th Gamma -> delay.t th (ctx.norm^(""jwa.obs)_jwa.val th Gamma) \
  ogs.apply th {Gamma cl jwa.nctx} th {A cl jwa.ntyp} th (v cl jwa.val th Gamma th A) th (o cl jwa.obs"".ctx.Oper th A) \
    quad cl jwa.obs"".ctx.dom th o asgn(jwa.val) Gamma -> jwa.cmd th Gamma $

Let us start with the evaluation map. Although it is not really necessary, for
clarity we will implement an _evaluation step_ function, taking a command
to either a normal form or to a new command to be evaluated further. The evaluation map is
then simply obtained by unguarded iteration in the #delay.t monad.

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
quantified over negative types, instead of explicitly asking that it is a
continuation type. This is an artifact of the language machine axiomatization and in this
case it would be better written with the following isomorphic representation.

$ jwa.apply th {Gamma cl jwa.nctx} th {A cl jwa.typ} th (v cl jwa.val th Gamma th jwa.neg A) th (o cl jwa.pat th A) \
    quad cl jwa.dom o asgn(jwa.val) Gamma -> jwa.cmd th Gamma $

What needs to be done is then more clear: embed the pattern, substitute it by the given assignment, and
send the whole thing to the continutation value $v$.

#definition[Observation Application][
  Define observation application as follows.

  $ jwa.apply th {Gamma cl jwa.nctx} th {A cl jwa.ntyp} th (v cl jwa.val th Gamma th A) th (o cl jwa.obs"".ctx.Oper th A) \
    quad cl jwa.obs"".ctx.dom th o asgn(jwa.val) Gamma -> jwa.cmd th Gamma \
    jwa.apply th {Gamma} th {jwa.neg A} th v th o th gamma := (jwa.p2v th o)[gamma] jwa.capp v $
] <def-jwa-obsapp>

We now have everything to instantiate the JWA language machine.

#definition[Language Machine][
  The JWA language machine is given by the following record.

  $ jwa.jwa cl ogs.machine th jwa.obs th jwa.val th jwa.cmd \
    jwa.jwa := pat(
      ogs.eval   & := jwa.eval,
      ogs.apply  & := jwa.apply,
      ogs.evalext & := ...,
      ogs.appext & := ...
    ) $

  Note that $ogs.appext$ is proven by direct application of $sub.sext$ from the
  substitution monoid structure of values. $ogs.evalext$ is obtained by simple rewriting,
  as extensional equality of commands is simply propositional equality.
]

By the above definition we can already instantiate the OGS model, but
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

  Proceed by tower induction and then by cases on $c$, following the elimination
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
      = quad & (jwa.eval th (v[sigma] jwa.capp jwa.vlam c'[sigma[ctx.popc],ctx.topc])) .itree.obs & #[by def.] \
      = quad & itree.tauF th (jwa.eval th c'[sigma[ctx.popc],ctx.topc][sub.var,v[sigma]]) quad & #[by def.] \
      = quad & itree.tauF th (jwa.eval th c'[sub.var,v][sigma]) quad & #[by sub. fusion] $
    Unfolding the RHS reduces to $ itree.tauF th (jwa.eval th c'[sub.var,v] itree.bind kw.fun th n |-> jwa.eval th (ogs.emb th n)[sigma]). $
    The two $itree.tauF$ provide a synchronization and we conclude by coinduction hypothesis on $c'[sub.var,v]$

  - $jwaletin((jwa.vvar th i), c')$ #sym.space.quad Impossible by $base.exfalso th (ctx.eltupg th i)$.
  - $jwaletin(jwavpair(v,w), c')$ #sym.space.quad Unfold the LHS and rewrite as follows.
    $ & (jwa.eval th (jwaletin(jwavpair(v,w), c'))[sigma]) .itree.obs & \
      = quad & (jwa.eval th (jwaletin(jwavpair(v[sigma],w[sigma]), c'[sigma[ctx.popc compose ctx.popc, ctx.popc th ctx.topc, ctx.topc]]))) .itree.obs & #[by def.] \
      = quad & itree.tauF th (jwa.eval th c'[sigma[ctx.popc compose ctx.popc], ctx.popc th ctx.topc, ctx.topc][sub.var,v[sigma],w[sigma]]) & #[by def.] \
      = quad & itree.tauF th (jwa.eval th c'[sub.var,v,w][sigma]) quad & #[by sub. fusion] \
    $
    Unfolding the RHS reduces to $ itree.tauF th (jwa.eval th c'[sub.var,v,w][sigma] itree.bind kw.fun th n |-> jwa.eval th (ogs.emb th n)[sigma]). $
    The two $itree.tauF$ provide a synchronization and we conclude by coinduction hypothesis on $c'[sub.var,v,w]$

  This concludes $ogs.evalsub$. Although slightly tedious, it is not hard to prove. As we will
  see in other instances, the pattern is always the same: analyzing the configuration to make
  the evaluation reduce, upon hitting a redex, shift substitutions around and conclude by coinduction.
  Upon hitting a normal form, apply a refolding lemma and conclude by reflexivity.

  Thankfully the other two properties are almost trivial. $ogs.appsub$ is a
  direct application of substitution fusion, as follows.

  $        & jwa.apply th v[sigma] th o th gamma[sigma] & \
    = quad & (jwa.p2v th o)[gamma[sigma]] jwa.capp v[sigma] quad quad & #[by def.] \
    = quad & ((jwa.p2v th o)[gamma] jwa.capp v)[sigma] quad quad & #[by sub. fusion] \
    = quad & (jwa.apply th v th o th gamma)[sigma] & #[by def.] $

  $ogs.evalnf$ is proven by unicity of splitting after one-step unfolding, as follows.

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
  As explained for @def-jwa-obsapp, we silently do a benign preprocessing to express the property using
  patterns instead of observations, for else the notational weight would be
  unbearable. We need to prove that the relation defined by the following inference rule is well founded.

  #inferrule(
    ($i cl Gamma ctx.var alpha_1$,
     $o_1 cl jwa.pat th alpha_1$,
     $gamma_1 cl jwa.dom th o_1 asgn(jwa.val) Gamma$,
     $v cl jwa.val th Gamma th jwa.neg alpha_2$,
     $o_2 cl jwa.pat th alpha_2$,
     $gamma_2 cl jwa.dom th o_2 asgn(V) Gamma$,
     $H_1 cl sub.isvar th v -> base.bot$,
     $H_2 cl jwa.eval th (jwa.apply th v th o_2 th gamma_2) itree.eq itree.ret th ((i ctx.cute o_1), gamma_1)$
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
  The above proof of finite redex is quite remarkable: no "redex failure" can happen,
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
  Conclude by the fact that $itree.weq$ is an equivalence
  relation#margin-note(mark: true)[
    For the beauty of the game, let us say that a tiny generalization of the
    last proof step, shifting an equivalence relation around a bi-implication,
    is a very useful fact of any symmetric transitive relation $R$,
    namely that $R xrel(R rel.arr R rel.arr (<->)) R.$
  ].
]

We also obtain NF model correctness in the exact same way.

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

Note that we obtain correctness only for commands in negative scopes. This is
easily dealt with, by defining an extended equivalence relation on
commands in arbitrary scopes $Gamma cl ctx.ctxc th jwa.typ$, which first quantifies over an ultimate pattern for each type in
$Gamma$ and asserts OGS equivalence of the configurations
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

  We only give the type of the required family of renamings $de("aux")$ as it is not a joy
  to write down.

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
  By pointwise lifting of $jwa.v2p$ and $jwa.v2a$ applyied to $gamma$, compute $alpha
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
  considering NF bisimularity instead of the OGS strategy
  bisimilarity, by following exactly the same step, replacing the OGS
  interpretation by the NF strategy interpretation.
]

This concludes the instantiation of our generic framework for JWA. Arguably,
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

#let cbv = txsc("Cbv")
#let cbn = txsc("Cbn")

depending on which of $uut.mu$ or $uut.mut$ reduces first. A simple way
to overcome this non-determinism is to bias the calculus to either
call-by-value, prioritizing #uut.mu or call-by-name, prioritizing #uut.mut.
We adopt the other standard solution, arguably more general, which is to
parametrize configurations by a mode, or _polarity_, recording whether they are
currently in call-by-value mode (#uut.pp) or call-by-name mode (#uut.pn). This
_polarized_ #short.uuc thus has the ability to express both execution
strategies. In effect, each type is assigned a polarity, and the polarity of a
configuration is determined by the type on which it is cutting. The type system
is entirely symmetric with respect to polarity, so that every type former has a
dual of opposite polarity. Do not confuse the #cbv\-#cbn duality of
type polarities with the producer-consumer duality of terms and coterms as the
two are entirely orthogonal!

The concrete way by which the priority of the #uut.mu or #uut.mut rule is
managed is by restricting both of their reduction rules to only apply when the
other side of the configuration is a _value_. Now pay attention because the
different dualities mingle!

- A *value of #cbv type* is a new syntactic category included in terms,
  the _weak head normal terms_, consisting of variables and of
  _constructors_ of that type.
- A *covalue of #cbv type* is simply a coterm of that type.
// LOL
#scale(x: -100%, y: -100%)[
  - A *covalue of #cbn type* is a new syntactic category included in
    coterms, _weak head normal coterms_, consisting of covariables and of
    _destructors_ of that type.
  - A *value of #cbn type* is simply a term of that type.
]

We hope that all the symmetries are enjoyable. The consequence is that at a
#cbv type, the #uut.mu reduction rule will fire across any coterm, while
the #uut.mut rule will only fire across a weak-head normal term (of which
#uut.mu is not). The opposite happens at #cbn types.

Technically, our polarized presentation approximately follows the one from
#nm[Downen] and #nm[Ariola]~#mcite(<DownenA20>), obtaining a middle
ground between their #nm[System L] and #nm[System D]. For a more general
introduction to unpolarized #short.uuc, we can recommend the tutorial by
#nm[Binder] _et. al_~#mcite(dy: 0.5em, <BinderTMO24>).

Without further ado, let us jump
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
    inferrule("", $uut.tone cl uut.xtyp th Theta th uut.pp$),
    inferrule("", $uut.tbot cl uut.xtyp th Theta th uut.pn$),
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
product and sum types, each in their #cbv ($uut.tzer$, $uut.tone$,
$uut.tten$, $uut.tplu$) and #cbn ($uut.tbot$, $uut.ttop$, $uut.tand$,
$uut.tpar$) variants. We then have the two shifts, $uut.tdw$ for _thunks_ of
a #cbn type and $uut.tup$ for _returners_ of a #cbv type, and two
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

#figure(placement: bottom, caption: [#short.uuc Syntax],
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

We now define the infrastructure for patterns: first the _observable_
subset of side-annotated types, which will appear in the OGS game, then the
patterns, their embedding into values, and finally the splitting of values into
a pattern and a filling, together with the associated refolding lemmas. In JWA
we called the observable types "negative", but here this word is already quite
overloaded so we call them "private" instead. Recall that these are the types
that will appear in the OGS construction, as they denote syntactic objects
whose sharing between players is mediated by variables. Their definition follows
the pattern of values, with only #cbv consumers and #cbn producers being considered
private.

#definition[Private Types][
  Define private types as a subset of types given by the following predicate.

  #mathpar(block: true,
    block[
      $ uut.isneg cl uut.styp -> base.sProp $
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
language machine instantiation. This starts by defining observations, and as for JWA,
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

With patterns defined, we introduce the embedding and splitting in one go. We do not
spell out their definition but only characterize it by its refolding properties as
writing them down would become quite unwieldy.

#definition[Value Splitting][
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
  two auxiliary properties respectively concerned with #cbv weak head normal terms and
  #cbn weak head normal coterms. The second property (unicity of
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
    & uut.evalstep th & agl uut.vw th uutabs(uut.tand, c_1, c_2) & xpn uut.vw th (uut.vsnd th k) agr && := base.inj2 th c_2[sub.var,k] \
    & uut.evalstep th & agl uut.vw th uut.vdw t & xpp uut.vw th uutpm(uut.tdw, c) agr && := base.inj2 th c[sub.var,t] \
    & uut.evalstep th & agl uut.vw th uutabs(uut.tup, c) & xpn uut.vw th uut.vdw e agr && := base.inj2 th c[sub.var,e] \
    & uut.evalstep th & agl uut.vw th uut.vmin k & xpp uut.vw th uutpm(uut.tmin, c) agr && := base.inj2 th c[sub.var,k] \
    & uut.evalstep th & agl uut.vw th uutabs(uut.tneg, c) & xpn uut.vw th uut.vneg v agr && := base.inj2 th c[sub.var,v] \
    & uut.evalstep th & agl uut.vw th (uut.vmu th v) & xpp uut.vw th uutpm(uut.tmu, c) agr && := base.inj2 th c[sub.var,v] \
    & uut.evalstep th & agl uut.vw th uutabs(uut.tnu, c) & xpn uut.vw th (uut.vnu th k) agr && := base.inj2 th c[sub.var,k]
  $
]

#remark[
  It should not be obvious, but it can be checked that all the (co)terms and
  weak head normal (co)terms by which we are substituting are indeed (co)values,
  with the type polarity and side annotation properly lining up.
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
      ogs.evalext & := ...,
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

    Proceed by tower induction, then pattern match on $c$, following the case tree of $uut.evalstep$. In
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

== Untyped Weak Head #short.llc <sec-inst-krivine>

Our first two examples were in several aspects quite similar: two simply-typed
languages, rather low level and centered around explicit control flow using
some form of first-class continuations. Let us now turn to a radically
different language: pure untyped #short.llc with weak head reduction semantics.
There will be several hurdles to overcome, so let us give an overview, in increasing
order of difficulty.

*Typing* #sym.space.quad The language is untyped, but our framework for
substitution requires some set of types. This is quite easy to overcome with a
benign change of perspective, as we can see any untyped language as an
un#[*i*]typed language, that is, a language with a single type.

*Configurations* #sym.space.quad The language is presented with natural
deduction style judgments, as opposed to language machines and the first two
examples, which have sequent calculus style judgments. What we mean by this, is
that the #short.llc is usually presented without any notion which would be
similar to a language machine's configurations: the thing on which the
evaluator operates and which is only indexed by a scope. The way out is
two-fold.

First, we switch to a common, but perhaps not the most standard presentation of
weak head reduction: some variant of the #nm[Krivine]
machine~#mcite(<Curien93>). This is a bit of a goalpost moving, as arguably we
will not present a #short.llc language machine but rather a #nm[Krivine]
language machine. However it is best to go with the flow of the axiomatization
and adopt the abstract machine mindset. This will pay off when proving the
correctness theorem hypotheses.

Second, since continuations, a.k.a. _stacks_, will start floating around our
#nm[Krivine] machine configurations, we will need to introduce formal
continuations, i.e., a new kind of variable denoting continuations. Indeed,
during the OGS game and in the NF interpretation, we will need to exchange
symbolic continuations with our opponent. To distinguish them from the already
existing "term" variables there is a simple mean: typing. We had a single type,
now we already have two: one for terms and one for continuations. To avoid
confusion, we will stop referring to them as types and instead call them
_sorts_.

In a sense, our #nm[Krivine] machine will operate on _radically open_ configurations,
in the sense that not only terms might contain free variables, but also stacks!

*Observations* #sym.space.quad The usual intuition behind the design of the
binding family of observations is that they denote some kind of copatterns, or
eliminators. This understanding is enough to get a satisfying definition when
the language already circles around this concept, like our first two examples.
More pragmatically, as our axiomatization derives the normal forms
from these observations, we better engineer them to fit the normal forms we
intend to have. For call-by-value #short.llc, as sketched in the introduction
(@sec-intro-ogs), it does not take much squinting to see that the two shapes of
normal forms---a value and a stuck application in an evaluation context---do
indeed look like eliminators. Namely calls (on opponent functions) and returns
(on implicit opponent continuations).

For weak head reduction #short.llc, there are two shapes for normal forms: lambda
abstractions $lambda x.T$ and stuck applications $x T_1 ... T_n$. Applications
are not too difficult to see as being eliminators. We deduce that in this
world, functions are eliminated by giving not one but a whole spine of arguments. In
fact, one can recognize this spine as a stack, which is nice since our earlier
choices start to make more sense. However, the lambda abstraction is rather
devilish. It does not look like it is stuck on anything, so once again, this
must be an elimination on an implicit context/stack variable. But which part
of $lambda x.T$ is the pattern (the static part) and the filling? Lets look
at it backwards: what kind of elimination would make sense for a stack? Stacks
are sequences of terms, so it would make sense to pattern match on them. And indeed,
the $lambda x.T$ normal form is simply a request to _grab_ the next argument
from the stack. If the stack is empty, this request cannot be fulfilled. But
if it is not, the opponent may answer the request by a "here it is", giving us two
new handles, a term variable for the head and a stack variable for the rest.
Another way to look at requests is to understand them as fully evaluated,
or _forced_ functions.

Putting things back together, what we just did is to introduce a _third_ sort,
for argument _requests_, which will accordingly need be accompanied by
request variables. Eliminating a stack introduces a new _request variable_ for
the opponent, and eliminating a request introduces a term variable and a stack
variable.

Let us formalize that!

=== Syntax and Semantics

#definition[Sorts][
  Define _sorts_ as the following data type.

  $ kw.dat th kriv.sort cl base.Type := kriv.stm th | th kriv.sstk th | th kriv.sreq $

  Further define _contexts_ by the following shorthand $kriv.ctx := ctx.ctxc th kriv.sort$.
]

Instead of writing three mutually defined judgments for terms, stacks and
requests, we will simply use a single syntactic judgment, indexed by sorts.
This will have the happy side effect to fuse the three different variables in a
single sorted construct. Note that we did not talk a lot about
_configurations_, but they unsurprisingly pair a term with a stack.

#definition[Syntax][
  Define the unified judgment for _syntax_ as the data type $kw.dat th kriv.syn cl base.Type^(kriv.ctx,kriv.sort)$
  with the following constructors.

  #mathpar(block: true, spacing: 0em,
    inferrule(
      $Gamma ctx.varc th s$,
      $kriv.var th i cl kriv.syn th Gamma th s$
    ),
    inferrule(
      ($a cl kriv.syn th Gamma th kriv.stm$, $b cl kriv.syn th Gamma th kriv.stm$),
      $a kriv.app b cl kriv.syn th Gamma th kriv.stm$
    ),
    inferrule(
      $r cl kriv.syn th Gamma th kriv.sreq$,
      $krivreq(r) cl kriv.syn th Gamma th kriv.stm$
    ),
    inferrule(
      $a cl kriv.syn th (Gamma ctx.conc kriv.stm) th kriv.stm$,
      $kriv.lam th a cl kriv.syn th Gamma th kriv.sreq$
    ),
    inferrule(
      ($a cl kriv.syn th Gamma th kriv.stm$, $k cl kriv.syn th Gamma th kriv.sstk$),
      $a kriv.cons k cl kriv.syn th Gamma th kriv.sstk$ 
    ),
  )

  Further define the judgment for _configurations_ as the data type $kw.dat th kriv.conf cl base.Type^kriv.ctx$
  with the following constructor.

  #block(inferrule(
    ($a cl kriv.syn th Gamma th kriv.stm$, $k cl kriv.syn th Gamma th kriv.sstk$),
    $krivcfg(a,k) cl kriv.conf th Gamma$
  ))
]

#lemma[Substitution][
  The family $kriv.syn$ forms a substitution monoid with decidable variables, and $kriv.conf$ forms a substitution module
  over it.
] <lem-kriv-sub>
#proof[
  Although the meaning of $kriv.syn$ is perhaps still puzzling, it can be opaquely viewed as
  an arbitrary syntax with bindings. As such, the renaming and substitution operators and
  their laws can be derived by standard means.
]

We can now define the binding family of observations. Because technically there is exactly
one observation at each sort, we could take the tricky $kw.fun th s |-> base.unit$
definition. The $ctx.dom$ map would be quite puzzling though, so that we prefer defining
a special purpose family and give these observations nice names.

#definition[Observations][
  Define the family of _observations_ as the data type $kw.dat th kriv.fobs cl base.Type^kriv.sort$
  with the following constructors.

  #mathpar(block: true, spacing: 1fr,
    inferrule($$, $kriv.force cl kriv.fobs th kriv.stm$),
    inferrule($$, $kriv.grab cl kriv.fobs th kriv.sstk$),
    inferrule($$, $kriv.push cl kriv.fobs th kriv.sreq$),
  )

  Define their _domain_ by the following function.

  $ kriv.dom th {s} cl kriv.fobs th s -> kriv.ctx $
  #v(-0.8em)
  $ & kriv.dom th kriv.force && := ctx.nilc ctx.conc kriv.sstk \
    & kriv.dom th kriv.grab && := ctx.nilc ctx.conc kriv.sreq \
    & kriv.dom th kriv.push && := ctx.nilc ctx.conc kriv.stm ctx.conc th kriv.sstk $

  Further define their binding family as follows.

  $ kriv.obs cl ctx.bfam th S th T \
    pat(
      ctx.Oper th s & := kriv.fobs th s,
      ctx.dom th o  & := kriv.dom th o,
    ) $
]

Let us recapitulate. We have a $kriv.force$ observation on terms, which has one argument: a stack
in which it should be evaluated. We have a $kriv.grab$ observation on stacks,
which has one argument: a request, that is, a lambda abstraction. And finally we have a $kriv.push$
observation on requests, which has two arguments: a head term and a tail stack. We are ready
to see the evaluator.

#definition[Evaluator][
  Define the _evaluation_ map by iteration of the following _evaluation step_ map.

  #let cxl = cs(sym.angle.l + th)
  #let cxr = cs(th + sym.angle.r)
  #let cxm = $cs(cbin(||))$

  $ kriv.eval th {Gamma} cl kriv.conf th Gamma -> delay.t th (ctx.norm_kriv.syn^(#h(0.2em) kriv.obs) th Gamma) $
  #v(-0.8em)
  $ kriv.eval := itree.iter th (itree.ret compose kriv.evalstep) $

  $ kriv.evalstep th {Gamma} cl kriv.conf th Gamma -> ctx.norm_kriv.syn^(#h(0.2em) kriv.obs) th Gamma base.sum kriv.conf th Gamma $
  #v(-0.8em)
  $ & kriv.evalstep th & cxl kriv.var th i & cxm k cxr && := base.inj1 th (i ctx.cute kriv.force, [ k ]) \
    & kriv.evalstep th & cxl a kriv.app b & cxm k cxr && := base.inj2 th krivcfg(a, b kriv.cons k) \
    & kriv.evalstep th & cxl krivreq(r) & cxm kriv.var i cxr && := base.inj1 th (i ctx.cute kriv.grab, [ r ]) \
    & kriv.evalstep th & cxl krivreq(kriv.var th i) & cxm b kriv.cons k cxr && := base.inj1 th (i ctx.cute kriv.push, [ b, k ]) \
    & kriv.evalstep th & cxl krivreq(kriv.lam th a) & cxm b kriv.cons k cxr && := base.inj2 th krivcfg(a[sub.var,b], k) $
]

Let us rejoice! The journey to obtain this may have been convoluted, but the
resulting observations and evaluator are even shorter than for JWA. In fact, once
the pattern is ingrained, the proofs that this language machine verifies the
correctness hypotheses are similarly straightforward. The sole exception is that the
well-foundedness of our so called _redex failure_ relation will not be
entirely vacuous, as indeed chains of length greater than zero do exist. This
phenomenon is a trademark of natural deduction style calculi implemented as
abstract machines. But before jumping to the proofs, let us actually define the
observation application map and finally the language machine.

#definition[Observation Application][
  Define the observation application map as follows.

  $ kriv.apply th {Gamma th s} th (x cl kriv.syn th Gamma th s) th (o cl kriv.fobs th s) cl kriv.dom th o asgn(kriv.syn) th Gamma -> kriv.conf th Gamma $
  #v(-0.8em)
  $ & kriv.apply th a th kriv.force th gamma && := krivcfg(a, gamma th ctx.topc) \
    & kriv.apply th k th kriv.grab th gamma && := krivcfg(krivreq(gamma th ctx.topc), k) \
    & kriv.apply th r th kriv.push th gamma && := krivcfg(krivreq(r), gamma th (ctx.popc th ctx.topc) kriv.cons gamma th ctx.topc) $
]

#definition[Language Machine][
  Define the #nm[Krivine] language machine by the following record.

  $ kriv.kriv cl ogs.machine_kriv.obs th kriv.syn \
    kriv.kriv := \
    pat(
      ogs.eval & := kriv.eval,
      ogs.apply & := kriv.apply,
      ogs.evalext & := ...,
      ogs.appext & := ...
    ) $
]

#lemma[Machine Respects Substitution][
  The #nm[Krivine] language machine respects substitution.
] <lem-kriv-resp-sub>
#proof[
  - $ogs.evalsub$ #sym.space.quad Given $Gamma, Delta cl kriv.ctx$, $c cl kriv.conf th Gamma$ and
    $sigma cl Gamma asgn(kriv.syn) Delta$, we need to prove the following statement.

    $ kriv.eval th c[sigma] itree.eq kriv.eval th c itree.bind kw.fun th n |-> kriv.eval th (ogs.emb th n)[sigma] $

    Proceed by coinduction, then destruct $c$ following the pattern of $kriv.evalstep$.

    - When $c := krivcfg(kriv.var th i, k)$, by reflexivity.
    - When $c := krivcfg(a kriv.app b, k)$, by synchronization and coinduction hypothesis.
    - When $c := krivcfg(krivreq(r), kriv.var th i)$, by reflexivity.
    - When $c := krivcfg(krivreq(kriv.var th i), b kriv.cons k)$, by reflexivity.
    - When $c := krivcfg(krivreq(kriv.lam th a), b kriv.cons k)$, the LHS is definitionally equal
      to $ itree.tauF th (kriv.eval th krivcfg(a[sigma[ctx.popc],ctx.topc][sub.var,b], k[sigma])). $
      Rewrite it to the following and conclude by synchronization and coinduction hypothesis.
      $ itree.tauF th (kriv.eval th krivcfg(a[sub.var,b][sigma], k[sigma])) $
  - $ogs.appsub$ #sym.space.quad By direct case analysis on the observation.
  - $ogs.evalnf$ #sym.space.quad By direct case analysis on the normal form.
#v(-1.9em)
]

#lemma[Finite Redexes][
  The #nm[Krivine] language machine has finite redexes.
] <lem-kriv-finred>
#proof[
  Recall that we need to prove the following relation to be well-founded.

  #inferrule(
    ($i cl Gamma ctx.var s_1$,
     $o_1 cl kriv.fobs th s_1$,
     $gamma_1 cl kriv.dom th o_1 asgn(kriv.syn) Gamma$,
     $x cl kriv.syn th Gamma th s_2$,
     $o_2 cl kriv.fobs th s_2$,
     $gamma_2 cl kriv.dom th o_2 asgn(kriv.syn) Gamma$,
     $H_1 cl sub.isvar th v -> base.bot$,
     $H_2 cl kriv.eval th (kriv.apply th x th o_2 th gamma) itree.eq itree.ret th ((i ctx.cute o_1), gamma_1)$
    ),
    $ogs.badc th H_1 th H_2 cl o_1 ogs.badinst o_2$
  )

  Introduce $s_2$ and $o_2 cl kriv.fobs th s_2$ and let us show that $o_2$ is accessible. By
  constructor, assume $s_1$ and $o_1 cl kriv.fobs th s_1$ such that $o_1 ogs.badc o_2$, and
  let us show that $o_1$ is accessible. Destruct the relation witness and
  introduce all the hypotheses as above. Proceed by case on $o_2$.

  1. When $o_2 := kriv.push$, then $x$ must be a request.
     - When $x := kriv.var th i$, then $H_1$ is absurd.
     - When $x := kriv.lam th a$, then $H_2$ is absurd as $kriv.apply th (kriv.lam th a) th kriv.push th gamma$
       will perform an evaluation step.
  2. When $o_2 := kriv.grab$, then $x$ must be a stack.
     - When $x := kriv.var th i$, then $H_1$ is absurd.
     - When $x := b kriv.cons k$, let $r := gamma th ctx.topc$.
       - When $r := kriv.var th i$, by $H_2$, $o_1$ must be $kriv.push$, which is accessible by (1).
       - When $r := kriv.lam th a$, then $H_2$ is absurd.
  3. When $o_2 := kriv.force$, then $x$ must be a term. Proceed by case on $x$.
     - When $x := kriv.var th i$, then $H_1$ is absurd.
     - When $x := a kriv.app b$, then $H_2$ is absurd.
     - When $x := krivreq(r)$, pose $k := gamma th ctx.topc$.
       - When $k := kriv.var th i$, by $H_2$, $o_1$ must be $kriv.grab$, which is accessible by (2).
       - When $k := a kriv.cons k'$, by case on $r$.
         - When $r := kriv.var th i$, by $H_2$, $o_1$ must be $kriv.push$ which is accessible by (1).
         - When $r := kriv.lam th a$, then $H_2$ is absurd.
  #v(-1.8em)
]

This concludes the correctness of the #nm[Krivine] language machine! Its NF
strategies from @ch-nf-bisim can be recognized as #nm[Levy]-#nm[Longo]
trees~#mcite(<Levy75>)#mcite(dy: 3em, <Longo83>). Thus, @thm-nf-correctness
gives us a soundness proof of #nm[Levy]-#nm[Longo] tree w.r.t. weak head
observational equivalence, although this fact was already known~#mcite(dy: 3.3em, <Sangiori93>).
This claim should probably be properly justified better, by formalizing a clean
representation of these trees and proving them isomorphic to our NF strategies,
but we will not go further than this.

For the sake of it, let us simply state the normal form bisimulation
correctness theorem, for the last time in this thesis!

#theorem[NF Correctness][
  Define the weak head normalization predicate as follows.

  #let whn = de(cnorm(sym.arrow.double.b))
  #let intp(x) = $de(bracket.double.l) #x de(bracket.double.r)^de("NF")_kriv.kriv$

  $ ar whn cl kriv.conf th (ctx.nilc ctx.conc kriv.sstk) -> base.Prop \
    c whn := (base.fst itree.fmap kriv.eval th c) itree.weq itree.ret th (ctx.topc ctx.cute kriv.grab) $

  For all $t_1, t_2 cl kriv.syn th Gamma th kriv.stm$ such that
  $ intp(krivcfg(t_1[ctx.popc], kriv.var th ctx.topc)) itree.weq intp(krivcfg(t_2[ctx.popc], kriv.var th ctx.topc)), $
  then for all $sigma cl Gamma asgn(kriv.syn) (ctx.nilc ctx.conc kriv.sstk)$ and
  $k cl kriv.syn th (ctx.nilc ctx.conc kriv.sstk) th kriv.sstk$
  $ krivcfg(t_1[sigma], k) whn <-> krivcfg(t_2[sigma],k) whn. $
]
#proof[
  By application of @thm-nf-correctness to $kriv.kriv$, $t_1$, $t_2$ and
  $[sigma,k]$, with hypotheses proven in @lem-kriv-sub, @lem-kriv-resp-sub
  and @lem-kriv-finred, obtain the following.

  $           & base.fst itree.fmap kriv.eval th krivcfg(t_1[ctx.popc], sub.var ctx.topc)[sigma,k] \
    itree.weq & base.fst itree.fmap kriv.eval th krivcfg(t_2[ctx.popc], sub.var ctx.topc)[sigma,k] $

  Conclude by substitution fusion and equivalence.
]

We could further post-process the above theorem to obtain a statement on the
more standard #sym.lambda\-terms and evaluation contexts, as they embed into our
#nm[Krivine] machine syntax. This would clear away our non-standard stack and request
variables, but we will stop our case study at this point.

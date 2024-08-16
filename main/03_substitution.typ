#import "/lib/all.typ": *

= A Categorical Treatment of Substitution

#peio[todo plan chapitre]

== To Type or not to Type, and Other Questions

#peio[rework, trop verbeux]

Without surprise, programming languages and type systems are routinely studied
by type theory practitioners. As such, the concrete matter of how to encode and
work with syntactic terms of an object language inside type theory has been
widely researched, for example in the various submissions to the first
#txsc[PoplMark] challenge~#mcite(<poplmark>). There are two main design points:
how to represent variables and bindings, and how to enforce typing.

The general orientation of my Coq formalization is towards correct-by-construction
programming, that is, enforcing as much invariants as possible inside data
structures using dependent typing. Hence, the natural choice is to use the
_type- and scope-safe_ representation of syntax, also called the _intrinsically
typed and scoped_ representation. Terms are indexed both by their scope (or
typing context) and by their type and form a family $de("Term") cl de("Scope")
-> de("Ty") -> base.Set$. This indexation is used to enforce that only
well-typed terms are represented and that no meaningless variable is used. This
style is known to be hard to scale to complex type systems, in which case the
preferred approach is to keep only intrinsic scoping and to manage typing
extrinsically, using a typing relation on untyped terms. #peio[ref Brady?]
However, as in this thesis I will only consider simply-typed languages, the
simplicity of intrinsic typing and its rich categorical background is much
appreciated.

For further historical background and detailled exposition of
this setting, I refer the interested reader to two comprehensive papers:
the first one by #nm[Allais] et al.~#mcite(dy: -3em, <AllaisACMM21>) and the
second one by #nm[Fiore] and #nm[Szamozvancev]~#mcite(dy: 2em, <FioreS22>),
both coming with beautifully crafted Agda implementations. For design choice
discussion in practical mechanization projects, I can mention #peio[ref jesper
blog, idris talk? metacoq? cocon, elpi?]

An important specificity of the point of view we will adopt in this
chapter, is to be completely silent on the actual construction of the syntax.
Indeed, as our goal is to formalize a (reasonably) language-generic OGS
construction, we will only be interested in _specifying_ what operations a
syntax should support and leave open the choice for actual _instanciation_.
Crucially, we will not assume any kind of induction principle. Surely it can be
debated whether or not something which is not inductively defined diserves to
be called syntax, and indeed our generic OGS construction could very well be
instanciated not by syntax but by some other denotational model of a language.
However, for clarity we will keep using syntactical terminology.

#peio[wip, annonce plan]

This chapter will hence be strictly focused on specifying practical notions for
families supporting variables and substitution. We will start in @sec-sub-ovw
with a quick overview of the state-of-the-art. Next, in @sec-scope we introduce
a small contribution to the intrinsically-scoped approach, loosening the notion
of scope which is typically fixed to singly-linked lists of types. Finally, in
@sec-sub-monoid we will define substitution monoids, i.e., families supporting
variables and substitutions, but also another contribution: substitution
modules. This second notion is motivated by modelling other syntactical
categories than terms, whose variables can be substituted by terms.

== The Theory of Intrinsically-Typed Substitution <sec-sub-ovw>

*Contexts* #sym.space.quad The type- and scope-safe approach starts by defining typing
contexts as lists of types (written backwards, for consistency with the
traditional notation of sequents) and variables as dependently typed #nm[De
Bruijn] indices, i.e., proof-relevant membership witnesses:

$ kw.dat th ctx.ctxc th (T cl base.Set) cl base.Set th kw.whr \
    pat(ctx.nilc cl ctx.ctxc th T,
        ar ctx.conc ar cl ctx.ctxc th T -> T -> ctx.ctxc th T) $

$ kw.dat th ar ctx.varc ar th {T} cl ctx.ctxc th T -> T -> base.Set th kw.whr \
  pat(
    ctx.topc th {Gamma th alpha} cl (Gamma ctx.conc alpha) ctx.varc alpha,
    ctx.popc th {Gamma th alpha th beta} cl Gamma ctx.varc alpha
    -> (Gamma ctx.conc beta) ctx.varc alpha) $

The main category of interest is given by _scoped-and-typed families_ $ctx.ctxc
th T -> T -> base.Set$. Variables are such a family, and this is where we will
try to define terms, or more generally "things supporting substitution".

This is enough to express _assignments_: given a scoped-and-typed family $X$
and two contexts $Gamma, Delta cl ctx.ctxc th T$, an _$X$-assignment from
$Gamma$ to $Delta$_ is a typed mapping from variables in $Gamma$ to elements of
$X$ over $Delta$:

$ Gamma asgn(X) Delta := forall th {alpha} -> Gamma ctx.varc alpha -> X th Delta th alpha. $

Renamings can readily be defined as $ctx.varc$-assignments, i.e., mappings from variables to
variables, turning the set $ctx.ctxc th T$ into a category $ctx.ctxcat th T$.

$ Gamma ctx.ren Delta := Gamma asgn(ctx.varc) Delta $

#remark[
  As contexts are finite, assignements are maps with finite domain, and can
  thus be tabulated and represented as tuples. The tuple representation makes
  intensional equality of assignments better behaved. However as other parts
  of my Coq development already depend on setoids, I will not shy away from
  the setoid of functions with pointwise equality.

  Although it does have this pointwise equality problem, the functional
  representation has other benefits: thanks to #{sym.eta}-equality, functional
  renamings as defined above construct _strict_ category, where all the laws
  hold w.r.t. _definitional_ equality.
]

#remark[
  When computational efficiency is a concern, another typical choice is to
  define a more economic subcategory of contexts, whose renamings consist
  only of order-preserving embeddings (#txsc[ope]). An #txsc[ope] can
  be computationally modelled by a bitvector, where a 0 at position $i$ means
  that $i$-th variable is dropped while 1 means that it is kept. However as
  computational efficiency is not our prime concern, we will not go down this
  route. Still, we keep this idea around, borrowing and slightly abusing the
  notation $ctx.ren$ for renamings, which is traditionally only used for
  embeddings.
]

*Substitution Monoids* #sym.space.quad It is now direct to express that a given
scoped-and-typed family $X$ has variables and substitution. First, variables
must map into $X$. Second, given an element of $X$ over $Gamma$ and an
$X$-assignment from $Gamma$ to $Delta$ we must compute an element of $X$ over
$Delta$. In other words, $X$ must admit maps of the following types.

$ pr("var") th {Gamma th alpha} cl Gamma ctx.varc alpha -> X th Gamma th alpha \
  pr("sub") th {Gamma th Delta th alpha} cl X th Gamma th alpha -> Gamma asgn(X) Delta -> X th Delta th alpha $

This structure is dubbed a _substitution monoid_ and is further subject to the
usual associativity and left and right identity laws of monoids. To see more
clearly how these two maps can be seen as the unit and multiplication maps of a
monoid, notice that the types of these two maps can be refactored as

$ pr("var") cl ar ctx.varc ar ctx.arr X \
  pr("sub") cl X ctx.arr ctxhom(X, X) $

where $ctx.arr$ denotes pointwise maps of scoped-and-typed families and $ctxhom(ar, ar)$ is
the following _internal substitution hom_ functor.

$ ctxhom(X,Y) th Gamma th alpha := forall th {Delta} -> Gamma asgn(X) Delta -> Y th Delta th alpha $

Further note that for any scoped-and-typed family $X$, the functor $ctxhom(X, ar)$ has a
left adjoint $ar ctx.tens X$, the _substitution tensor product_, given by

$ (X ctx.tens Y) th Gamma th alpha := (Delta cl ctx.ctxc th T) times X th Delta th alpha times Delta asgn(Y) Gamma. $

This substitution tensor exhibits scoped-and-typed
families as a _skew monoidal category_ with unit $ctx.varc$ #peio[ref]. By adjointness, the
substitution map could be alternatively be written with the isomorphic type
$ pr("sub") cl X ctx.tens X ctx.arr X. $

As such, although we prefer using the internal substitution hom presentation
which gives a much more easily manipulated _curried_ function type to
substitution, from a mathematical point of view, substitution monoids are
precisely monoid objects in the skew monoidal category $(ctx.ctxc th T -> T ->
base.Set, ctx.varc, ctx.tens)$.

*Renamings* #sym.space.quad Although in this thesis we will not require a
particularly fine treatement of renamings, let us finish this overview of the
state-of-the-art with a notable recent insight on the operation of _renaming_.

In the categorical approach, it seems particularly obvious to formalize that a
family $X cl ctx.ctxc th T -> T -> base.Set$ supports renamings if it is
functorial in the first arguments, i.e., if it is in fact a functor $ctx.ctxcat
th T -> T -> base.Set$. However, the reader might have already noticed that we
prefer working with _families_ instead of _functors_. While all of the above
theory can be recast in the functor category (and has historically started that
way), the substitution hom and tensor on functorial families become quite a bit
more tricky to express inside type theory. Indeed they become respectively ends
and coends, instead of $Pi$ types and $Sigma$ types.

The trick to express functoriality while avoiding functors is to
notice that the faithfull functor $ (ctx.ctxcat th T -> T -> base.Set) ->
(ctx.ctxc th T -> T -> base.Set) $ is comonadic, and its associated comonad is
$square X := ctxhom(ctx.varc, X)$, i.e.,

$ square X th Gamma th alpha := forall {Delta} -> Gamma ctx.ren Delta -> X th Delta th alpha. $

In other words, families supporting renamings, i.e., functors $ctx.ctxcat th T -> T ->
base.Set$ can be equivalently seen as families with a coalgebras structure on
the $square$ comonad #peio[ref]. This means that we can express the operation of
renaming as a map

$ pr("ren") cl X ctx.arr square X. $

Every substitution monoid induces such a comonad structure since renamings can
be implemented by substitution with variables. However the typical
implementation of substitution on a syntax with binders require readily
available $pr("ren")$ and $pr("var")$ operations to go through. This package of
renamings and variables can be formalized as a _pointed coalgebra_ structure
and its compatibily conditions with a substitution monoid structure is
straightforward.


== What is a Variable? Abstracting #nm[De Bruijn] Indices <sec-scope>

While theoretically a sound choice, defining contexts as lists of types and
variables as #nm[De Bruijn] indices is practically unsatisfactory. Perhaps the
most convincing reason is that storing sequences as singly-linked lists and
membership proofs as unary numbers is not computationally efficient. When
executability is a concern, one typically chooses an off-the-shelf finite map
datastructure as e.g. binary trees, which enjoy logarithmic time
lookup and logarithmic size membership proofs.

Although I like to imagine
that my Coq development makes sound computational choices, I must admit that I
have not yet been truly serious about efficiency. But there is a more type-theoretical
objection to lists and #nm[De Bruijn] indices: while all free monoid
constructions are isomorphic (extensionally equal) to lists, there are
situations where some are more practical to manipulate than others.

#[

#let nice = emoji.sparkles
#let snice = nice //text(size: 7pt, nice)
#let cnice = $de(ctx.ctxc^snice)$
#let tnice = $T^snice$
#let tm = $de("Term")$
#let downg = math.class("opening", sym.arrow.b)
#let upg = math.class("opening", sym.arrow.t)

// TODO: remove this when 0.12 is released with color emoji support or fix
// ctheorems which is broken with typst master
#show emoji.sparkles: text(fill: colors.kw, sym.star.filled)

#peio[fix sparkles emoji]
The prime example is the following setting.
#margin-note[
  This situation is not entirely artificial and does in fact appear
  routinely in OGS instances. Indeed, the scopes tracking the shared
  variables of both players are usually restricted to contain only the types of
  some kind of non-transmitted values, typically called _negative types_.
] We have a set of types $T$ and we construct some syntax $tm cl ctx.ctxc th T
-> T -> base.Set$. Now for some reason, we have a subset $ nice cl T ->
base.Prop$ of let's say, _nice_ types, and we need to work with the sub-syntax
of terms in _nice_ contexts, that is in contexts containing only nice types.
Assuming we have worked out the theory of substitution for bare terms, we want
to lift it to the nice setting.

In the framework of lists and #nm[De Bruijn] indices, we must define
nice contexts as lists of pairs of a type together with a proof that it is nice.

$ tnice := (alpha cl T) times nice th alpha \
  cnice th T := ctx.ctxc th tnice $

To lift the syntax into a _nice_ syntax $tm^snice cl cnice th T -> tnice ->
base.Set$, we can define

$ tm^snice th Gamma th alpha := tm th downg Gamma th downg alpha $

where $arrow.b$ is overloaded both as $cnice th T -> ctx.ctxc th T$ and as
$tnice -> T$, _downgrading_ nice things to their underlying bare object.

Assuming the bare syntax supports variables with the operator

$ sub.var cl Gamma ctx.varc alpha -> tm th Gamma th alpha, $

we can lift this to the nice syntax as follows using a suitable downgrade on variables
$Gamma ctx.varc alpha -> downg Gamma ctx.varc downg alpha$.

$ sub.var^snice cl Gamma ctx.varc alpha -> tm^snice th Gamma th alpha \
  sub.var^snice th i := sub.var th downg i $

Now to lift substitution our goal is to define

$ sub.sub^snice cl tm^snice th Gamma th alpha -> Gamma asgn(tm^nice) Delta -> tm^snice th Delta th alpha. $

This is almost but not quite the following instance of our already defined bare
substitution

$ sub.sub cl tm th downg Gamma th downg alpha -> downg Gamma asgn(tm) downg Delta -> tm th downg Delta th downg alpha. $

The culprit is the assignment argument. Spelling out the two types completely, we have
respectively nice assignments

$ {alpha cl tnice} -> Gamma ctx.varc alpha -> tm th downg Delta th downg alpha $

and bare assignments at downgraded contexts

$ {alpha cl T} -> downg Gamma ctx.varc alpha -> tm th downg Delta th alpha. $

One can already feel that things are going south: to downgrade the former into
the latter, we are given a bare type and a membership proof of this type in a
downgraded nice context, and to apply it to the nice assignment we need to
_upgrade_ this into a membership proof of the given type---that was in fact
nice---in the original nice context.
#margin-note[
  Indeed given $Gamma cl cnice th T$ and $alpha cl T$, the following isomorphism holds $ downg Gamma ctx.varc alpha approx (p cl nice th alpha) times Gamma ctx.varc (alpha, p). $
] This is perfectly doable but I will stop
at this point. It is in some way satisfying, but quite exhausting, to play the
upgrade-downgrade yoga on variables which is required to finish the definition
of $sub.sub^snice$, then that of $sub.var^snice$, and finally to prove the
substitution monoid laws (which I have for now only alluded to).

The way out of all this administrative type
shuffling is to notice that our definition of $cnice th T$ completely misses
the point that nice contexts are a subset of contexts, in the sense that it is
a pair of a context together with a proof that it contains only nice types. A
more practical definition in this situation would have been

$ cnice th T := (Gamma cl ctx.ctxc th T) times de("All") th nice th Gamma, $

where the $de("All")$ predicate lifting can be defined as

$ de("All") cl (T -> base.Prop) -> (ctx.ctxc th T -> base.Prop) \
  de("All") th P th Gamma := forall th {alpha} -> Gamma ctx.varc alpha -> P th alpha. $

This makes downgrading nice contexts easier, but the prime benefit of this
change is in the definition variables.

$ ar attach(ctx.varc, tr: snice) ar cl cnice th T -> tnice -> base.Set \
  Gamma attach(ctx.varc, tr: snice) alpha := Gamma .base.fst ctx.varc alpha .base.fst $

As variables now disregard niceness, all of the upgrade-downgrade yoga
disappears. In fact lifting the substitution monoid structure to the nice terms
is now mostly a matter of #{sym.eta}-expanding all the fields, as all of the
work is taken care of by unification.

$ sub.var^snice th i := sub.var th i \
  sub.sub^snice th {Gamma} th x th gamma := sub.sub th x th (kw.fun th {alpha} th i |-> gamma th {alpha, Gamma .base.snd th i} th i) $

]

The moral of this small case study is that although our two definition of nice
contexts are _isomorphic_, they are by no means equivalent in term of ease of
use. Because it is important to build abstractions that people will actually
willingly instanciate in their particular case of interest, I believe it is
important to provide some slack in the concrete definition of contexts and
crucially their notion of variables.


=== Abstract Scopes


/*#definition[Abstract Scope][
  Given a category $cal("A")$ with initial object $bot$ and coproduct $+$, a _abstract scope over
  $cal("A")$_ is given by

  1. a set of _scopes_ $S cl base.Set$,
  2. an _empty scope_ $ctx.emp cl S$,
  3. a _concatenation operation_ $ar ctx.cat ar cl S -> S -> S$, and
  4. a family of variables $ctx.vvar cl S -> cal("A")$,

  such that

  5. $ctx.vvar th ctx.emp approx cop(bot)$, and
  6. $ctx.vvar th (Gamma ctx.cat Delta) approx ctx.vvar th Gamma + ctx.vvar th Delta$.
]

#remark[
  The classical example of typed and scoped syntax for some set of types $T$ is
  given for $cal("A") := T -> base.Set$ by $S := ctx.ctxc th T$ and $ctx.vvar th
  Gamma := Gamma ctx.varc ar$. In this setting, scoped families have the
  usual sort $ctx.ctxc th T -> T -> base.Set$.
]

#remark[
  At this abstract level we also capture the traditional presentation of untyped intrinsically scoped
  syntax with $C := de("Nat")$, $cal("A") := base.Set$ and $ctx.var th n := de("Fin") th n$.
  Here, scoped families have the simpler sort $de("Nat") -> base.Set$.
]
*/

So what is a scope, if not a list? For our purpose very little is needed. We
will only need to know about an empty scope, a concatenation operation on
scopes and a definition for variables. More precisely, given a set of types $T
cl base.Set$, a scope structure on a set $S cl base.Set$ consists of

1. a distinguished _empty scope_ $ctx.emp cl S$,
2. a binary _concatenation_ operation $ar ctx.cat ar cl S -> S -> S$,
3. and a family of _variables_ $ar ctx.var ar cl S -> T -> base.Set$,
4. such that the empty scope has no variable: $ctx.emp ctx.var t approx th base.bot$,
5. and such that the set of variables of a concatenation is the coproduct of the sets
   of variables: $(Gamma ctx.cat Delta) ctx.var t approx (Gamma ctx.var t) base.sum (Delta ctx.var t). $

To formalize the two isomorphisms, I will not take the route of axiomatising
two maps, _forward_ and _backward_, which compose to the identity. First remark
that by initiality of $base.bot$, it suffices to have the forward direction
$ctx.emp ctx.var t -> base.bot$ to obtain the first isomorphism (4) in full.

For the second isomorphism (5), taking hints both from Homotopy Type
Theory~#mcite(<hottbook>, dy: -1.2em, supplement: [§4.4, pp.~136--137]) and
from the _view_ methodology~#mcite(<McBrideM04>, dy: 2.8em, supplement: [§6,
pp.~98--102])~#mcite(<Allais23>, dy: 5.8em), I will axiomatise only the
backward map and ask that its fibers are _contractible_, i.e., inhabited by
exactly one element. This will make the isomorphism far easier to use, enabling
inversions by a simple dependent pattern matching instead of tedious equational
rewriting.

As the domain of the backward map of the second isomorphism has as domain a
sum type, I will axiomatize it implicitely as the copairing of two simpler maps:

$ Gamma ctx.var t -> (Gamma ctx.cat Delta) ctx.var t \
  Delta ctx.var t -> (Gamma ctx.cat Delta) ctx.var t, $

which can be concisely written

$ Gamma ctx.ren (Gamma ctx.cat Delta) \
  Delta ctx.ren (Gamma ctx.cat Delta). $

The fibers of the copairing of two maps can be generally characterized by the
following data type.

$ kw.dat base.vsum th (f cl A -> C) th (g cl B -> C) cl C -> base.Type kw.whr \
    pat(base.vlft th (i cl A) cl base.vsum th (f th i),
        base.vrgt th (j cl B) cl base.vsum th (g th j)) $

#definition[Abstract Scope Structure][
  Given $S,T cl base.Set$, an _abstract scope structure on $S$ with types $T$_
  is given by the following typeclass.
  #margin-note(dy: 2em)[
    Note that in this definition, the set $T$ plays almost no role, being only
    used to form the family category $T -> base.Set$ in the sort of $ctx.var$.
    In future work I believe to be particularly fruitful to replace $T ->
    base.Set$ with an arbitrary suitably well-behaved category $cal("A")$,
    i.e. axiomatising variables as $ar ctx.var cl S -> cal("A")$.

    In particular $cal("A") := base.Set$ provides a more satisfying account of
    untyped calculi than setting $T := base.unit$, i.e. $cal("A") :=
    base.unit -> base.Set$ (as is currently required). In general, it would
    allow much more flexibility in choosing the sort of term families.
  ]

  $ kw.cls ctx.scope_T th S kw.whr \
    pat(
      ctx.emp cl S,
      ar ctx.cat ar cl S -> S -> S,
      ar ctx.var ar cl S -> T -> base.Set,
      ctx.vemp th {t} th (i cl ctx.emp ctx.var t) cl base.bot,
      ctx.rcatl th {Gamma th Delta} cl Gamma ctx.ren (Gamma ctx.cat Delta),
      ctx.rcatr th {Gamma th Delta} cl Delta ctx.ren (Gamma ctx.cat Delta),
      ctx.vcat th {Gamma th Delta th t} th (i cl (Gamma ctx.cat Delta) ctx.var t) cl base.vsum th ctx.rcatl th ctx.rcatr th i,
      ctx.vcatirr th {Gamma th Delta th t} th {i cl (Gamma ctx.cat Delta) ctx.var t} th v cl ctx.vcat th i = v) $

  _Renamings_ $Gamma ctx.ren Delta$ are mutually defined as follows.

  $ ar ctx.ren ar cl S -> S -> base.Set \
    Gamma ctx.ren Delta := forall th {t} -> Gamma ctx.var t -> Delta ctx.var t $
]

#definition[Scope Category][
  A scope structure $ctx.scope_T th S$ defines a _category of
  scopes_ $ctx.ctxcat_S$ whose objects are given by $S$ and whose morphisms are
  given by renamings $Gamma ctx.ren Delta$.
  #margin-note[In other words, $ctx.ctxcat_S$ is the _full image_ of $ar ctx.var$.]
]

This axiomatization of scopes is enough to derive the two isomorphisms describing the
variables of our scope operations:

$ ctx.emp ctx.var t & approx th base.bot \
  (Gamma ctx.cat Delta) ctx.var t & approx (Gamma ctx.var t) base.sum (Delta ctx.var t) $

In particular, this entails that $ctx.rcatl$ and $ctx.rcatr$ are both injective
and have disjoint images. In fact, assuming an abstract scope structure
$ctx.scope_S th T$, the category $ctx.ctxcat_S$ whose objects are elements of
$S$ and whose morphisms are given by renamings, has an initial object $ctx.emp$
and a coproduct structure given by $ctx.cat$.

Before moving on to the theory of scoped-and-typed families and substitution
monoids, we will reap the benefits of this new abstraction and conclude with
some useful instances of abstract scopes.

=== Instances

*Concrete Scopes* #sym.space.quad Lists and #nm[De Bruijn] indices are the
obvious first instance, which we call _concrete scopes_. Concatenation is computed
by induction on the second right-hand context:

$ & ar ctx.catc ar cl ctx.ctxc th T -> ctx.ctxc th T -> ctx.ctxc th T $
#v(-0.5em)
$ & Gamma ctx.catc ctx.nilc & := & Gamma \
  & Gamma ctx.catc (Delta ctx.conc alpha) & := & (Gamma ctx.catc Delta) ctx.conc alpha $

I will not provide the full instanciation of the scope structure, suffice to say that
statements about concatenations are proven by induction on the second context
argument. Notably, proving the subsingleton property of the fibers of the coproduct
injections ($ctx.vcatirr$) requires the use of #nm[Streicher]'s axiom K.

#definition[Concrete Scopes][
  Given $T cl base.Set$, _concrete scopes_ $ctx.ctxc th T$ have an abstract
  scope structure with types $T$ given by the following (incomplete) definition.

  $ //de("CtxScope")_T cl ctx.scope_T th (ctx.ctxc th T) \
    de("CtxScope")_T :=
      pat(ctx.emp         & := ctx.nilc,
          Gamma ctx.cat Delta & := Gamma ctx.catc Delta,
          Gamma ctx.var alpha & := Gamma ctx.varc alpha,
          ...) $
]

*Subset Scopes* #sym.space.quad We can now revisit our introductory example motivating
the introduction of abstract scope structures: _subset scopes_.
Given an abstract scope structure $C cl ctx.scope_T th S$, define the following
predicate lifting.

$ ctx.all_S cl (T -> base.Prop) -> (S -> base.Prop) \
  ctx.all_S th P th Gamma := forall th {alpha} -> Gamma ctx.var alpha -> P th alpha $

We define the subset type of elements of $x$ verifying $P th x$, i.e., the _total
space_ of the predicate $P$ as follows.

$ base.int th {X cl base.Set} cl (X -> base.Prop) -> base.Set \
  base.int P := (x cl X) times P th x $

#definition[Subset Scopes][
  Given an abstract scope instance $ctx.scope_T th S$ and a predicate $P
  cl S -> base.Prop$, _subset scopes_ $base.int (ctx.all_S th P)$ have an
  abstract scope structure with types $base.int P$ given by the following
  (incomplete) definition.

  $ de("SubScope") cl ctx.scope_(base.int P) th base.int (ctx.all_S th P) \
    de("SubScope") := \ pat(
      ctx.emp & :=
        pat(base.fst & := ctx.emp,
            base.snd th i & := kw.case th (ctx.vemp th i) th pat0),
      Gamma ctx.cat Delta & :=
        pat(base.fst := Gamma .base.fst ctx.cat Delta .base.fst,
            base.snd th i := kw.case th (ctx.vcat th i) \
              pat(base.vlft th i &:= Gamma .base.snd th i,
                  base.vrgt th j &:= Delta .base.snd th i)),
      Gamma ctx.var alpha & := Gamma .base.fst ctx.var alpha .base.fst,
      ...) $
]

*Direct Sum of Scopes* #sym.space.quad Another useful instance is the case
where a language is designed with two kinds of variables, i.e., where terms are
indexed by two contexts. We can capture this as the direct sum of abstract
scope structures.

#definition[Direct Sum Scopes][
  Given two abstract scope instances $ctx.scope_(T_1) th S_1$ and
  $ctx.scope_(T_2) th S_2$, _direct sum scopes_ $S_1 base.prod S_2$ have an
  abstract scope structure with types $T_1 base.sum T_2$ given by the following
  (incomplete) definition.

  $ de("SumScope") cl ctx.scope_(T_1 base.sum T_2) th (S_1 base.prod S_2) \
    de("SumScope") := \ pat(
      ctx.emp & := (ctx.emp , ctx.emp),
      Gamma ctx.cat Delta & := (Gamma .base.fst ctx.cat Delta .base.fst, Gamma .base.snd ctx.cat Delta .base.snd),
      Gamma ctx.var base.inj1 th alpha & := Gamma .base.fst ctx.var alpha,
      Gamma ctx.var base.inj2 th alpha & := Gamma .base.snd ctx.var alpha,
      ...) $
]

== Substitution Monoids and Modules <sec-sub-monoid>

Equipped with this new abstraction for scopes, we are ready to continue the theory of
substitution. This will largely follow the now standard approach outlined in @sec-sub-ovw:
we will define scoped families, then assignments, and finally substitution monoids. We will
however introduce one novel contribution: substitution modules.

=== Substitution Monoids

Before defining substitution monoids (families supporting substitution), we first need
to adapt the definition of scoped-and-typed families as well as assignments.

#definition[Scoped-and-Typed Family][
  Given a abstract scope structure $ctx.scope_T th S$, the set of
  _scoped-and-typed families_ is given by the following sort.

  $ ctx.fam1_T th S := S -> T -> base.Set $
]

#definition[Assignments][
  Assuming a scope structure $ctx.scope_T th S$, given a scoped-and-typed
  family $X cl ctx.fam1_T th S$, the set of _$X$-assignments from $Gamma$ to
  $Delta$_ is defined as follows.

  $ ar asgn(X) ar : S -> S -> base.Set \
    Gamma asgn(X) Delta := forall {alpha} -> Gamma ctx.var alpha -> X th Delta th alpha $
]
#remark[
  Since assignments are given by functions, and since we do not want to depend
  on functional extensionality, we will make explicit use of extensional
  equality on assignments. Given $gamma, delta cl Gamma asgn(X) Delta$, it is
  expressed as follows.

  $ gamma approx delta := forall th {alpha} th (i cl Gamma ctx.var alpha) -> gamma th i = delta th i $

  An alternative would be to require that the set of variables in a given context is
  finite, and instead work with _tabulated_ assignments which enjoy a better behaved
  intensional equality when represented inductively.
]

Then, we can construct the substitution hom functor and finally substitution monoids.

#definition[Internal Substitution Hom][
  Assuming a scope structure $ctx.scope_T th S$, the _internal substitution hom_ functor
  is defined as follows.

  $ ctxhom(ar, ar) cl ctx.fam1_T th S -> ctx.fam1_T th S -> ctx.fam1_T th S \
    ctxhom(X, Y) th Gamma th alpha := forall th {Delta} -> Gamma asgn(X) Delta -> Y th Delta th alpha $
]

#definition[Substitution Monoids][
  Assuming a scope structure $ctx.scope_T th S$ and a family $X cl ctx.fam1_T th S$,
  a _substitution monoid_ structure on $X$ is given by the following typeclass.

  #let eqx = math.attach(sym.eq, br: "X")
  $ kw.cls th sub.mon_S th (X cl ctx.fam1_T th S) kw.whr \
    pat(
      sub.var cl ar ctx.var ar ctx.arr X,
      sub.sub cl X ctx.arr ctxhom(X, X),
      sub.sext cl sub.sub xrel(eqx th attach(ctx.arr, tr: rel.r) ctxhom(eqx, eqx)^de(rel.r)) sub.sub,
      //sub.sext cl base.ext th sub.sub,
      sub.idl th {Gamma th alpha} th (x cl X th Gamma th alpha)
        cl sub.sub th x sub.var = x,
      sub.idr th {Gamma th alpha} th (i cl Gamma ctx.var alpha) th (gamma cl Gamma asgn(X) Delta)
        cl sub.sub (sub.var th i) th gamma = gamma th i,
      sub.assoc th {Gamma_1 th Gamma_2 th Gamma_3 th alpha} th (x cl X th Gamma_1 th alpha) \
        quad (gamma cl Gamma_1 asgn(X) Gamma_2) th (delta cl Gamma_2 asgn(X) Gamma_3) \
        quad cl sub.sub (sub.sub th x th gamma) th delta = sub.sub x th (kw.fun th i |-> sub.sub th (gamma th i) th delta)
    ) $
]

To make substitution a bit less wordy we will use the notation $v[gamma] :=
sub.sub th v th gamma$. Moreover, we extend substitution pointwise to assignments with the same
notation, using the context to disambiguate:

$ gamma[delta] := kw.fun th i |-> sub.sub th (gamma th i) th delta. $

For example, using these notations the conclusion of the $sub.assoc$ law can be written
$x[gamma][delta] = x[gamma[delta]]$.

#remark[
  Note that the type of $sub.var$, here written $ar ctx.var ar ctx.arr X$, is
  definitionally equal to the _identity assignment_ type $forall th {Gamma} -> Gamma
  asgn(X) Gamma$.

  This coincidence stems from the fact that substitution monoid structures
  are exactly $ctx.var$-relative monads~#mcite(<AltenkirchCU10>). In this
  perspective, one can construct something similar to a Kleisli category for
  $X$, the _$X$-assignment category_ $de(cal("A"))_X$ whose objects are
  contexts in $S$ and morphisms are given by $X$-assignments. It is then
  unsurprising that $sub.var$---the unit of the relative monad $X$---is the
  identity morphism of it's Kleisli category.
]

#remark[
  As stated previously, to avoid functional extensionality, we need to know
  that every function taking assignments as arguments respects their extensional
  equality. This is the case for $sub.sub$, for which $sub.sext$ is the corresponding
  congruence property. As in the previous chapter, we hide the rather large type
  of $sub.sext$ by liberally using the relational translation of type theory, denoted
  by the superscript $ar^rel.r$. Explicitely, the type of $sub.sext$ unfolds as
  follows.

  $ forall th & {Gamma th alpha} th {x^1 th x^2 cl X th Gamma th alpha} (x^rel.r cl x^1 = x^2) \
              & {Delta} th {gamma^1 th gamma^2 cl Gamma asgn(X) Delta} (gamma^rel.r cl forall th {beta} th (i cl Gamma ctx.var beta) -> gamma_1 th i = gamma_2 th i) \
              & -> x_1 [gamma_1] = x_2[gamma_2] $
]

=== Substitution Modules

#[

#let val = de(cop("Val"))
#let cfg = de(cop("Conf"))
#let ecx = de(cop("EvCtx"))

Substitution monoids have neatly been generalized to abstract scopes, but for
modelling OGS a part of the theory of substitution is still missing. As
motivated in the introductory chapter #peio[ref précise?], in OGS we will
typically see other syntactic constructs such as _values_, _evaluation
contexts_ and _configurations_. Values can be readily represented as a
scoped-and-typed family $ val cl S -> T -> base.Set. $ In contrast, evaluation
contexts are rather represented as a family $ ecx cl S -> T -> T -> base.Set, $
where $E cl ecx th Gamma th alpha th beta$ typically denotes an evaluation
context in scope $Gamma$, with a _hole_ of type $alpha$ and an _outer type_
$beta$. Similarly, configuration have yet a different sort as their judgement
is only indexed by a scope: $ cfg cl S -> base.Set. $

It is clear how to axiomatize that values should support substitution: they should
form a substitution monoid. But for the other two kinds of families, we would like
to axiomatize a substitution operation that allows replacing their variables by
values. More explicitely, we want the following substitution operations.

$ sub.sub th {Gamma th alpha th beta} cl ecx th Gamma th alpha th beta -> Gamma asgn(val) Delta -> ecx th Delta th alpha th beta \
  sub.sub th {Gamma} cl cfg th Gamma -> Gamma asgn(val) Delta -> cfg th Delta $

#let cc = math.cal("C")

As we will see, these two maps can be accounted for by constructing a
_substitution module structure over values_ for $ecx$ and $cfg$. To capture
both kinds of variously indexed families, let us define a _family category_ as
a category of maps $T_1 -> ... -> T_n -> base.Set$ where all $T_i cl base.Set$.

#definition[Generalized Substitution Hom][
  Given an abstract scope structure $ctx.scope_T th S$ and a family category
  $cc$, the _generalized substitution hom_ functor is defined as follows.

  $ ctxhom(ar, ar) cl ctx.fam1_T th S -> (S -> cc) -> (S -> cc) \
    ctxhom(X, Y) th Gamma th alpha_1 th ... th alpha_n := forall th {Delta} -> Gamma asgn(X) Delta -> Y th Delta th alpha_1 th ... th alpha_n $
]

#definition[Substitution Module][
  Given an abstract scope structure $ctx.scope_T th S$, a family category $cc$,
  a substitution monoid $sub.mon_S th M$ and a family $X cl S -> cc$, a
  _substitution module over $M$ on $X$_ is given by the following typeclass.
  #margin-note(dy: 2em)[
    I am slightly sloppy around the $n$-ary binders denoted by "$...$". In the
    current Coq code, I have rather unsatisfyingly special-cased this
    definition for scoped families indexed by 0, 1 or 2 types, which are
    sufficient for our purpose. In further work this precise definition
    could be captured by building upon~#text-cite(<Allais19>)
  ]

  #let eqx = math.attach(sym.eq, br: "X")
  #let eqm = math.attach(sym.eq, br: "M")
  $ kw.cls th sub.mon_S th (X cl ctx.fam1_T th S) kw.whr \
    pat(
      sub.act cl X ctx.arr ctxhom(M, X),
      sub.aext cl sub.act xrel(eqx th attach(ctx.arr, tr: rel.r) ctxhom(eqm, eqx)^de(rel.r)) sub.act,
      sub.aid th {Gamma th alpha_1 th ... th alpha_n} th (x cl X th Gamma th alpha_1 th ... th alpha_n)
        cl sub.act th x sub.var = x,
      sub.acomp th {Gamma_1 th Gamma_2 th Gamma_3 th alpha_1 th ... th alpha_n} th (x cl X th Gamma_1 th alpha_1 th ... th alpha_n) \
        quad (gamma cl Gamma_1 asgn(M) Gamma_2) th (delta cl Gamma_2 asgn(M) Gamma_3) \
        quad cl sub.act (sub.act th x th gamma) th delta = sub.act x th (kw.fun th i |-> sub.sub th (gamma th i) th delta)
    ) $
]

Overloading the notation for the ordinary substitution $sub.sub$, we will write
$x[gamma]$ as a shorthand for $sub.act th x th gamma$.

#remark[
  Although this is irrelevant to our OGS concerns, substitution modules shed a
  new light on the renaming operation. As seen in @sec-sub-ovw the state of
  the art is to axiomatize a family with renamings as a coalgebra for the #box($ctxhom(ctx.var,
  ar "")$) comonad~#mcite(<FioreS22>)#mcite(dy: 3em, <AllaisACMM21>).
  Alternatively, a family with renamings could be presented as a substitution
  module over $ctx.var$ (which trivially forms a substitution monoid). Pulling
  the other way, given a substitution monoid $M$, the functor $ctxhom(M, ar
  "")$ is a comonad and substitution modules over $M$ are nothing else
  than its coalgebras.
]

]

== Patterns and Binding Constructs

We now have enough tools to properly work with all kinds of scoped families
supporting substitution. However a last piece of the syntactic puzzle is
missing for OGS: observations. Together with variables pointing at
opponent-shared _channels_, observations form the content of the messages
exchanged during an OGS play. Observations are typically concretely defined as
a form of _copatterns_~#mcite(<AbelPTS13>), which is just another name for
record projections, i.e. everything we have written in #pr("pink").

Copatterns, like patterns, can be seen as syntactic objects which in particular
use their variables _linearly_. However, an intrinsically typed and scoped
account of linearity is a complex topic of its own (see e.g. #mcite(<WoodA20>))
so we will rather adopt a much simpler point of view in which (co)patterns are
understood as syntactic objects where all variables are fresh. Since a virtue
of the #nm[DeBruijn] indices approach is to eschew any representation of fresh
variables, keeping only bound or free variables, there is no use to index their
sort by an ambiant context. Instead, given a particular (co)pattern, we should
be able to compute its set of _holes_, or _binders_: a context listing the types
of its nameless fresh variables. This leads us to the following definition.

#definition[Binding Family][
  Given an abstract scope structure $ctx.fam1_T th S$, a _binding family_ is
  given by a record of the following type.
  #peio[wip]
]

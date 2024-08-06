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

$ & kw.dat th ctx.ctxc th (T cl base.Set) cl base.Set th kw.whr \
  & quad ctx.nilc cl ctx.ctxc th T \
  & quad ar ctx.conc ar cl ctx.ctxc th T -> T -> ctx.ctxc th T $

$ & kw.dat th ar ctx.varc ar th {T} cl ctx.ctxc th T -> T -> base.Set th kw.whr \
  & quad ctx.topc th {Gamma th alpha} cl (Gamma ctx.conc alpha) ctx.varc alpha \
  & quad ctx.popc th {Gamma th alpha th beta} cl Gamma ctx.varc alpha -> (Gamma ctx.conc beta) ctx.varc alpha $

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
  representation has other benefits: thanks to $eta$ equality, functional
  renamings as defined above construct _strict_ category, where all the laws
  hold w.r.t. _definitional_ equality.
]

#remark[
  When computational efficiency is a concern, another typical choice is to
  define a more economic subcategory of contexts, whose renamings consist
  only of order-preserving embeddings (#txsc[Ope]). An #txsc[Ope] can
  be computationally modelled by a bitvector, where a 0 at position $i$ means
  that $i$-th variable is dropped while 1 means that it is kept. However as
  computational efficiency is not our prime concern, we will not go down this
  route. Still, we keep this idea around, borrowing and slightly abusing the
  notation $ctx.ren$ for renamings, which is traditionally only used for
  embeddings.
]

*Substitution Monoids* #sym.space.quad It is now direct to express that a given scoped-and-typed family $X$ has
variables and substitution. First, variables must map into $X$. Second, given
an element of $X$ over $Gamma$ and an $X$-assignment from $Gamma$ to $Delta$ we
must compute an element of $X$ over $Delta$. In other words, $X$ must admit
maps of the following types.

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

This substitution tensor with unit $ctx.varc$ exhibits scoped-and-typed
families as a _skew monoidal category_ #peio[ref]. By adjointness, the
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
way), the substitution hom and tensor become quite a bit more tricky to express
inside type theory. Indeed they become respectively ends and coends, instead of
$Pi$ types and $Sigma$ types as we have done in families.

The trick to express functoriality while avoiding functors is to
notice that the faithfull functor $ (ctx.ctxcat th T -> T -> base.Set) ->
(ctx.ctxc th T -> T -> base.Set) $ is comonadic, and its associated comonad is
$square X := ctxhom(ar ctx.varc ar, X)$, i.e.,

$ square X th Gamma th alpha := forall {Delta} -> Gamma ctx.ren Delta -> X th Delta th alpha. $

Hence, families supporting renamings, i.e., functors $ctx.ctxcat th T -> T ->
base.Set$ can be equivalently seen as families with a coalgebras structure on
the $square$ comonad #peio[ref]. In other words, we can express the operation of
renaming as a map

$ pr("ren") cl X ctx.arr square X. $

Every substitution monoid induces such a comonad structure, as renamings can be
implemented by substitution with variables. However the typical implementation
of substitution on a syntax with binders require readily available $pr("ren")$
and $pr("var")$ operations. This package can be formalized as _pointed
coalgebras_ and their compatibily conditions with a substitution monoid
structure is straightforward.


== What is a Variable? Abstracting #nm[De Bruijn] Indices <sec-scope>

While theoretically a sound choice, defining contexts as lists of types and
variables as #nm[De Bruijn] indices is practically unsatisfactory. Perhaps the
most convincing reason is that storing sequences as singly-linked lists and
membership proofs as unary numbers is not computationally efficient. When
executability is a concern, one typically chooses an off-the-shelf finite map
datastructure such as hash-tables or binary trees, which enjoy logarithmic time
lookup and logarithmic size membership proofs. However, while I like to imagine
that my Coq development makes sound computational choices, I must admit that I
have not yet been truly serious about efficiency. But there is a more type-theoretical
objection to lists and #nm[De Bruijn] indices: while all free monoid
constructions are isomorphic (extensionally equal) to lists, there are
situations where some are more practical to manipulate than others.

The prime example is the following setting. We have a set of types $T$ and
construct some syntax $de("Term") cl ctx.ctxc th T -> T -> base.Set$. Now for
some reason, we have a subset $S cl T -> base.Prop$ of let's say, _nice_
types, and we need to work with the sub-syntax of terms in _nice_ contexts,
that is in contexts where all types verify $S$. The framework of lists and #nm[De
Bruijn] indices readily applies to this case, by setting $T' := (alpha cl T)
times S th alpha$ and working with $ctx.ctxc th T'$, i.e.,

$ de(C_1) := ctx.ctxc th ((alpha cl T) times S th alpha). $

However, this completely misses the point that nice contexts are a subset of
contexts, in the sense that they have the same computational content. Indeed,
the arguably more idiomatic definition in this case would be

$ de(C_2) := (Gamma cl ctx.ctxc th T) times de("All") th S th Gamma, $

where the $de("All")$ predicate can be defined as

$ de("All") cl (T -> base.Prop) -> (ctx.ctxc th T -> base.Prop) \
  de("All") th S th Gamma := forall th {alpha} -> Gamma ctx.varc alpha -> S th alpha. $

The crucial difference between the two definition is in their notion of
variable. With the refined definition $de(C_2)$, a variable of a nice type
$alpha$ in a nice context $Gamma$ is exactly given by a variable of the
underlying type in the underlying context $Gamma ctx.varc alpha$, forgetting
altogether about niceness. In contrast, with the original rigid definition
$de(C_1)$ a variable is a membership proof of $alpha$ _as nice type_ in $Gamma$
_as a list of nice types_. This second membership proof is complicated by the presence
of the niceness witnesses, hindering flexible promotion and demotion of a given
variable between the setting where we consider niceness and the setting where
we do not.

The above situation is not entirely artificial and does in fact appear
routinely in OGS instances. Indeed, the scopes tracking the shared variables of
both players are usually restricted to contain only some kind of types,
typically called _negative types_. In these settings one first constructs the
usual syntax of the calculus, with unrestricted contexts and types, providing
its substitution operator and the usual meta-theory. Subsequently, when
constructing the OGS instance, one needs to restrict this substitution operator
to negative contexts and negative types. This involves juggling between
"negative variables" of negative type in some negative context and "usual
variables" of the underlying type in the underlying context. In particular,
round-tripping a variable from the "negative" notion, to the "underlying usual"
notion and back is not trivial if one uses the naive encoding. In contrast with
the idiomatic encoding, this kind of round-trip is _definitionally_ the
identity, greatly simplifying (in fact making
largely trivial) the restriction of the substitution operator.

#peio[Plus de def, moins de blabla? En particulier dernier paragraphe.]


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

So what is a scope, if not a list? For our purpose, we will only need to know
about an empty scope, a concatenation operation on scopes and a definition for
variables. More precisely, given a set of types $T cl base.Set$, a set $S cl
base.Set$ hase a scope structure if it has

1. a distinguished _empty scope_ $ctx.emp cl S$,
2. a binary _concatenation_ operation $ar ctx.cat ar cl S -> S -> S$,
3. and a family of _variables_ $ar ctx.var ar cl S -> T -> base.Set$.

Moreover we require that the empty scope has no variable, i.e.,
$ ctx.emp ctx.var t approx th base.bot, $
and that the set of variables of a concatenation is the coproduct of the sets
of variables, i.e.,
$ (Gamma ctx.cat Delta) ctx.var t approx (Gamma ctx.var t) base.sum (Delta ctx.var t). $

#remark[
  To formalize these two isomorphisms, I will not take the route of
  axiomatising two maps, _forward_ and _backward_, which compose to the
  identity. Instead, taking hints both from Homotopy Type Theory #peio[ref
  hottbook] and from the _view_ methodology #peio[ref view from the left;
  Dagand? Allais?], I will axiomatise a single map whose fibers are
  contractible, i.e., inhabited by exactly one element. This will make the
  isomorphism far easier to use, enabling simple inversions by dependent
  pattern matching instead of tedious equational rewriting. More precisely,
  for mostly stylistic reasons I will not take the usual definition of $X$
  being a "contractible type" to be $ (a cl X) times ((b cl X) -> a = b) $
  but rather the equivalent notion of "pointed sub-singleton" $ (x cl X)
  times ((a th b cl X) -> a = b). $
]

The definition of abstract scope structure will thus involve two steps: first
axiomatising the operations, the variables and the backward maps of the
isomorphism and second, characterizing the fibers of the backward maps and
axiomatising their contractibility. The first backward map has as domain
$base.bot$, as such it is trivial and we do not need to axiomatise it. The
second has as codomain a sum type, so we axiomatise it implicitely as
the copairing of two maps.

#definition[Abstract Pre-Scope Structure][
  Let $S,T cl base.Set$. An _abstract pre-scope structure on $S$ with types $T$_
  is given by a record of the following type.

  $ kw.cls ctx.prescope_T th S kw.whr \
    quad ctx.emp cl S \
    quad ar ctx.cat ar cl S -> S -> S \
    quad ar ctx.var ar cl S -> T -> base.Set \
    quad ctx.rcatl th {Gamma th Delta} cl Gamma ctx.ren (Gamma ctx.cat Delta) \
    quad ctx.rcatr th {Gamma th Delta} cl Delta ctx.ren (Gamma ctx.cat Delta) $

  Where _renamings_ $Gamma ctx.ren Delta$ are defined as follows.

  $ ar ctx.ren ar cl S -> S -> base.Set \
    Gamma ctx.ren Delta := forall th {t} -> Gamma ctx.var t -> Delta ctx.var t $
]

#definition[Abstract Scope Structure][
  Let $S,T cl base.Set$. Assuming an abstract pre-scope structure $ctx.prescope_T th S$,
  define the following proof-relevant predicate, characterizing the fibers of the copairing of
  $ctx.rcatl$ and $ctx.rcatr$.

  $ kw.dat ctx.catV th {Gamma th Delta th t} cl (Gamma ctx.cat Delta) ctx.var t -> base.Type kw.whr \
    quad ctx.vcatl th (i cl Gamma ctx.var t) cl ctx.catV th (ctx.rcatl th i) \
    quad ctx.vcatr th (j cl Delta ctx.var t) cl ctx.catV th (ctx.rcatr th j) $

  An _abstract scope structure on $S$ with types $T$_ is given by a record of the
  following type.

  $ kw.cls ctx.scope_T th S kw.whr \
    quad kw.ext th ctx.prescope_t th S \
    quad ctx.vemp th {t} th (i cl ctx.emp ctx.var t) cl base.bot \
    quad ctx.vcat th {Gamma th Delta th t} th (i cl (Gamma ctx.cat Delta) ctx.var t) cl ctx.catV th i \
    quad ctx.vcatirr th {Gamma th Delta th t th i} th (v_1 th v_2 cl ctx.catV th {Gamma} th {Delta} th {t} th i) cl v_1 = v_2 \
    $
]

#peio[wip]

/*
#let cc = "C"
#let cxx = de(math.cal(math.bold("C")))
#let aa = math.cal(math.bold("A"))

At this abstract level, given $aa$ a sufficiently well-behaved category, a
notion of scopes is given by a set $cc cl base.Set$, and

The category of contexts $cxx$ is then defined to be the full image of
$ctx.var$: its object are elements of $C$ and maps $cxx[Gamma,Delta]$ are given
by _renamings_ $aa[ctx.var th Gamma, ctx.var th Delta]$.

#let tt = de(cop("Tm"))
In this setting, _scoped families_ of sort $C -> aa$ can then be used to model
terms or other syntactic categories. Given such a family $tt$, we can generalize
renamings into _assignments_, mapping variables in $Gamma$ not to variables in $Delta$
but to $tt$-terms over $Delta$, written as

$ Gamma asgn(tt) Delta := aa[ctx.var th Gamma, tt th Delta]. $
*/


=== Instances

*Subset Scopes* #sym.space.quad blabla

*Direct Sum of Scopes* #sym.space.quad  blabla

== Substitution Monoids and Modules <sec-sub-monoid>

=== Assignments

=== Substitution Tensor and Internal Hom

=== Substitution Monoids

=== Substitution Modules

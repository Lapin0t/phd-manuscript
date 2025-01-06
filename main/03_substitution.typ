#import "/lib/all.typ": *

= A Categorical Treatment of Substitution <ch-subst>

Our generic OGS construction depends mainly on two broad technical fields:
games and programming language syntax. Since we clarified games in the previous
chapter, it is now left to provide the same technical grounding for syntax.
While syntax might seem like already well-known, the details of working
formally with syntactic objects are more subtle than they seem.

Being close topics, programming languages and type systems are routinely
studied by type theory practitioners. As such, the concrete matter of how to
encode and work with syntactic terms of an object language inside type theory
has been widely researched, for example in the various submissions to the first
#txsc[PoplMark] challenge~#mcite(<poplmark>). There are two main design points:
how to represent variables and bindings, and how to enforce typing. My
inclination towards correct-by-construction programming, that is, enforcing as
much invariants as possible inside data structures using dependent typing, makes
it a natural choice to use the _type- and scope-safe_, or _intrinsically
typed and scoped_ representation of syntax. Quoting #nm[Fiore] and
#nm[Szamozvancev]~#mcite(<FioreS22>),

#block(inset: 1em)[
  "We believe that the nameless, intrinsic representation is hard to surpass in
  dependently-typed proof assistants thanks to its static guarantees on the
  typing and scoping of terms."
]


In this setting, the sort of terms is indexed both by a scope (or typing
context) and by a type, so as to form a family $de("Term") cl de("Scope") ->
de("Ty") -> base.Type$. This indexing may then be used to enforce that only
well-typed terms are represented and that all the mentioned variables are in scope.

An important specificity of the point of view we will adopt in this
chapter is to be completely silent on the actual construction of the syntax.
Indeed, as our goal is to formalize a (reasonably) language-generic OGS
construction, we will only be interested in _specifying_ what operations a
syntax should support and leave open the choice for actual _instantiation_.
Crucially, we will not assume any kind of induction principle and keep the
syntax opaque. Surely it can be debated whether or not something which is not
inductively defined deserves to be called a syntax, and indeed our generic OGS
construction could very well be instantiated not by syntax but by some other
denotational model of a language. However, for clarity, we will keep using
syntactic terminology.

We start in @sec-sub-ovw with a short informal overview of the core points of
the intrinsic representation and the axiomatization of substitution. This
overview largely follows two comprehensive papers with beautifully crafted Agda
implementations which I heartily recommend reading~#mcite(dy: -1em,
    <FioreS22>)#mcite(dy: 2em, <AllaisACMM21>). The main point is the
introduction of _substitution monoids_, which axiomatize type- and
scope-indexed families supporting variables and substitutions. In
@sec-sub-scope, we motivate and introduce a small contribution. In typical type
theory formalizations, the notion of scope is fixed in the abstract theory of
substitution and defined as lists of types, but this rigidity can be cumbersome
for some languages. This is remedied by providing a simple abstraction for
scopes. Finally, in @sec-sub-monoid, we adapt the definition of substitution
monoid to this new abstraction. We also present _substitution modules_, a
notion required to deal with syntactic objects which have a substitution
operation, but whose arguments may be of a different kind, such as evaluation
contexts, whose variables can be substituted by values.
Substitution module have already been studied~#mcite(<HirschowitzM10>), but
they are rarely presented even though they become necessary quite quickly in
lots of concrete examples.

== The Theory of Intrinsically-Typed Substitution <sec-sub-ovw>

#remark[
  The following section will consist in an informal overview. As such every
  introduced notion will be properly defined later on.
]

*Contexts* #sym.space.quad The type- and scope-safe approach starts by defining
typing contexts as lists of types (written backwards, for consistency with the
traditional notation of sequents) and variables as dependently typed #nm[De
Bruijn] indices, in other words, proof-relevant membership witnesses:

$ kw.dat th ctx.ctxc th (T cl base.Type) cl base.Type th kw.whr \
    pat(ctx.nilc cl ctx.ctxc th T,
        ar ctx.conc ar cl ctx.ctxc th T -> T -> ctx.ctxc th T) $

$ kw.dat th ar""cnorm(ctx.varc)ar th {T} cl ctx.ctxc th T -> T -> base.Type th kw.whr \
  pat(
    ctx.topc th {Gamma th alpha} cl (Gamma ctx.conc alpha) ctx.varc alpha,
    ctx.popc th {Gamma th alpha th beta} cl Gamma ctx.varc alpha
    -> (Gamma ctx.conc beta) ctx.varc alpha) $

The main category of interest for syntactic objects is given by _scoped-and-typed
families_ $ctx.ctxc th T -> T -> base.Type$. Variables given by $ar""cnorm(ctx.varc)ar$ are already such a
family, but so too will be terms, and more generally "things
by which variables can be substituted".

Next, renamings are defined as type-preserving mappings from variables in
one context to variables in another, turning the set $ctx.ctxc th T$ into the
category $ctx.ctxcat th T$. Instead of just variables, the codomain of these
renamings can be generalized to any scoped-and-typed family $X$, yielding the
notion of assignment. More precisely, given two contexts $Gamma, Delta cl
ctx.ctxc th T$, an _$X$-assignment from $Gamma$ to $Delta$_ is a type-preserving
mapping from variables over $Gamma$ to $X$-terms over $Delta$.

$ Gamma asgn(X) Delta := forall th {alpha} -> Gamma ctx.varc alpha -> X th Delta th alpha \
  Gamma ctx.ren Delta := Gamma asgn(ctx.varc) Delta $

#remark[
  As contexts are finite, assignments are maps with finite domain, and may
  thus be tabulated and represented as tuples. The tuple representation makes
  intensional equality of assignments better behaved. However as other parts
  of my Rocq development already depend on extensional equality, I will not shy away from
  the pointwise extensional equality of functions.

  Although it does have this issue, the representation of assignments as functions
  has other benefits. Thanks to the #{sym.eta}-law
  renamings as defined above construct a _strict_ category, where all the laws
  hold w.r.t. _definitional_ equality. This would be lost when working
  with tabulated representations.
]

#remark[
  When computational efficiency is a concern, another typical choice is to
  define a more economic subcategory of contexts, whose renamings consist
  only of order-preserving embeddings (#txsc[Ope]). An #txsc[Ope] can
  be computationally modeled by a bitvector, where a 0 at position $i$ means
  that the $i$-th variable is dropped while 1 means that it is kept. However as
  computational efficiency is not our prime concern, we will not go down this
  route. Still, we keep this idea around, borrowing and slightly abusing the
  notation $ctx.ren$ for renamings, which is traditionally associated with
  embeddings.
]

*Substitution Monoids* #sym.space.quad It is now direct to express that a given
scoped-and-typed family $X$ has variables and substitution. First, variables
must map into $X$. Second, given an $X$-term over $Gamma$ and an
$X$-assignment from $Gamma$ to $Delta$, substitution should return some $X$-term over
$Delta$. In other words, $X$ must admit maps of the following types.

$ pr("var") th {Gamma th alpha} cl Gamma ctx.varc alpha -> X th Gamma th alpha \
  pr("sub") th {Gamma th Delta th alpha} cl X th Gamma th alpha -> (Gamma asgn(X) Delta) -> X th Delta th alpha $

This structure is dubbed a _substitution monoid_~#mcite(<FioreS22>)
and is further subject to the usual associativity and left
and right identity laws.

$ sub.sub th (sub.var th i) th gamma & = gamma th i \
  sub.sub th x th sub.var & = x \
  sub.sub th (sub.sub th x th gamma) th delta & = sub.sub th x th (kw.fun th i |-> sub.sub th (gamma th i) th delta)
  $

To explain how these two maps can be seen as the unit and
multiplication maps of a monoid, notice that their types
may be refactored as

$ pr("var") cl ar ctx.varc ar ctx.arr X \
  pr("sub") cl X ctx.arr ctxhom(X, X) $

where $ctxhom("" ar "", ar "")$ is the following _internal substitution hom_ functor~#mcite(<FioreS22>).

$ ctxhom(X,Y) th Gamma th alpha := forall th {Delta} -> Gamma asgn(X) Delta -> Y th Delta th alpha $

Further note that for any scoped-and-typed family $X$, the functor $ctxhom(X, ar "")$ has a
left adjoint $ar ctx.tens X$, the _substitution tensor product_~#num-cite(<FioreS22>), given by

$ (X ctx.tens Y) th Gamma th alpha := (Delta cl ctx.ctxc th T) times X th Delta th alpha times Delta asgn(Y) Gamma. $

This substitution tensor exhibits scoped-and-typed families as a _skew monoidal
category_~#mcite(dy: -1em,<AltenkirchCU10>)#mcite(dy: 2em,<Szlachanyi>) with unit $ctx.varc$.
Being _skew_ monoidal is slightly weaker than monoidal, as the left and right
unit laws as well as associativity laws on the tensor product are not true
w.r.t. isomorphisms, but w.r.t. morphisms in one direction. By
adjointness, the substitution map could be alternatively written with the
isomorphic type $ pr("sub") cl X ctx.tens X ctx.arr X. $

Thus, although we prefer using the internal substitution hom presentation
which gives a much more easily manipulated _curried_ function type to
substitution, from a mathematical point of view, substitution monoids are
precisely monoid objects in the skew monoidal category $(ctx.ctxc th T -> T ->
base.Type, ctx.varc, ctx.tens)$.

*Renamings* #sym.space.quad Let us finish this overview of the state of the art
with a notable recent insight on the type-theoretical presentation of the
operation of _renaming_.

In the categorical approach, it seems particularly obvious to formalize that a
family $X cl ctx.ctxc th T -> T -> base.Type$ supports renamings if it is
functorial in the first argument, i.e., if it extends to a functor $ctx.ctxcat th T ->
T -> base.Type$. In fact, as is customary in category-theoretic
presentations, all of the above theory can be recast in the functor category,
entirely eliminating families _not_ supporting renamings. However, as shown by
folklore practice in the dependently-typed community, and stressed by
#nm[Fiore] and #nm[Szamozvancev]~#mcite(<FioreS22>), working solely in the
functor category is problematic as it crucially requires to work with quotients.
Essentially, the reason is that when constructing the syntax, one can _implement_
renamings by induction on terms. This implementation does not appeal to the
automatic renaming operation that exists by virtue of working only with functors.
As such, we are left with two renaming operations, and quotients are necessary to
make sure they coincide.

The trick to provide a theoretical account of the renaming operation while
avoiding functors is to notice that the faithful functor $ (ctx.ctxcat th T ->
T -> base.Type) -> (ctx.ctxc th T -> T -> base.Type) $ is comonadic, with
associated comonad given by $square X := ctxhom(ctx.varc, X)$, i.e.,

$ square X th Gamma th alpha := forall {Delta} -> (Gamma ctx.ren Delta) -> X th Delta th alpha. $

In plain words, families supporting renamings, i.e., functors $ctx.ctxcat th T
-> T -> base.Type$ can be equivalently seen as families with a $square$-coalgebra
structure~#mcite(<AllaisACMM21>)#num-cite(<FioreS22>). This coalgebra structure
exactly gives the renaming map, expressing it as

$ pr("ren") cl X ctx.arr square X. $

This is obviously an after-the-fact theoretical reconstruction of the familiar
operation of renaming and indeed matches the obvious type

$ pr("ren") th {Gamma th Delta th alpha} cl X th Gamma th alpha -> Gamma ctx.ren Delta -> X th Delta th alpha. $

Every substitution monoid induces such a renaming coalgebra structure since
renamings can be implemented by substitution with variables. However, the
typical implementation of substitution on a syntax with binders requires
readily available $pr("ren")$ and $pr("var")$ operations to allow substitution
to go under binders. This package of renamings and variables can be formalized as a
_pointed coalgebra structure_~#mcite(<FioreS22>) and its compatibility
conditions with a substitution monoid structure are straightforward.

== What is a Variable? Abstracting #nm[De Bruijn] Indices <sec-sub-scope>

While theoretically a sound choice, defining contexts as lists of types and
variables as #nm[De Bruijn] indices is practically unsatisfactory. Perhaps the
most convincing reason is that storing sequences as singly-linked lists and
membership proofs as unary numbers is not computationally efficient. When
efficient execution is a concern, one typically chooses an off-the-shelf finite
map data structure such as binary trees, which enjoy logarithmic time lookup and
logarithmic size membership proofs.

Although I like to imagine that my Coq development makes sound computational
choices, I must admit that I have not yet been truly serious about efficiency.
But there is a more type-theoretical objection to lists and #nm[De Bruijn]
indices: while all free monoid constructions are isomorphic (extensionally
equal) to lists, there are situations where some are much more practical to
manipulate than others.

#[

//#let nice = emoji.sparkles
#let nice = image("/images/sparkle.svg", height: 0.8em)
#let snice = nice //text(size: 7pt, nice)
#let cnice = $de(ctx.ctxc^snice)$
#let tnice = $T^snice$
#let tm = $de("Term")$
#let downg = math.class("opening", sym.arrow.b)
#let upg = math.class("opening", sym.arrow.t)

// TODO: remove this when 0.12 is released with color emoji support or fix
// ctheorems which is broken with typst master
//#show emoji.sparkles: text(fill: colors.kw, sym.star.filled)

The prime example is the following setting#margin-note(mark: true, dy: -4.5em)[
  This situation is not entirely artificial and does in fact appear
  routinely in OGS instances. Indeed, the scopes tracking the shared
  variables of both players are usually restricted to contain only the types of
  some kind of non-transmitted values, typically called _negative types_.
]. We have a set of types $T$ and we construct some syntax $tm cl ctx.ctxc th T
-> T -> base.Type$. Now for some reason, we have a subset $ nice cl T ->
base.Prop$ of let's say, _nice_ types, and we need to work with the sub-syntax
of terms in _nice_ contexts, that is in contexts containing only nice types.
Assuming we have worked out the theory of substitution for bare terms, we want
to lift it to the nice setting.

In the framework of lists and #nm[De Bruijn] indices, we must define
nice contexts as lists of pairs of a type together with a proof that it is nice:

$ tnice := (alpha cl T) times nice th alpha \
  cnice th T := ctx.ctxc th tnice $

To lift the syntax into a _nice_ syntax $tm^snice cl cnice th T -> tnice ->
base.Type$, we set

$ tm^snice th Gamma th alpha := tm th downg Gamma th downg alpha $

where $arrow.b$ is overloaded both as $cnice th T -> ctx.ctxc th T$ and as
$tnice -> T$, _downgrading_ nice things to their underlying bare object.

Assuming the bare syntax supports variables with the operator

$ sub.var cl Gamma ctx.varc alpha -> tm th Gamma th alpha, $

we can lift it to the nice syntax as follows using a suitable downgrade on variables,
of type $Gamma ctx.varc alpha -> downg Gamma ctx.varc downg alpha$.

$ sub.var^snice cl Gamma ctx.varc alpha -> tm^snice th Gamma th alpha \
  sub.var^snice th i := sub.var th downg i $

Now to lift substitution our goal is to define

$ sub.sub^snice cl tm^snice th Gamma th alpha -> Gamma asgn(tm^nice) Delta -> tm^snice th Delta th alpha. $

This is almost but not quite the following instance of our already defined bare
substitution

$ sub.sub cl tm th downg Gamma th downg alpha -> downg Gamma asgn(tm) downg Delta -> tm th downg Delta th downg alpha. $

The culprit is the assignment argument. Spelling out the two assignment types
completely, we have respectively nice assignments of sort

$ {alpha cl tnice} -> Gamma ctx.varc alpha -> tm th downg Delta th downg alpha $

and bare assignments at downgraded contexts of sort

$ {alpha cl T} -> downg Gamma ctx.varc alpha -> tm th downg Delta th alpha. $

One can already feel that things are going south: to downgrade the former into
the latter, we are given a bare type $alpha$ and a membership proof in a
downgraded nice context $i cl downg Gamma ctx.varc alpha$, and to apply it to
the nice assignment we need to _upgrade_ this into a niceness witness
$p cl nice th alpha$ and a membership proof in the original nice context $Gamma
ctx.varc (alpha, p)$.
This is perfectly doable as indeed the following isomorphism holds

$ downg Gamma ctx.varc alpha approx (p cl nice th alpha) times Gamma ctx.varc (alpha, p), $

but I will stop at this
point. It is in some way satisfying, but quite exhausting, to play the
upgrade-downgrade yoga on variables which is required to finish the definition
of $sub.sub^snice$, and then to prove the substitution monoid laws (which I
have for now only alluded to).

The way out of all this administrative type
shuffling is to notice that our definition of $cnice th T$ completely misses
the point that nice contexts are a subset of contexts. Indeed a more practical
definition in this situation would have been as pairs of a context together
with a proof that it contains only nice types.

$ cnice th T := (Gamma cl ctx.ctxc th T) times de("All") th nice th Gamma, $

where the $de("All")$ predicate lifting can be defined as

$ de("All") cl (T -> base.Prop) -> (ctx.ctxc th T -> base.Prop) \
  de("All") th P th Gamma := forall th {alpha} -> Gamma ctx.varc alpha -> P th alpha. $

This makes downgrading nice contexts easier, but the prime benefit of this
change is in the definition variables.

$ ar attach(ctx.varc, tr: snice) ar cl cnice th T -> tnice -> base.Type \
  Gamma attach(ctx.varc, tr: snice) alpha := Gamma .base.fst ctx.varc alpha .base.fst $

As variables now disregard niceness, all of the upgrade-downgrade yoga
vanishes. In fact lifting the substitution monoid structure to the nice terms
is now mostly a matter of #{sym.eta}-expanding all the fields, and the hard
work is taken care of by unification.

$ sub.var^snice th i & := sub.var th i \
  sub.sub^snice th {Gamma} th x th gamma & := sub.sub th x th (kw.fun th {alpha} th i |-> gamma th {alpha, Gamma .base.snd th i} th i) $

]

The conclusion of this small case study is that although our two definitions of
nice contexts are _isomorphic_, they are by no means equivalent in term of ease
of use. Because I believe it is important to build abstractions that people will actually
willingly instantiate in their particular case of interest, it becomes
necessary to provide some breathing room in the concrete definition of contexts and
crucially in their notion of variables.

=== Abstract Scopes


/*#definition[Abstract Scope][
  Given a category $cal("A")$ with initial object $bot$ and coproduct $+$, a _abstract scope over
  $cal("A")$_ is given by

  1. a set of _scopes_ $S cl base.Type$,
  2. an _empty scope_ $ctx.emp cl S$,
  3. a _concatenation operation_ $ar ctx.cat ar cl S -> S -> S$, and
  4. a family of variables $ctx.vvar cl S -> cal("A")$,

  such that

  5. $ctx.vvar th ctx.emp approx cop(bot)$, and
  6. $ctx.vvar th (Gamma ctx.cat Delta) approx ctx.vvar th Gamma + ctx.vvar th Delta$.
]

#remark[
  The classical example of typed and scoped syntax for some set of types $T$ is
  given for $cal("A") := T -> base.Type$ by $S := ctx.ctxc th T$ and $ctx.vvar th
  Gamma := Gamma ctx.varc ar$. In this setting, scoped families have the
  usual sort $ctx.ctxc th T -> T -> base.Type$.
]

#remark[
  At this abstract level we also capture the traditional presentation of untyped intrinsically scoped
  syntax with $C := de("Nat")$, $cal("A") := base.Type$ and $ctx.var th n := de("Fin") th n$.
  Here, scoped families have the simpler sort $de("Nat") -> base.Type$.
]
*/

So what is a scope, if not a list? For our purpose very little is needed. We
will only need to know about an empty scope, a concatenation operation on
scopes and a definition for variables. More precisely, given a set of object
language types $T cl base.Type$, a scope structure on a set $S cl base.Type$
consists of

1. a distinguished _empty scope_ $ctx.emp cl S$,
2. a binary _concatenation_ operation $ar ctx.cat ar cl S -> S -> S$,
3. and a family of _variables_ $ar ctx.var ar cl S -> T -> base.Type$,
4. such that the empty scope has no variable: $ctx.emp ctx.var t approx th base.bot$,
5. and such that the set of variables of a concatenation is the coproduct of the sets
   of variables: $(Gamma ctx.cat Delta) ctx.var t approx (Gamma ctx.var t) base.sum (Delta ctx.var t). $
#margin-note(dy: -8em)[
  Notice that we do not ask for a singleton scope $pr([ bk(ar) ]) cl T -> S$ which would
  embed types into scopes. This operation is not part of the core theory, but
  may be easily added in applications other than OGS for which it is required.
]

To formalize the two isomorphisms, we will not take the route of axiomatizing
two maps, _forward_ and _backward_, which compose to the identity. First remark
that by initiality of $base.bot$, it suffices to have the forward direction
$ctx.emp ctx.var t -> base.bot$ to obtain the first isomorphism (4) in full.

For the second isomorphism (5), taking hints both from Homotopy Type
Theory~#mcite(<hottbook>, supplement: [§4.4, pp.~136--137]) and
from the _view_ methodology~#mcite(<McBrideM04>, dy: 4em, supplement: [§6,
pp.~98--102])#mcite(<Allais23>, dy: 7em), we will axiomatize only the
backward map and ask that its fibers (sets of preimages) are _contractible_,
i.e., inhabited by exactly one element. This will make the isomorphism much
easier to use, enabling inversions by a simple dependent pattern matching
instead of tedious equational rewriting.

#remark[
    Let us quickly see why contractible fibers are of practical interest.
The fibers of a function $f$ can be encoded in type theory by the following family.

#mathpar(block: true, spacing: 1em,
  $kw.dat subs.fiber th {A th B} th (f : A -> B) : base.Type^B \ #v(0.1em)$,
  inferrule($a cl A$, $subs.fib th a cl subs.fiber th f th (f th a)$),
)

Then, given a function $f cl A -> B$ and a proof that its fibers are
inhabited $ "inv" cl (b cl B) -> subs.fiber th f th b, $ in any proof with a variable
$b cl B$ in scope, we can do a dependent elimination on $"inv" th b$. This will
introduce an $a cl A$ and magically unify $b$ with $f th a$, clearing $b$ from
the scope. It is for example trivial to obtain an left-inverse to $f$, given
by $de("get") compose "inv"$ as follows.

#mathpar(block: true, spacing: 1fr,
  $de("get") th {b} cl subs.fiber th f th b -> A \
   de("get") th (subs.fib th a) := a $,
  $de("left-inv") th (b cl B) cl f th (de("get") th ("inv" th b)) = b \
   de("left-inv") := kw.case th p th b \
    pat(
      subs.fib th a := base.refl
    )$,
)

From an additional proof that every element of the fiber $x cl
subs.fiber th f th b$ is equal to $"inv" th b$

$ H cl forall th {b} th (x cl subs.fiber th f th b) -> x = "inv" th b, $

it is again not much work to obtain the right-inverse property, recognizing that
by definition $de("get") th (subs.fib th a) = a$

$ de("right-inv") th (a : A) cl de("get") th ("inv" th (f th a)) = a \
  de("right-inv") a := de("congr") th de("get") th (H th (subs.fib th a)) $
]

As the domain of the backward map of the isomorphism in (5) has as domain a sum
type, I will axiomatize it implicitly as the copairing of two simpler maps:

$ forall th {t} -> Gamma ctx.var t -> (Gamma ctx.cat Delta) ctx.var t \
  forall th {t} -> Delta ctx.var t -> (Gamma ctx.cat Delta) ctx.var t, $

which are respectively definitionally equal to more concise notations

$ & Gamma && ctx.ren (Gamma ctx.cat Delta) \
  & Delta && ctx.ren (Gamma ctx.cat Delta). $

The fibers of the copairing of two maps can be more directly characterized by the
following data type.

$ kw.dat base.vsum th (f cl A -> C) th (g cl B -> C) cl C -> base.Type $

#mathpar(block: true,
  inferrule($i cl A$, $base.vlft th i cl base.vsum th f th g th (f th i)$),
  inferrule($j cl B$, $base.vrgt th j cl base.vsum th f th g th (g th j)$),
)

We are now ready to give the definition of abstract scope structures.

#definition[Abstract Scope Structure][
  Given $S,T cl base.Type$, an _abstract scope structure on $S$ over $T$_
  is given by the following typeclass, mutually defined with a notation for
  renamings.

  $ kw.cls ctx.scope_T th S kw.whr \
    pat(
      ctx.emp cl S,
      ar ctx.cat ar cl S -> S -> S,
      ar ctx.var ar cl S -> T -> base.Type,
      ctx.vemp th {t} th (i cl ctx.emp ctx.var t) cl base.bot,
      ctx.rcatl th {Gamma th Delta} cl Gamma ctx.ren (Gamma ctx.cat Delta),
      ctx.rcatr th {Gamma th Delta} cl Delta ctx.ren (Gamma ctx.cat Delta),
      ctx.vcat th {Gamma th Delta th t} th (i cl (Gamma ctx.cat Delta) ctx.var t) cl base.vsum th ctx.rcatl th ctx.rcatr th i,
      ctx.vcatirr th {Gamma th Delta th t} th {i cl (Gamma ctx.cat Delta) ctx.var t} th v cl ctx.vcat th i = v) $

  $ ar ctx.ren ar cl S -> S -> base.Type \
    Gamma ctx.ren Delta := forall th {t} -> Gamma ctx.var t -> Delta ctx.var t $

  Note that the mnemonic "cat" in the above stands for con#[_cat_]enation (and not for #[_cat_]egory).
] <def-scope>

#definition[Scope Category][
  A scope structure $ctx.scope_T th S$ defines a _category of
  scopes_ $ctx.ctxcat_S$ whose objects are given by $S$ and whose morphisms are
  given by renamings $Gamma ctx.ren Delta$.
  In other words, $ctx.ctxcat_S$ is the _full image_ of $ar""cnorm(ctx.var)$.
]

#remark[
  Note that in the definition of abstract scope structures, the set $T$ plays
  almost no role, being only
  used to form the family category $T -> base.Type$ in the sort of $ctx.var$.
  In future work I believe to be particularly fruitful to replace $T ->
  base.Type$ with an arbitrary suitably well-behaved category $cal("A")$,
  i.e. axiomatizing variables as $ar ctx.var cl S -> cal("A")$.

  In particular $cal("A") := base.Type$ provides a more satisfying account of
  untyped calculi than setting $T := base.unit$, i.e. $cal("A") :=
  base.unit -> base.Type$ (as is currently required). In general, it would
  allow much more flexibility in choosing the sort of term families.
]

#remark[
  Our definition of abstract scope structure is quite close in spirit to the
  the _nameless, painless_ (#txsc[NaPa]) abstraction of
  #nm[Pouillard]~#mcite(<Pouillard11>). Their notion is only concerned with
  untyped scopes and variables, but this is only a superficial difference as
  their theory could certainly be lifted to indexed settings, or ours lowered
  as sketched in the previous remark. Apart from this, the actual difference is
  twofold.

  First, they focus on extending scopes by one variable on the right, whereas we
  axiomatize arbitrary concatenation. We believe that such single variable extension
  is an accident of the typical lists and #nm[De-Bruijn] indices, and that it is
  more practical to abstract over a more symmetric core operation, namely binary
  concatenation. This leads to a rather more concise axiomatization of the laws,
  and to an easier instantiation of the structure in cases where extending on the
  right is not the natural primitive operation.

  Second, they further _axiomatize_ a notion of scope inclusions, whereas we
  _derived_ $ctx.ren$ as functions from variables to variables. Again, this
  leads to their addition of several more laws and coherence conditions. These
  essentially state that scopes and inclusions form a category and that $ctx.var$
  is functorial. Because we decreed that the category of scopes is given by the
  full image of $ctx.var$, every single such law is true _definitionally_.
]

This axiomatization of scopes is enough to derive the two isomorphisms describing the
variables of our scope operations:

$ ctx.emp ctx.var t & approx th base.bot \
  (Gamma ctx.cat Delta) ctx.var t & approx (Gamma ctx.var t) base.sum (Delta ctx.var t) $

In particular, this entails that $ctx.rcatl$ and $ctx.rcatr$ are both injective
and have disjoint images. In fact, assuming an abstract scope structure
$ctx.scope_S th T$, the category $ctx.ctxcat_S$ is cocartesian, with the initial object $ctx.emp$
and the coproduct given by $ctx.cat$.

Before moving on to the theory of scoped-and-typed families and substitution
monoids, let us reap the benefits of this new abstraction and conclude with
some instances of abstract scopes.

=== Instances

*Concrete Scopes* #sym.space.quad Lists and #nm[De Bruijn] indices are the
obvious first instance, which we call _concrete scopes_. Concatenation is computed
by induction on the second (right-hand) context:

$ & ar ctx.catc ar cl ctx.ctxc th T -> ctx.ctxc th T -> ctx.ctxc th T $
#v(-0.5em)
$ & Gamma ctx.catc ctx.nilc & := & Gamma \
  & Gamma ctx.catc (Delta ctx.conc alpha) & := & (Gamma ctx.catc Delta) ctx.conc alpha $

I will not provide the full instantiation of the scope structure, suffice it to say that
statements about concatenation are proven by induction on the second context
argument. Notably, I believe that proving the contractibility property of the
fibers of the coproduct injections ($ctx.vcatirr$) requires the use of
#nm[Streicher]'s axiom K, although I am not entirely sure about this.

#definition[Concrete Scopes][
  Given $T cl base.Type$, _concrete scopes_ $ctx.ctxc th T$ have an abstract
  scope structure with types $T$ given by the following (incomplete) definition.

  $ //de("CtxScope")_T cl ctx.scope_T th (ctx.ctxc th T) \
    de("CtxScope")_T :=
      pat(ctx.emp         & := ctx.nilc,
          Gamma ctx.cat Delta & := Gamma ctx.catc Delta,
          Gamma ctx.var alpha & := Gamma ctx.varc alpha,
          ...) $
]

Pay attention to the difference between $ctx.var$ and $ctx.varc$! The former denotes the
family of concrete #nm[De-Bruijn] indices, while the latter denotes the abstract variables
of a scope structure instance. I apologize for this abuse of notation to the color blind
reader. In any case the symbol $in.rev$ can without any loss be considered to always denote
the abstract notion of variable. In the concrete case it will be definitionally equal to
#nm[De-Bruijn] indices. Further note that this symbol is entirely different to
$in$, which we used to denote predicate membership proofs, i.e., a specialized notation for
reverse function application. The latter will be use exceedingly rarely from
this point on.


*Subset Scopes* #sym.space.quad We can now revisit our introductory example motivating
the notion of abstract scope structures: _subset scopes_.
Given an abstract scope structure $C cl ctx.scope_T th S$, define the following
(strict) predicate lifting.

$ ctx.all_S cl (T -> base.sProp) -> (S -> base.sProp) \
  ctx.all_S th P th Gamma := forall th {alpha} -> Gamma ctx.var alpha -> P th alpha $

We define the subset type of elements of $x$ satisfying $P th x$, i.e., the _total
space_ of the predicate $P$ as follows.

$ base.int th {X cl base.Type} cl (X -> base.sProp) -> base.Type \
  base.int P := (x cl X) times P th x $

#definition[Subset Scopes][ Given an abstract scope instance $ctx.scope_T th S$
  and a predicate $P cl T -> base.Prop$, the type $base.int (ctx.all_S th P)$ of
  _subset scopes_ bears an abstract scope structure on types $base.int P$,
  given by the following (incomplete) definition.

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
] <def-subset-scope>

*Direct Sum of Scopes* #sym.space.quad Languages exist in various shapes and
forms, and sometimes the designers deem it useful to have _two_ kinds of variables,
stored in _two_ different scopes. We can capture this pattern as the direct sum of abstract
scope structures.

#definition[Direct Sum Scopes][ Given two abstract scope instances
  $ctx.scope_(T_1) th S_1$ and $ctx.scope_(T_2) th S_2$, the type $S_1 base.prod
  S_2$ of _direct sum scopes_ bears an abstract scope structure on types $T_1
  base.sum T_2$ given by the following (incomplete) definition.

  $ de("SumScope") cl ctx.scope_(T_1 base.sum T_2) th (S_1 base.prod S_2) \
    de("SumScope") := \ pat(
      ctx.emp & := (ctx.emp , ctx.emp),
      Gamma ctx.cat Delta & := (Gamma .base.fst ctx.cat Delta .base.fst, Gamma .base.snd ctx.cat Delta .base.snd),
      Gamma ctx.var base.inj1 th alpha & := Gamma .base.fst ctx.var alpha,
      Gamma ctx.var base.inj2 th alpha & := Gamma .base.snd ctx.var alpha,
      ...) $
]

*Untyped Scopes* #sym.space.quad An untyped syntax can always be made to fit into
a typed setting by seeing it as un#[*i*]typed, i.e., where the set of types is given
by the singleton $base.unit$, but it is not _that_ simple.
Setting $T := base.unit$ and going on working with e.g., concrete scopes
$ctx.ctxc th base.unit$ and #nm[De-Bruijn] indices is slightly unsatisfying. First
of all, $ctx.ctxc th base.unit$ is isomorphic to the more idiomatic $base.nat$
and likewise, the corresponding #nm[De-Bruijn] indices $th ar""cnorm(ctx.varc) th base.tt cl
base.Type^(ctx.ctxc th base.unit)$ are isomorphic to $base.fin cl
base.Type^base.nat$, the finite sets. Apart from these esthetical
considerations, a more worrying technicality arises when your chosen type theory does
_not_ support the #sym.eta\-rule on $base.unit$. This law
is quite important as it makes all inhabitants of $base.unit$
definitionally equal, and, more importantly, all function $f cl base.unit -> X$
definitionally constant. In the idealized type theory chosen for this thesis we
do assume this #sym.eta\-rule, but our concrete code artifact is stuck with a
theory which does not (Rocq!).

Recall the definition of _finite sets_ $kw.dat th base.fin cl base.Type^base.nat$.

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
$ & base.fshft th {base.ze}   && th i && := i \
  & base.fshft th {base.su m} && th i && := base.su th (base.fshft th {m} th i) $

Finally define _untyped scopes_ as the following instance of scope structure.

$ ctx.untyped cl ctx.scope_base.unit th base.nat \
  ctx.untyped := \
  pat(
    ctx.emp & := base.ze,
    m ctx.cat n & := n + m,
    n ctx.var x & := base.fin th n,
    ctx.rcatl th i & := base.fshft th i,
    ctx.rcatr th i & := base.fwkn th i,
    dots
  ) $
#margin-note(dy: -11em)[
  Note that we swap $m$ and $n$ in the definition of $m ctx.cat n$. The
  reason for this is that scopes are traditionally taken to grow towards
  the right, while unary natural numbers grow towards the left, i.e.,
  addition is defined by recursion on the first argument. This is technically
  unnecessary but helps avoid unpleasant surprises during index juggling.
]

We will use concrete scopes in @ch-ogs, and subset scopes will make an
appearance in @ch-instance but the other instances are mostly here for
illustration.

== Substitution Monoids and Modules <sec-sub-monoid>

Equipped with this new abstraction for scopes, we are ready to continue the
theory of substitution. This will largely follow the now standard approach
outlined in @sec-sub-ovw. We will however introduce one novel contribution:
substitution modules. Let us start with scoped families and assignments.

#definition[Scoped-and-Typed Family][
  Given $S, T cl base.Type$, the set of _scoped-and-typed families_ is given by the following sort.

  $ ctx.fam_T th S := S -> T -> base.Type $

  Scoped-and-typed families form a category with arrows $X ctx.arr Y$ lifted pointwise
  from $base.Type$.
]

#definition[Assignments][
  Assuming a scope structure $ctx.scope_T th S$, given a
  scoped-and-typed family $X cl base.Type^(S,T)$ and $Gamma, Delta : S$, the set
  of _$X$-assignments from $Gamma$ to $Delta$_ is defined as follows.

  $ ar asgn(X) ar : S -> S -> base.Type \
    Gamma asgn(X) Delta := forall th {alpha} -> Gamma ctx.var alpha -> X th Delta th alpha $

  As seen in @sec-sub-ovw, because assignments are represented as functions, we will
  use of extensional equality on assignments at several places. Given $gamma, delta
  cl Gamma asgn(X) Delta$, it is expressed as follows.

  $ gamma approx delta := forall th {alpha} th (i cl Gamma ctx.var alpha) -> gamma th i approx delta th i $
]

#remark[
  By definition, renamings $Gamma ctx.ren Delta$ are exactly given by
  $ctx.var$-assignments $Gamma asgn(ctx.var) Delta$.
]

#definition[Copairing][
  Given a scope structure $ctx.scope_T th S$ and a family $X cl
  base.Type^(S,T)$, we extend the initial renaming $ctx.emp ctx.ren Gamma$ and
  the renaming copairing derived from the cocartesian structure of
  $ctx.ctxcat_S$ to arbitrary $X$-assignments as follows.

  $ de([]) th {Gamma} cl ctx.emp asgn(X) Gamma \
    de([]) th i := kw.case ctx.vemp th i th [] $

  $ de("[")""ar""de(",")ar""de("]") th {Gamma_1 th Gamma_2 th Delta} cl (Gamma_1 asgn(X) Delta) -> (Gamma_2 asgn(X) Delta) \
    #h(6em) -> (Gamma_1 ctx.cat Gamma_2) asgn(X) Delta \
    de("[")""f""de(",")g""de("]") th i := kw.case ctx.vcat th i \
    pat(
      base.vlft th i & := f th i,
      base.vrgt th j & := g th i,
    ) $
]


=== Substitution Monoids

We now define the internal substitution hom and subsequently substitution monoids.

#definition[Internal Substitution Hom][
  Assuming a scope structure $ctx.scope_T th S$, the _internal substitution hom_
  is defined as follows.
  $ //ctxhom("" ar "", ar "") cl ctx.fam_T th S -> ctx.fam_T th S -> ctx.fam_T th S \
    ctxhom("" ar "", ar "") cl base.Type^(S,T) -> base.Type^(S,T) -> base.Type^(S,T) \
    ctxhom(X, Y) th Gamma th alpha := forall th {Delta} -> Gamma asgn(X) Delta -> Y th Delta th alpha $
] <def-sub-hom>

#definition[Substitution Monoids][
  Assuming a scope structure $ctx.scope_T th S$ and a family $X cl base.Type^(S,T)$,
  a _substitution monoid_ structure on $X$ is given by the following typeclass.

  #let eqx = sym.approx
  //$ kw.cls th sub.mon_S th (X cl ctx.fam_T th S) kw.whr \
  $ kw.cls th sub.mon_S th (X cl base.Type^(S,T)) kw.whr \
    pat(
      sub.var cl ar ctx.var ar ctx.arr X,
      sub.sub cl X ctx.arr ctxhom(X, X),
      sub.sext cl sub.sub xrel(rel.forall eqx th attach(ctx.arr, tr: rel.r) ctxhom(eqx, eqx)^de(rel.r)) sub.sub,
      //sub.sext cl base.ext th sub.sub,
      sub.idl th {Gamma th alpha} th (x cl X th Gamma th alpha)
        cl sub.sub th x sub.var approx x,
      sub.idr th {Gamma th alpha} th (i cl Gamma ctx.var alpha) th (gamma cl Gamma asgn(X) Delta)
        cl sub.sub (sub.var th i) th gamma approx gamma th i,
      sub.assoc th {Gamma_1 th Gamma_2 th Gamma_3 th alpha} th (x cl X th Gamma_1 th alpha) \
        quad (gamma cl Gamma_1 asgn(X) Gamma_2) th (delta cl Gamma_2 asgn(X) Gamma_3) \
        quad cl sub.sub (sub.sub th x th gamma) th delta approx sub.sub x th (kw.fun th i |-> sub.sub th (gamma th i) th delta)
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
  are exactly $ctx.var$-relative monads~#mcite(<AltenkirchCU10>). From this
  perspective, one can construct something similar to a #nm[Kleisli] category for
  $X$, the _$X$-assignment category_ $de(cal("A"))_X$ whose objects are
  contexts in $S$ and morphisms are given by $X$-assignments. It is then
  unsurprising that $sub.var$---the unit of the relative monad $X$---is the
  identity morphism of its #nm[Kleisli] category.
]

#remark[
  As stated previously, to avoid functional extensionality, we need to know
  that every function taking assignments as arguments respects their pointwise
  equality. This is the case for $sub.sub$, for which $sub.sext$ is the corresponding
  "congruence" property (sometimes we say "monotonicity"). As in the previous chapter, we hide the rather large type
  of $sub.sext$ by liberally using a form of relational translation of type
  theory~#mcite(<BernardyJP12>), denoted by the superscript $ar^rel.r$.
  Explicitly, given $X^1, X^2, Y^1, Y^2 cl base.Type^(S,T)$ and

  $ X^rel.r cl forall th {Gamma th alpha} -> X^1 th Gamma th alpha -> X^2 th Gamma th alpha -> base.Prop \
    Y^rel.r cl forall th {Gamma th alpha} -> Y^1 th Gamma th alpha -> Y^2 th Gamma th alpha -> base.Prop, $

  $ctxhom(X^rel.r, Y^rel.r)^de(rel.r)$ is defined as follows.

  $ ctxhom(X^rel.r, Y^rel.r)^de(rel.r) th {Gamma th alpha} cl ctxhom(X^1, Y^1) th Gamma th alpha -> ctxhom(X^2, Y^2) th Gamma th alpha -> base.Prop \
    ctxhom(X^rel.r, Y^rel.r)^de(rel.r) th f th g := \
    quad forall th {Delta} th (gamma^1 cl Gamma asgn(X^1) Delta) th (gamma^2 cl Gamma asgn(X^2) Delta) \
    quad -> (forall th {alpha} th (i cl Gamma ctx.var th alpha) -> X^rel.r th (gamma^1 th i) th (gamma^2 th j)) \
    quad -> Y^rel.r th (f th gamma^1) th (g th gamma^2) $

  Then, the type of $sub.sext$ can be seen to unfolds as follows.

  $ forall th & {Gamma th alpha} th {x_1 th x_2 cl X th Gamma th alpha} th (x^rel.r cl x_1 approx x_2) \
              & {Delta} th {gamma_1 th gamma_2 cl Gamma asgn(X) Delta} \
              & -> (forall th {beta} th (i cl Gamma ctx.var beta) -> gamma_1 th i approx gamma_2 th i) \
              & -> x_1 [gamma_1] approx x_2[gamma_2] $

  Remark that with our notation for extensional equality of assignments, the
  above type is the same as the following one.

  $ forall th & {Gamma th alpha} th {x_1 th x_2 cl X th Gamma th alpha} th (x^rel.r cl x_1 approx x_2) \
              & {Delta} th {gamma_1 th gamma_2 cl Gamma asgn(X) Delta} \
              & -> gamma_1 approx gamma_2 \
              & -> x_1 [gamma_1] approx x_2[gamma_2] $

  As such, an alternative compact way to write once again the exact same thing would have been the following

  $ sub.sub xrel(rel.forall cnorm(approx) rel.carr rel.forall (cnorm(approx) rel.arr cnorm(approx))) sub.sub. $

  The extraordinarily scrupulous reader will have noticed that our use of
  $rel.forall$ is here slightly inconsistent with its definition (right before @lem-up2bind). Because
  type-and-scoped families have _two_ indices (the scope and the type), we
  should have written the last expression above as well as our actual type
  for $sub.sext$ with _two_ corresponding $rel.forall$ at the head, i.e., respectively

  $ sub.sub xrel(rel.forall rel.forall cnorm(approx) rel.carr rel.forall (cnorm(approx) rel.arr cnorm(approx))) sub.sub \
    sub.sub xrel(rel.forall rel.forall cnorm(approx) th attach(ctx.arr, tr: rel.r) ctxhom(cnorm(approx), cnorm(approx))^de(rel.r)) sub.sub. $

  This abuse is "easily" made formal by extending the definition of $rel.forall$ to $n$-ary type
  families (and their $n$-ary relation families) as follows.

  $ rel.forall th {X^1 th X^2 cl base.Type^(I_1, .., I_n)} \
    quad cl (forall th {i_1 th .. th i_n} -> X^1 th i_1 th .. th i_n -> X^2 th i_1 th .. th i_n -> base.Prop) \
    quad -> (forall th {i_1 th .. th i_n} -> X^1 th i_1 th .. th i_n) \
    quad -> (forall th {i_1 th .. th i_n} -> X^2 th i_1 th .. th i_n) \
    quad -> base.Prop \
    rel.forall th X^rel.r th F^1 th F^2 := forall th {i_1 th .. th i_n} -> X^rel.r th {i_1} th .. th {i_n} th F^1 th F^2 $

  I hope that this glimpse into pure bureaucratic madness makes it clearer why we
  _need_ our terse and perhaps slightly magical relational combinators.
]

=== Substitution Modules

#[

#let val = de(cop("Val"))
#let cfg = de(cop("Conf"))
#let ecx = de(cop("ECtx"))

Substitution monoids have neatly been generalized to abstract scopes, but for the purpose of
modeling OGS, a part of the theory of substitution is still missing. As
explained in our introductory primer (@sec-intro-ogs), in OGS we will
typically refer to various different syntactic constructs such as _values_, _evaluation
contexts_, _terms_ and evaluator _configurations_.

Values (as well as terms) can be readily represented as a
scoped-and-typed family $ val cl S -> T -> base.Type. $ In contrast, evaluation
contexts are better represented as a family $ ecx cl S -> T -> T -> base.Type, $
where $E cl ecx th Gamma th alpha th beta$ typically denotes an evaluation
context in scope $Gamma$, with a _hole_ of type $alpha$ and an _outer type_
$beta$. The family of configurations of an abstract machine has yet a different
sort as it is only indexed by a scope: $ cfg cl S -> base.Type. $

We already know how to axiomatize substitution for values: their
scoped-and-typed family should form a substitution monoid. But for the other
two kinds of families, we would like to axiomatize a substitution operation
that allows replacing their variables by values. More explicitly, we want the
following substitution operations.

$ sub.sub th {Gamma th alpha th beta} cl ecx th Gamma th alpha th beta -> Gamma asgn(val) Delta -> ecx th Delta th alpha th beta \
  sub.sub th {Gamma} cl cfg th Gamma -> Gamma asgn(val) Delta -> cfg th Delta $

#let cc = math.cal("C")

As we will see, these two maps can be accounted for by constructing a
_substitution module structure over_ $val$ for both $ecx$ and $cfg$.

To capture the substitution of both kinds of variously indexed families, let us
extend the internal substitution hom to $n$-ary families.

#definition[Generalized Substitution Hom][
  Given an abstract scope structure $ctx.scope_T th S$ and a sequence of indexing
  types $T_1, .., T_n cl base.Type$,
  the _generalized substitution hom_ is defined as follows.

  $ ctxhom("" ar "", ar "") cl base.Type^(S,T) -> base.Type^(S,T_1,..,T_n) -> base.Type^(S,T_1,..,T_n) \
    ctxhom(X, Y) th Gamma th alpha_1 th .. th alpha_n := forall th {Delta} -> Gamma asgn(X) Delta -> Y th Delta th alpha_1 th .. th alpha_n $
] <def-sub-hom-gen>

#definition[Substitution Module][
  Given an abstract scope structure $ctx.scope_T th S$ and a sequence of indexing
  types $T_1, .., T_n cl base.Type$,
  a substitution monoid $sub.mon_S th M$ and a family $X cl base.Type^(S,T_1,..,T_n)$, a
  _substitution module over $M$ on $X$_ is given by the following typeclass.
  #margin-note(dy: 2em)[
    I am slightly sloppy around the $n$-ary binders denoted by "$..$". In the
    current Rocq code, I have rather unsatisfyingly special-cased this
    definition for scoped families indexed by 0, 1 or 2 types, which are
    sufficient for our purpose. In further work this precise definition
    could be captured by building upon~#text-cite(<Allais19>)
  ]

  #let eqx = sym.approx
  #let eqm = sym.approx
  //$ kw.cls th sub.mod_S th (X cl ctx.fam_T th S) kw.whr \
  $ kw.cls th sub.mod_S th (X cl base.Type^(S,T_1, .. ,T_n)) kw.whr \
    pat(
      sub.act cl X ctx.arr ctxhom(M, X),
      sub.aext cl sub.act xrel(eqx th attach(ctx.arr, tr: rel.r) ctxhom(eqm, eqx)^de(rel.r)) sub.act,
      sub.aid th {Gamma th alpha_1 th .. th alpha_n} th (x cl X th Gamma th alpha_1 th .. th alpha_n)
        cl sub.act th x sub.var approx x,
      sub.acomp th {Gamma_1 th Gamma_2 th Gamma_3 th alpha_1 th .. th alpha_n} th (x cl X th Gamma_1 th alpha_1 th .. th alpha_n) \
        quad (gamma cl Gamma_1 asgn(M) Gamma_2) th (delta cl Gamma_2 asgn(M) Gamma_3) \
        quad cl sub.act (sub.act th x th gamma) th delta approx sub.act x th gamma[delta]
    ) $
]

Overloading the notation for the ordinary substitution $sub.sub$, we will use
$x[gamma]$ as shorthand for $sub.act th x th gamma$.

=== Renaming Structures

Substitution modules shed a new light on the renaming operation. Indeed, as seen in
@sec-sub-ovw the state of the art is to mechanize a family with renamings as a
coalgebra for the $ctxhom(ctx.var, ar "")$ comonad~#mcite(<FioreS22>)#mcite(dy:
3em, <AllaisACMM21>). However, a family with renamings can also be
characterized as a substitution module over $ctx.var$ (as $ctx.var$ trivially
forms a substitution monoid).

Pulling the other way on these two point of views, substitution modules over $M$
could be reframed as coalgebras for the comonad $sub.box_M X := ctxhom(M, X)$,
exhibiting the reindexing functor $(de(cal(A))_M -> cal(C)) -> (S -> cal(C))$
as comonadic.

Let's give a bit more details. First, the monoid structure on $ctx.var$.

#lemma[Monoid Structure on $ctx.var$][
  Assuming a scope structure $ctx.scope_T th S$, the scoped-and-typed family
  $ar ctx.var ar cl base.Type^(S,T)$ can be equipped with a substitution monoid
  structure as follows.

  $ de(cnorm(in.rev)"-sub-monoid") cl sub.mon th (ar""cnorm(ctx.var)ar) \
    de(cnorm(in.rev)"-sub-monoid") := \
    pat(
      sub.var th i := i,
      sub.sub th i th gamma := gamma th i,
      ...,
    ) $
]

Next, we can define a shorthand for renaming structures.

#definition[Renaming Structure][
  Assuming a scope structure $ctx.scope_T th S$, given a family $X cl base.Type^(S,T_1,..,T_n)$,
  a _renaming structure_ on $X$ is given by the following typeclass.

  $ kw.cls sub.ren th X := sub.mod_ctx.var th X $
]

Finally, we define the $sub.box_M$ comonad and link it with substitution modules.

#definition[Internal Substitution Hom Comonad][
  Assuming a scope structure $ctx.scope_T th S$, given a family $M cl
  base.Type^(S,T)$ equipped with a substitution monoid structure $sub.mon th
  M$, define the following functor.

  $ sub.box_M cl base.Type^(S,T_1,..,T_n) -> base.Type^(S,T_1,..,T_n) \
    sub.box_M th X := ctxhom(M, X) $

  $sub.box_M$ has a comonad structure, with counit $epsilon$ and
  comultiplication $delta$ given as follows.

  #mathpar(block: true, spacing: 2em,
  $ epsilon cl sub.box_M th X ctx.arr X \
    epsilon th f := f th sub.var $,
  $ delta cl sub.box_M th X ctx.arr sub.box_M th (sub.box_M th X) \
    delta th f th gamma_1 th gamma_2 := f th gamma_1[gamma_2] $
  )
]

#lemma[Substitution Module is Coalgebra][
  Assuming a scope structure $ctx.scope_T th S$, given a family $M cl
  base.Type^(S,T)$ equipped with a substitution monoid structure $sub.mon th M$,
  for any $X cl base.Type^(S,T_1,..,T_n)$, substitution module structures over $M$
  on $X$ coincide with $sub.box_M$ comonad coalgebra structures on $X$.

  For any $X$, we directly deduce that $sub.box_M th X$ enjoys a substitution
  module structure over $M$: the free coalgebra structure on $X$.
]
#proof[
  This lemma is more or less trivial, since our definition of substitution
  module can be directly read as the definition of $sub.box_M$ comonad coalgebras. Indeed,
  $sub.act$ coincides with the coalgebra structure map while $sub.aid$ and
  $sub.acomp$ coincide with the two comonad coalgebra laws.
]

The above lemma exhibits the link between our substitution modules and
$sub.box_M$ coalgebras, extending the previous result on renaming
structures~#mcite(<AllaisACMM21>)#mcite(dy: 5em, <FioreS22>).

Finally, we conclude this chapter by defining one last structure, for families
that have both renamings and variables, described by #nm[Fiore] and #nm[Szamozvancev] as
_pointed coalgebras_.

#definition[Pointed Renaming Structure][
  Assuming a scope structure $ctx.scope_T th S$, given a family $X cl base.Type^(S,T)$,
  a _pointed renaming structure_ on $X$ is given by the following typeclass.

  $ kw.cls sub.pren th X := \
    pat(kw.ext th sub.ren th X,
        sub.var cl ar ctx.var ar ctx.arr X,
        sub.avar th {Gamma th Delta th alpha} th i th (rho cl Gamma ctx.ren Delta) cl (sub.var th i)[rho] approx sub.var th (rho th i)
    ) $
]

]

With substitution monoids, substitution modules and renaming structures
defined, we now have the flexible tools we need in the next chapter to
axiomatize the object language of our generic OGS construction. Although we
have only seen a glimpse of what can be done using the intrinsically typed and
scoped approach for modeling binders, I hope to have demonstrated the ease
with which it can be adapted to specific situations like different indexing
(with substitution modules) or new scope representations (with abstract
scope structures).

#import "/lib/all.typ": *

= A Categorical Treatment of Substitution

#peio[todo plan chapitre]

== To Type or not to Type, and Other Questions

#peio[rework, trop verbeux]

Without surprise, programming languages and type systems are routinely
studied by type theory practitioners. As such, the concrete matter of how to
encode and work with syntactic terms of an object language inside type theory
has been widely researched, culminating for example in the #smallcaps[PoplMark]
challenge~#mcite(<poplmark>). There are two main design points: how to
represent variables and bindings, and how to enforce typing.

The general orientation of my Coq formalization is towards correct-by-construction
programming, that is, enforcing as much invariants as possible inside data
structures using dependent typing. As such it is appealing to use the type- and scope-safe
representation of syntax, also called the _intrinsically typed and scoped_ representation.
Terms are indexed both by their scope (or
typing context) and by their type: $de("Term") cl de("Scope") -> de("Ty") -> base.Set$.
This indexation is used to enforce that only well-typed terms are represented
and that no meaningless variable is used. This style is known to be hard to
scale to complex type systems, in which case the preferred approach is to keep
intrinsic scoping, but to use extrinsic typing, i.e., constructing an untyped
syntax and a typing relation on top of that. However, in this thesis I only consider
simply-typed languages, so the simplicity of intrinsic typing and its rich
categorical background is much appreciated.

For further on historical background and detailled exposition of this approach,
I refer interested reader into the two comprehensive papers most closely
related to our setting. A first one by Guillaume Allais et
al.~#mcite(dy: -1em, <AllaisACMM21>) and another by Marcelo Fiore and Dmitrij
Szamozvancev~#mcite(dy: 3em, <FioreS22>). Both come with beautifully crafted
Agda code. For design choice discussion in practical formalization projects, I
can mention #peio[TODO jesper blog, idris talk? metacoq?. TODO? ref cocon, elpi?]

A first important specificity of the point of view I will adopt in this
chapter, is to be completely silent on the actual construction of the syntax.
Indeed, as my goal is to formalize a (reasonably) language-generic OGS
construction, I will only be interested in _specifying_ what operations a
syntax should support and leave open the choice for actual _instanciation_.
Crucially, I will not assume any kind of induction principle. Surely it can be
debated, whether or not something which is not inductively defined diserves to
be called syntax, and indeed the generic OGS construction could very well be
instanciated not by syntax but by some other denotational model of a language.
As such, this chapter will be strictly focused on specifying practical notions
for context, variable and substitution.

== What is a Variable? Abstracting De Bruijn Indices

In the type- and scope-safe approach, one typically starts by defining contexts
by lists of types and variables by dependent De Bruijn indices (membership proofs):

$ & kw.dat th ctx.ctxc th (T cl base.Set) cl base.Set th kw.whr \
  & quad ctx.nilc cl ctx.ctxc th T \
  & quad ar ctx.conc ar cl ctx.ctxc th T -> T -> ctx.ctxc th T $

$ & kw.dat th ar ctx.varc ar th {T} cl ctx.ctxc th T -> T -> base.Set th kw.whr \
  & quad ctx.topc th {Gamma th alpha} cl (Gamma ctx.conc alpha) ctx.varc alpha \
  & quad ctx.popc th {Gamma th alpha th beta} cl Gamma ctx.varc alpha -> (Gamma ctx.conc beta) ctx.varc alpha $

While theoretically a sound choice, it is practically unsatisfactory. Perhaps
the most convincing reason is that storing sequences as singly-linked lists and
membership proofs as unary numbers is not computationally efficient. When
executability is a concern, one typically chooses an off-the-shelf finite map
datastructure such as hash-tables or binary trees. However, while I like to
imagine that my development makes sound computational choices, I must admit
that I have not yet been truly serious about it. But there is a more
type-theoretical objection to lists and De Bruijn indices: while all free
monoid constructions are isomorphic (extensionally equal) to lists, there are situations
where some are more practical than others.

The prime example is the following setting. You have a set of types $T$ and
construct some syntax $de("Term") cl ctx.ctxc th T -> T -> base.Set$. Now for
some reason, you have a subset $S cl T -> base.Prop$ of let's say, _nice_
types, and you need to work with the sub-syntax of terms in _nice_ contexts,
that is in contexts where all types verify $S$. The framework of lists and De
Bruijn indices readily applies to this case, by setting $T' := (alpha cl T)
times S th alpha$ and working with $ctx.ctxc th T'$, i.e.,

$ de(C_1) := ctx.ctxc th ((alpha cl T) times S th alpha). $

However, this completely misses the point that nice contexts are a subset of
contexts, in the sense that they have the same computational content. Indeed,
the arguably more idiomatic definition in this case would be

$ de(C_2) := (Gamma cl ctx.ctxc th T) times de("All") th S th Gamma, $

where

$ de("All") cl (T -> base.Prop) -> (ctx.ctxc th T -> base.Prop) \
  de("All") th S th Gamma := forall th {alpha} -> Gamma ctx.varc alpha -> S th alpha. $

The crucial difference between the two definition is in their notion of
variable. With definition $de(C_2)$, a variable of a nice type in a nice context
is exactly given by a variable of the underlying type in the underlying context,
while with definition $de(C_2)$ it is a membership proof complicated by the
presence of the subset membership witness.

In fact the above situation does appear in typical OGS instances, in which
the scopes tracking the shared variables of both players usually only contain
_negative_ types (functions, computations or otherwise lazy data types).

=== A Bit of Theory

So what is a scope, if not lists? For our purpose, we will only need an empty scope, a
concatenation of scopes and a notion of variable. Before jumping to the
concrete definitions, I will outline the approach at a high categorical level.
Although the mechanization is not at this level of generality---to avoid the
friction of depending on a category theory library---I believe it to be simple
enough be explained here.

#let cc = "C"
#let cxx = de(math.cal(math.bold("C")))
#let aa = math.cal(math.bold("A"))

At this abstract level, given $aa$ a sufficiently well-behaved category, a
notion of scopes is given by a set $cc cl base.Set$, and
- a distinguished element $ctx.emp cl cc$,
- a binary operation $ar ctx.cat ar cl cc -> cc -> cc$,
- and an family representing variables $ctx.var cl cc -> aa$.

Moreover we require that:
- $ctx.var th ctx.emp approx th bot$, where $bot$ is the initial object in $aa$, and
- $ctx.var th (Gamma ctx.cat Delta) approx ctx.var th Gamma + ctx.var th Delta$, where
  $ar + ar$ is the coproduct in $aa$.

The category of contexts $cxx$ is then defined to be the full image of
$ctx.var$: its object are elements of $C$ and maps $cxx[Gamma,Delta]$ are given
by _renamings_ $aa[ctx.var th Gamma, ctx.var th Delta]$.

#let tt = de(cop("Tm"))
In this setting, _scoped families_ of sort $C -> aa$ can then be used to model
terms or other syntactic categories. Given such a family $tt$, we can generalize
renamings into _assignments_, mapping variables in $Gamma$ not to variables in $Delta$
but to $tt$-terms over $Delta$, written as

$ Gamma asgn(tt) Delta := aa[ctx.var th Gamma, tt th Delta]. $

#remark[
The prototypical example of typed and scoped syntax is given by $C := ctx.ctxc
th T$, $aa := T -> base.Set$ and $ctx.var th Gamma := Gamma ctx.varc ar$. In this
setting, scoped families have the usual sort $ctx.ctxc th T -> T -> base.Set$.

The above example can be readily adapted to another implemention of finite
collections $de("Coll")$ such as binary trees, provided it is equipped with a
suitable empty element, a concatenation operation and a membership relation
$de("Coll") -> T -> base.Set$.

At this abstract level we also capture the traditional presentation of untyped intrinsically scoped
syntax with $C := de("Nat")$, $aa := base.Set$ and $ctx.var th n := de("Fin") th n$.
Here, scoped families have the simpler sort $de("Nat") -> base.Set$.
]

Given $tt cl C -> aa$, it can be natural to 

this is enough to give the statements of "$tt$ has variables", "$tt$
can be renamed" and "$tt$ can be substituted":

$ pr("var") th {Gamma} cl aa[ctx.var th Gamma, tt th Gamma] \
  pr("ren") th {Gamma th Delta} cl cxx[Gamma, Delta] -> aa[tt th Gamma, tt th Delta] \
$





=== Subset Scopes

=== Direct Sum of Scopes

== Assignments and Renamings

== Substitution Monoids and Modules

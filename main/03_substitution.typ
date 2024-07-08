#import "/lib/all.typ": *

= A Categorical Treatment of Substitution

In this chapter, I will introduce the necessary preliminaries for
working with syntactic data, variables and substitution. TODO expand intro.

== To Type or not to Type, and Other Questions

Without surprise, typed programming languages and type systems are routinely
studied by Type Theory practitioners. As such, the concrete matter of how to
encode and work with syntactic terms of an object language inside Type Theory
has been widely researched, culminating for example in the #smallcaps[PoplMark]
challenge~#mcite(<poplmark>). There are two main design points: how to
represent variables and bindings, and how to enforce typing.

The general orientation of the formalization is towards correct-by-construction
programming, that is, enforcing as much invariants as possible inside data
structures using typing. As such it is appealing to use the type- and scope-safe
representation of syntax, where terms are indexed both by their scope (or
typing context) and by their type: $"term" cl "scope" -> "typ" -> base.Set$.
This indexation is used to enforce that only well-typed terms are represented
and that no meaningless variable is used. This style is known to be hard to
scale to complex type systems, in which case the preferred approach is to keep
intrinsic scoping, but use extrinsic typing, i.e., constructing an untyped
syntax and a typing relation. However, in this thesis I only consider
simply-typed languages, so the simplicity of intrinsic typing and its rich
categorical background is much appreciated.

For further on historical background and detailled exposition of this approach,
I refer interested reader into the two comprehensive papers most closely
related to our setting: TODO ref, which moreover come with beautifully crafted
Agda code. For design choice discussion in practical formalization projects, I
can mention TODO jesper blog, idris talk? metacoq?. TODO? ref cocon, elpi?

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
  & quad "-"ctx.conc"-" cl ctx.ctxc th T -> T -> ctx.ctxc th T $

$ & kw.dat th "-"ctx.varc"-" th {T} cl ctx.ctxc th T -> T -> base.Set th kw.whr \
  & quad ctx.topc {Gamma th alpha} cl (Gamma ctx.conc alpha) ctx.varc alpha \
  & quad ctx.popc {Gamma th alpha th beta} cl Gamma ctx.varc alpha -> (Gamma ctx.conc beta) ctx.varc alpha $

While theoretically a sound choice, it is practically unsatisfactory. Perhaps
the most convincing reason is that storing sequences as singly-linked lists and
membership proofs as unary numbers is not computationally efficient. When
executability is a concern, one typically chooses an off-the-shelf finite map
datastructure such as hash-tables or binary trees. However, while I like to
imagine that my development makes sound computational choices, I must admit
that I have not yet been truly serious about it. There is a more
type-theoretical objection to lists and De Bruijn indices: while all free
monoid constructions are isomorphic (extensionally equal), there are situations
where some are more practical than others.

The prime example is the following setting. You have a set of types $T$ and
construct some syntax $"term" cl ctx.ctxc th T -> T -> base.Set$. Now for some
reason, you have a subset of say _nice_ types $S cl T -> base.Prop$ and you
need to work with the sub-syntax of terms in _nice_ contexts, that is in contexts
where all types verify $S$. The framework of lists and De Bruijn indices readily
applies to this case, by setting $T' := (alpha cl T) times S th alpha$ and working
with $ctx.ctxc th T'$. However in this presentation, projecting a nice context
to its underlying basic context goes by induction, projecting each element on
its first component. Similarly, one can "downgrade" a nice variable into a
basic one, and even "upgrade" a basic variable into a nice variable, assuming
all the types of the basic context were in fact nice. While simple, all these
back-and-forth functions must be written, used, and their associated laws
proven.

However, instead of working with $ctx.ctxc th ((alpha cl T) times S th alpha)$,
i.e., lists of nice types, the idiomatic choice is to work with $(Gamma cl
ctx.ctxc th T) times "All" th S th Gamma$, i.e., nice lists of types. Instead
of an induction, the underlying context is simply given by first projection.
The associated notion of variable is given by $(Gamma, H) ctx.varc (alpha, t)
:= Gamma ctx.varc alpha$ and the downgrade and upgrade functions are given
by the identity function!

In fact the above situation does appear in typical OGS instances, in which
contexts usually only contain _negative_ types. However to drill down on 

=== Abstract Contexts

=== Scoped Families

== Assignments and Renamings

== Substitution Monoids and Modules

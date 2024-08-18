#import "/lib/all.typ": *

= Generic Operational Game Semantics

== The OGS Game

=== From Co-Patterns to OGS Moves

#peio[wip, moved from previous chapter]

Before moving on, let us define a combinator for constructing an scoped but
untyped family from two scoped-and-typed families which will come in handy in the next
chapter.

#definition[Formal Cut][
  Assuming a scope structure $ctx.scope_T th S$, given two scoped-and-typed
  family $X,Y cl ctx.fam_T th S$, the _formal cut of $X$ and $Y$_ is the
  family $X ctx.cut Y cl S -> base.Set$ defined as follows.

  $ ar ctx.cut ar cl ctx.fam_T th S -> ctx.fam_T th S -> (S -> base.Set) \
    (X ctx.cut Y) th Gamma := (alpha cl T) times X th Gamma th alpha base.prod Y th Gamma th alpha $ 

  The formal cut extends to a functor, with the action on arrows 
]

#peio[wip, moved from previous chapter]

We have defined enough tools to properly work with all
kinds of scoped families supporting substitution. However a last piece of the
syntactic puzzle is missing for OGS: observations. Together with variables,
observations form the content of the messages exchanged during an OGS play.
Observations are typically concretely defined as a form of
_copatterns_~#mcite(<AbelPTS13>), a notion which should be familiar by now
since I have used them extensively at the meta-level of Type Theory (they are
written in #pr("pink")).

Copatterns, like patterns, can be seen as syntactic objects which in particular
use their variables _linearly_. However, an intrinsically typed and scoped
account of linearity is a complex topic of its own (see e.g. #mcite(<WoodA20>))
so we will rather adopt a much simpler point of view in which patterns are
understood as syntactic objects where all variables are fresh. Since a virtue
of the #nm[DeBruijn] indices approach is to eschew any representation of fresh
variables, keeping only bound or free variables, there is no use to index
patterns by some ambiant context. Instead, given a particular pattern,
we should be able to compute its set of _holes_, or _binders_:
#margin-note[
  Once again, the two powersets~#num-cite(<HancockH06>) strike back. Up-to
  argument order, $ctx.fam_T th S$ is given by $T -> subs.Pow th S$ while
  $ctx.bfam_T th S$ is give by $T -> subs.Fam th S$.
] a context listing the types of its fresh (nameless and distinct) variables.
This leads us to describe the shape of observations not as a _scoped_ family,
but as a _binding_ family.

#definition[Binding Family][
  Given an abstract scope structure $ctx.scope_T th S$, a _binding family_ is
  given by a record of the following type.

  $ kw.rec ctx.bfam_T th S kw.whr \
    pat(ctx.Oper cl T -> base.Set,
        ctx.dom th {alpha} cl ctx.Oper th alpha -> S) $
]

The holes of a given element of a binding family can be _filled_ (formally substituted) by
suitable elements of a given scoped-and-typed family, yielding a new
scoped-and-typed family.

#definition[Binding Family Filling][
  Given an abstract scope structure $ctx.scope_T th S$, a binding family $A cl
  ctx.bfam_T th S$ and a scoped-and-typed family $X cl ctx.fam_T th S$, the
  _filling of $A$ by $X$_ is the scoped-and-typed $A ctx.fill X cl ctx.fam_T th S$
  given by records of the following type.

  $ kw.rec th (A ctx.fill X) th Gamma th alpha kw.whr \
    pat(ctx.oper cl A .ctx.Oper th alpha \
        ctx.args cl A .ctx.dom th ctx.oper asgn(X) Gamma) $

  We will use the following shorthand for constructing elements of the filling.
  $ o⟨gamma⟩ := pat(ctx.oper & := o, ctx.args & := gamma) $
]

Finally we provide a simpler definition for the trivial filling $A ctx.fill
(kw.fun th Gamma th alpha |-> base.unit)$, as it enables to see a binding
family as a scoped-and-typed family:

$ floor(ar) cl ctx.bfam_T th S -> ctx.fam_T th S \
  floor(A) th Gamma th alpha := A .ctx.Oper th alpha $

=== Remembering Time

=== Game Strategies and Composition

== Machine Languages

=== Values and Configurations

=== Evaluation

=== Finite Redexes

== The Machine Strategy

=== Telescopic Environments

=== Construction

== Semantics

=== OGS Equivalence

=== Substitution Equivalence

=== Correctness Theorem

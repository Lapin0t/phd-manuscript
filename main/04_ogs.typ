#import "/lib/all.typ": *

= Generic Operational Game Semantics <ch-ogs>

In @ch-game we have seen a general definition of games and the structure of
their strategies and in @ch-subst we have seen an axiomatic framework for
intrinsically typed and scoped substitution. Everything is now in place to
define the generic operational game semantics construction. The plan unfolds
as follows.

1. We first define in @sec-ogs-game the _statics_ of the construction, i.e., the
  description of the game, in the sense of @def-g, parametrized by the
  corresponding statics of the _object language_. These object
  language statics comprise the usual set of _object types_, but also a
  description of _observations_, which we will introduce. After defining the game,
  thanks to the generic construction of strategies over a game from @ch-game,
  we directly obtain the set of OGS strategies and counter-strategies, on which
  we further define an _interaction_ operator.

2. Next, in @sec-machine-lang we axiomatize the dynamics of the language, which
  will be used for parametrizing the OGS model construction. Since this
  axiomatization bears more similarities with abstract machines than usual term
  languages, we call it a _machine language_. It comprises two families for
  _values_ and _configurations_, satisfying suitable substitution operators, as
  well as an _evaluation_ map and an _observation application_ map. We moreover
  state the properties required for the OGS correction theorem.

3. Building upon this, in @sec-machine-strat we finally construct the OGS model,
  building a _machine strategy_ embedding machine configurations into OGS
  strategies.

4. In @sec-ogs-semantics we give #peio[wip]

== The OGS Game <sec-ogs-game>

Recall from the informal introductory description of OGS (#peio[ref]), that OGS
moves consist of pairs of a variable and an _observation_ on it, and that each
these observation introduces fresh variables (i.e., _binds_ new variables). Our
first task is then to properly define the notion of _observation_.

=== Binding Families

/*
In @ch-subst we have defined enough tools to properly work with all
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
*/

At first sight it might seem natural to describe observations as just a
scoped-and-typed family $de("Obs") cl ctx.fam_T th S$, where $o cl de("Obs") th
Gamma th alpha$ denotes an observation $o$ on some value of type $alpha$
binding the fresh variables listed in $Gamma$. However, while this
representation could work out, it would be quite unnatural to manipulate.

#peio[wip, pas très motivé]


#definition[Binding Family][
  Given an abstract scope structure $ctx.scope_T th S$, a _binding family_ is
  given by a record of the following type.

  $ kw.rec ctx.bfam_T th S kw.whr \
    pat(ctx.Oper cl T -> base.Type,
        ctx.dom th {alpha} cl ctx.Oper th alpha -> S) $
]

Before going back to the OGS game, let us first introduce some constructions on
binding families, which we will be useful later on. First holes of a binding
family can be _filled_ by an assignment valued in some scoped-and-typed family,
constructing a new scoped-and-typed family of "formal substitutions".

#definition[Binding Family Filling][
  Given an abstract scope structure $ctx.scope_T th S$, a binding family $A cl
  ctx.bfam_T th S$ and a scoped-and-typed family $X cl ctx.fam_T th S$, the
  _filling of $A$ by $X$_ is the scoped-and-typed $A ctxfill(X) cl ctx.fam_T th S$
  given by records of the following type.
  #margin-note(dy: 2.5em)[
    Note the similarity between the filling $ar ctxfill(ar)$ and the substitution
    tensor product $ar ctx.tens ar$. Once again the two powersets appear. Up to the
    isomorphism, the sort of scoped-and-typed families is given by $T -> subs.Pow th S$
    while the sort of binding families is given by $T -> subs.Fam th S$.
  ]

  $ kw.rec th A ctxfill(X) th Gamma th alpha kw.whr \
    pat(ctx.oper cl A .ctx.Oper th alpha \
        ctx.args cl A .ctx.dom th ctx.oper asgn(X) Gamma) $

  We will use the following shorthand for constructing elements of the filling.
  $ o⟨gamma⟩ := pat(ctx.oper & := o, ctx.args & := gamma) $
]

By filling a binding family with trivial data $A ctxfill(kw.fun th
Gamma th alpha |-> base.unit)$, we can see it as a scoped-and-typed
family. In this case $ctx.args$ becomes trivial, so we provide the following
simpler definition for this special case.

$ abs(ar) cl ctx.bfam_T th S -> ctx.fam_T th S \
  abs(A) th Gamma th alpha := A .ctx.Oper th alpha $

=== Naming Things

OGS moves are pairs of a variable and an observation on it, so assuming a
binding family $de("Obs") cl ctx.bfam_T th S$ and some suitable scope $Gamma$,
the sort of moves should translate formally to $(alpha cl T) base.prod (Gamma
ctx.var alpha) base.prod de("Obs").ctx.Oper th alpha$. However this kind of
object formed by two typed constructs joined on a common type will be quite
useful in other cases, so we introduce a more general combinator.

#definition[Formal Cut][
  Assuming a scope structure $ctx.scope_T th S$, given two scoped-and-typed
  family $X,Y cl ctx.fam_T th S$, the _formal cut of $X$ and $Y$_ is the
  family $X ctx.cut Y cl S -> base.Type$ defined as follows.

  $ ar ctx.cut ar cl ctx.fam_T th S -> ctx.fam_T th S -> (S -> base.Type) \
    (X ctx.cut Y) th Gamma := (alpha cl T) times X th Gamma th alpha base.prod Y th Gamma th alpha $

  Given $x cl X th Gamma th alpha$ and $y cl Y th Gamma th alpha$ we will write
  $x ctx.cute y$ as a shorthand for $ (alpha, x, y) cl (X ctx.cut Y) th Gamma. $
]

#definition[Named Terms][
  Assuming a scope structure $ctx.scope_T th S$, given a scoped-and-typed
  family $X cl ctx.fam_T th S$, the family of _named $X$-terms_ is the
  family $X^ctx.named cl S -> base.Type$ defined as follows.

  $ ar^ctx.named cl ctx.fam_T th S -> (S -> base.Type)\
    X^ctx.named := (ar ctx.var ar) ctx.cut X $
]

Finally, using all of our combinators, given some binding family of
observations $de("Obs") cl ctx.bfam_T th S$, we obtain OGS moves as
$abs(de("Obs"))^ctx.named$, i.e., named observations.

=== Remembering Time

In the OGS game, both players play named observations and in doing so, they
introduce fresh variables corresponding to their holes. These fresh variables
can then be further observed by the other player, but not by themselves! The
game position can thus be described as a pair of scopes $(Gamma, Delta)$, each
tracking the variables introduced by a given player, and thus allowed to be
chosen and observed by the other player. We obtain the following game
definition.

#definition[Naive OGS Game][
  Assuming a scope structure $ctx.scope_T th S$, given a binding family $O cl
  ctx.bfam_T th S$, the _naive OGS game on observations $O$_ is defined as follows.

  $ ogs.naivehg cl game.hg th (S base.prod S) th (S base.prod S) kw.whr \
    pat(game.mv th (Gamma, Delta) := abs(O)^ctx.named th Gamma,
        game.nx th {Gamma, Delta} th (i ctx.cute o) := (Delta ctx.cat O.ctx.dom th o, Gamma)) \
    \
    ogs.naiveg cl game.g th (S base.prod S) th (S base.prod S) kw.whr \
    pat(game.client := ogs.naivehg,
        game.server := ogs.naivehg) $
]

#remark[
  To avoid needlessly duplicating definitions we have prefered a symmetric game,
  where the client and server half-games are equal. To achieve this, we do
  not use an _absolute_ point of view on the scopes, where some player would
  always appends to the first component $Gamma$ while the other appends to
  $Delta$. Instead, we adopt a _relative_ point of view, where the first
  component always tracks the variables introduced by the _currently passive_
  player. As such after each move the two components are swapped.

  While this trick has bought us some simplicity by obtaining a _strictly_
  symmetric game, it should be re-evaluated in future work. Indeed I suspect
  that it murkens the categorical structure of the game in contrast to the
  absolute presentation, which is still symmetric, but only up to an involution
  on the sets of positions.
]

On the face of it, this definition seems quite fine and indeed it corresponds
very closely to the usual OGS construction, yet I have called it _naive_. The
problem with this game definition only arises quite late in the correctness
proof of OGS. To prove the correctness of the OGS model, we will need to prove
that the interaction of a strategy with a counter-strategy is _eventually
guarded_, in the sense of @sec-iter. To do so, we need to bound the number of
move exchanges which do not make the interaction truly progress. A crucial
ingredient, both in the OGS litterature and in our formal proof, is to observe
that under normal conditions, observing some variable $i$ can only trigger
observations on variables $j$ which were introduced _before_ $i$: the so-called
_visibility_ condition #peio[ref??]. The problem is now apparent: by keeping
the variables of both players in separate scopes we loose their relative
ordering in a common timeline, a prerequisite to talk about a variable appearing
before another.

A number of devices can be devised to keep track of this ordering. In fact we
could go further and statically enforce the visibility condition on
moves, not just the merely informative ordering data. However, we choose a simple path
by changing only the positions of the game.
Instead of using two scopes, where after each move the fresh increment
is concatenated into one of the components, we keep a common _list_ $Psi cl ctx.ctxc th S$ of
these context increments. Such lists $ctx.nilc
ctx.conc Gamma_0 ctx.conc Delta_0 ctx.conc Gamma_1 ctx.conc Delta_1 ctx.conc
dots$ will thus contain groups of scopes of fresh variables introduced alternatively by
each player.
Hence, the concatenation of all the _even_ elements
forms the scope of variables introduced by the currently passive player, while
the concatenation of the _odd_ elements contains the variables introduced by
the currently active player. Let us define the necessary utilities.

#definition[OGS Context][
  Assuming a scope structure $ctx.scope_T th S$, define _OGS contexts_ as follows.

  $ ogs.ctx th S := ctx.ctxc th S $

  Further define the _even_ and _odd concatenation maps_ $ogs.catE,ogs.catO cl ogs.ctx th S -> S$ as follows.

  $ & ogs.catE ctx.nilc             && := ctx.emp \
    & ogs.catE (Psi ctx.conc Gamma) && := ogs.catO Psi ctx.cat Gamma \
    \
    & ogs.catO ctx.nilc             && := ctx.emp \
    & ogs.catO (Psi ctx.conc Gamma) && := ogs.catE Psi $
]

We can now give the definition of the refined OGS game.

#definition[OGS Game][
  Assuming a scope structure $ctx.scope_T th S$, given a binding family $O cl
  ctx.bfam_T th S$, the _OGS game_ is defined as follows.

  $ ogs.hg cl game.hg th (ogs.ctx th S) th (ogs.ctx th S) kw.whr \
    pat(game.mv th Psi := abs(O)^ctx.named th ogs.catE Psi,
        game.nx th {Psi} th (i ctx.cute o) := Psi ctx.conc O.ctx.dom th o) \
    \
    ogs.g cl game.g th (ogs.ctx th S) th (ogs.ctx th S) kw.whr \
    pat(game.client := ogs.hg,
        game.server := ogs.hg) $
]

=== Game Strategies and Interaction

Recall that in @def-strat we have generically defined active and passive
strategies over a game as indexed interaction trees. OGS strategies are thus
easily defined.

#definition[OGS Strategies][
  Assuming an abstract scope structure $ctx.scope_T th S$, given a binding
  family $O cl ctx.bfam_T th S$ and a set $R cl base.Type$,
  _active and passive OGS strategy over $O$ with output $R$_ are given as
  follows.

  $ ogs.stratA th R := game.stratA_(ogs.g) th (kw.fun th Psi |-> R) \
    ogs.stratP th R := game.stratP_(ogs.g) th (kw.fun th Psi |-> R) $
]

#remark[
  Note that we have constrained the usual a _output family_ to be constant.
  The primary use for these outputs and #itree.retF moves in strategies is
  compositionality, that is, to allow building bigger strategies from smaller
  components, by sequential composition using the monadic _bind_. However,
  at some point the strategy should be "completed" and make no further use
  of #itree.retF moves. Hence, it would be natural to even set once and for all
  this output to the terminal family $kw.fun Psi |-> base.bot$. This would
  force completed strategies to "play the game", disallowing any #itree.retF move.
  Still, to cut some corners and avoid going too deep into the categorical
  structure of the OGS game, we _will_ make some use of these #itree.retF moves,
  and in fact such constant families of output will suffice.
]

An important construction on game strategies that we have not yet talked about
is _interaction_. Intuitively, it takes an active strategy over a game $G$ and
a passive _counter_-strategy (i.e., a strategy over the dual game $G^game.opp$)
and makes them "play" against each other. This process can either diverge, which
happens if either strategy diverges or if they keep playing moves indefinitely,
or it can return an output, if either strategy plays a #itree.retF move. Given
$G cl game.g th I th J$, $R_1 cl I -> base.Set$ and $R_2 cl J -> base.Set$, this
intuition can be formalized with by following type.

$ ar game.par ar & cl game.stratA_G th R_1 th i
                  -> game.stratP_(G^game.opp) th R_2 th i \
                 & -> delay.t th (((i cl I) base.prod R_1 th i) + (j cl J) base.prod R_2 th j) $

To avoid this unwieldy return type, we will restrict our attention to a simpler
case which suffice for our purpose: the case where both strategies have the
same, constant, output family, matching the restriction we just made in OGS
strategies. Moreover, note that since the OGS game is symmetric, strategies and
counter-strategies are the same thing. Consistently with our previous choices
throughout this thesis, we once again resist the urge to study the interaction
operator in its full generality and choose instead to go straight to the point
of our already quite technical goal: correctness for OGS. With these two
simplifications, the type of the interaction operator can be now given as
follows.

$ ar game.par ar cl ogs.stratA th R th Psi
                 -> ogs.stratP th R th Psi
                 -> delay.t th R $

Constructing this operator is intuitively very simple. To compute $a game.par
p$, start by observing the first move of $a$, then by case:

- If it is $itree.retF th r$ move, the interaction is finished, return $r$.
- If it is $itree.tauF th t$, emit a $itree.tauF$ node and continue computing $t game.par p$.
- If it is $itree.visF th m th k$, continue computing $p th m game.par k$.

This iterative process can be formalized by building upon the theory of iteration
operators developped in @sec-iter. As our goal is to define an operator in the
delay monad, we need to exhibit it as an arrow $X -> delay.t th Y$ for some
sets $X$ and $Y$, arising as the fixed point of an equation $X -> delay.t th (X + Y)$.
To match these requirements we need to uncurry the interaction operator so that
it only takes one argument. To express its uncurried argument type, we
first introduce a small gadget, which will be reused later on.

#definition[Family Join][
  Define the following _family join_ operator on types.

  $ ar ogs.join ar th {I} cl (I -> base.Set) -> (I -> base.Set) -> base.Set \
    X ogs.join Y := (i : I) base.prod X th i base.prod Y th i $

  Borrowing from the similarly defined $ctx.cut$ operator on scoped families,
  we will use the shorthand $x ctx.cute y := (i, x, y)$.
]

#definition[Interaction Equation][
  Assuming $ctx.scope_T th S$, given $O cl ctx.bfam_T th S$ and $R cl
  base.Set$, define the _interaction equation_ coinductively as follows.

  $ ogs.compeq cl (ogs.stratA th R) ogs.join (ogs.stratP th R) -> delay.t th ((ogs.stratA th R) ogs.join (ogs.stratP th R) + R) \
    ogs.compeq th (a ctx.cute p) := \
    pat(itree.obs := kw.case a .itree.obs \
      pat(itree.retF th r & := itree.retF th (base.inj2 th r),
          itree.tauF th t & := itree.tauF th (ogs.compeq th (t ctx.cute p)),
          itree.visF th m th k & := itree.retF th (base.inj1 th (p th m ctx.cute k))))
  $
]

#definition[Naive Interaction Operator][
  Assuming $ctx.scope_T th S$, given $O cl ctx.bfam_T th S$ and $R cl
  base.Set$, define the _naive interaction operator_ by iteration (@def-iter)
  of the interaction equation.

  $ ar game.par ar cl ogs.stratA th R th Psi -> ogs.stratP th R th Psi -> delay.t th R \
    a game.par p := itree.iter_ogs.compeq th (a ctx.cute p) $
]

#remark[
  Note the different treatement of iteration in the #itree.tauF case and in the
  #itree.visF case of the interaction equation. In the #itree.tauF case, we
  emit a #itree.tauF node and continue _coinductively_, while in the
  #itree.visF case, we instead continue _formally_, by returning into the
  left component of the equation.

  Although other variation are most likely possible, I found this one practical
  to work with. The idea is to use a _formal loop_ only in the truly
  important #itree.visF case, that is in case of an interaction between the
  two strategies. In contrast, the #itree.retF and #itree.tauF moves are simply
  "forwarded" and in the #itree.tauF this is acceptable since the iterative call
  is syntactically guarded.

  Further note that although we _could_ also guard the iterative call in the #itree.visF
  case by a #itree.tauF move, this would defeat the purpose of using the theory
  equation iteration and we would in fact directly obtain the naive interaction operator.
  Instead, much of the work required to prove OGS correctness, will be to prove that
  under some circumstances, a _unique, strong_ fixed point of this equation exists,
  i.e., that guarding this last iterative call by a #itree.tauF move is in
  fact _not required_.
]

This concludes our abstract constructions on the OGS game and we now turn to
specifying a suitable axiomatization of programming language for our generic
OGS model.

== Machine Languages <sec-machine-lang>

=== Values and Configurations

=== Evaluation

=== Finite Redexes

== The Machine Strategy <sec-machine-strat>

=== Telescopic Environments

=== Construction

== Semantics <sec-ogs-semantics>

=== OGS Equivalence

=== Substitution Equivalence

=== Correctness Theorem

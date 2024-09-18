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
  we further define an _interaction_ operator for composing strategies.

2. Next, in @sec-machine-lang we introduce a lightweight axiomatization of the
  dynamics of a language with evaluator called a _machine language_, suitable
  for then constructing the OGS model.

3. Building upon this, in @sec-machine-strat we finally construct the OGS model,
  building a _machine strategy_ embedding machine configurations into OGS
  strategies. We further introduce substitution equivalence, an analogue of
  #txsc[ciu] equivalence for machine languages and state the correctness theorem for OGS.


#peio[
  Dans un autre monde je refais le truc en 2 parties, d'abord avec le jeu naif
  (pas de coups finaux, position = paire de scopes), puis dans un 2ème temps
  avec tous les hacks: le jeu avec contextes alternées et environnements
  telescopiques, coups finaux. Ca serait bien plus graduel...

  1. Observations
  2. Simple OGS
    1. OGS Game
    2. Machine Language
    3. Machine Strategy
    4. Correctness
    5. Composition (Here Be Dragons)
  3. Remembering Time
    1. Refined Game
    2. Refined Strategy
]

== OGS Game <sec-ogs-game>

=== Observations <sec-ogs-obs>

Observations are a central component of OGS. Recall from the informal
introductory description (#peio[ref]) that the OGS model proceeds by computing
the normal form of a given configuration (or term) and then splitting it into
a _head variable_, an _observation_ on it, and a _filling assigment_,
associating a value to each _hole_ or _argument_ of the observation. An OGS
_move_ is then obtained by combining the head variable and the observation,
while the assignment is kept local to the OGS strategy and hidden from the
opponent. Symmetrically, the opponent can then _query_ these hidden arguments
by itself playing a move of the same shape, a variable and an observation,
resuming execution on player's side. To make these ideas formal, we first need to
properly define what these observations look like.

Intuitively, the set of observations should be indexed by an object type: the
type of values they are meant to be observing. Moreover, each observation has a
given arity, a list of arguments or holes, i.e., a scope. At first sight it
might seem natural to describe observations simply as a scoped-and-typed family
$de("Obs") cl base.Type^(S,T)$, where $o cl de("Obs") th Gamma th alpha$
denotes an observation $o$ on some value of type $alpha$ with arity $Gamma$.
While this representation could work out, it would be quite unnatural to
manipulate. To explain this, let us take a step back.

For other scoped syntactic categories like values or terms, the indexing scope
constrains what variables the term can _mention_. Because we want to think
about variables like pointers into a scope, in the information flow of the
concepts, the scope is pre-existing and the term over it comes after. It is then
sensible to mimick this information flow formally and use scoped-and-typed
families, making the sort of terms _depend_ on a scope (and also on an object type).
On the other hand, the scope of an observation is not there to constrain
anything but to make known the arity of that observation. Here, the more
natural information flow is to have the scope come _after_ the observation,
which would thus only depends on the type.

These fine encoding considerations might be dismissed as philosophical or even
taste questions but they do typically have consequences on universe levels and
sizes. As a perhaps more tangible argument, there are in typical calculi only a
finite number of observations at any given type while the set of scopes is
infinite. As such, only a fraction of scopes can be the arity of some
observation, wasting the expressivity of scoped-and-typed families since for
most $Gamma$, $de("Obs") th Gamma th alpha$ would be empty.

This leads us to axiomatize observations as _binding families_ which we now define.

#definition[Binding Family][
  #margin-note[
    Note that this definition is isomorphic to $T -> subs.Fam th S$. The record presentation
    is simply for clarity.
  ]
  Given $S,T cl base.Type$, a _binding family_ is given by records of the following type.

  $ kw.rec ctx.bfam th S th T kw.whr \
    pat(ctx.Oper cl T -> base.Type,
        ctx.dom th {alpha} cl ctx.Oper th alpha -> S) $
]

=== The Naive Game

Recall that OGS moves are made of pairs of a variable and an observation. Let
us define these pairs (or in fact _triplets_ accounting for typing information).

#definition[Named Observation][
  Assuming a scope structure $ctx.scope_T th S$, given a binding family $O cl
  ctx.bfam th S th T$ _named observations_ is the scoped family $O^ctx.named cl
  base.Type^S$ defined as follows.

  $ O^ctx.named th Gamma := (alpha cl T) base.prod (Gamma ctx.var alpha) base.prod O.ctx.Oper th alpha $

  We will write $i ctx.cute o$ as a shorthand for $(alpha, i, o)$, leaving
  $alpha$ implicit. Moreover, we lift $ctx.dom$ to named observations with the
  following definition.

  $ ctx.domnm th {Gamma} cl O^ctx.named th Gamma -> S \
    ctx.domnm th (i ctx.cute o) := O.ctx.dom th o $
] <def-named-obs>

In the OGS game, both players play named observations and in doing so, they
introduce fresh variables corresponding to their holes. These fresh variables
can then be further observed by the other player, but not by themselves! The
game positions can thus be described as pairs of scopes $(Gamma, Delta)$, each
tracking the variables introduced by a given player, and thus allowed to be
chosen and observed by the other player. We obtain the following game
definition.

#definition[Naive OGS Game][
  Assuming a scope structure $ctx.scope_T th S$, given a binding family $O cl
  ctx.bfam_T th S$, the _naive OGS game on observations $O$_ is defined as follows.

  $ ogs.naivehg cl game.hg th (S base.prod S) th (S base.prod S) kw.whr \
    pat(game.mv th (Gamma, Delta) := O^ctx.named th Gamma,
        game.nx th {Gamma, Delta} th o := (Delta ctx.cat ctx.domnm th o, Gamma)) \
    \
    ogs.naiveg cl game.g th (S base.prod S) th (S base.prod S) kw.whr \
    pat(game.client := ogs.naivehg,
        game.server := ogs.naivehg) $
] <def-ogs-g-naive>

#remark[
  To avoid needlessly duplicating definitions we have prefered a symmetric game,
  where the client and server half-games are equal. To achieve this, we do
  not use an _absolute_ point of view on the scopes, where some player would
  always append to the first component $Gamma$ while the other player would
  append to $Delta$. Instead, we adopt a _relative_ point of view, where the
  first component always tracks the variables introduced by the _currently
  passive_ player, in other words, the one who played last. As such after
  each move the two components are swapped.

  While this trick has bought us some simplicity by obtaining a _strictly_
  symmetric game, it should be re-evaluated in future work. Indeed, I suspect
  that it murkens the categorical structure of the OGS game in contrast to the
  absolute presentation. Note that the absolute presentation is still symmetric
  but in a weaker sense, only up to a function adapting the position (namely
  swapping the two scopes).
]

On the face of it, this definition seems quite fine and indeed it corresponds
very closely to the usual OGS construction, yet I have called it _naive_. The
problem with this game definition only arises quite late in the correctness
proof of OGS. To prove the correctness of the OGS model, we need to prove
that the interaction of a strategy with a counter-strategy is _eventually
guarded_, in the sense of @sec-iter. To do so, we need to bound the number of
move exchanges which do not make the interaction "truly progress", in a sense
which we will precise later on. A crucial ingredient, both in the OGS
litterature and in our formal proof, is to observe that under normal
conditions,#margin-note[
  This kind of condition is typically called a _visibility_ condition in the game semantic
  litterature. #peio[ref??]
] when being observed on some variable $i$, we can only trigger observations on
opponent variables $j$ which were introduced _before_ $i$. The problem is now
apparent: by keeping the variables of both players in separate scopes we loose
track of their relative ordering in a common timeline, a prerequisite to talk
about a variable appearing before another.

=== Remembering Time

A number of devices can be devised to keep track of this ordering. In fact we
could go further and statically enforce the visibility condition on
moves, not just the merely informative ordering data. However, we choose a simple path
by changing only the positions of the game.
Instead of using two scopes, where after each move the fresh increment
is concatenated into one of the components, we keep a common _list_ $Psi cl ctx.ctxc th S$ of
these context increments. Such lists $ctx.nilc
ctx.conc Gamma_0 ctx.conc Delta_0 ctx.conc Gamma_1 ctx.conc Delta_1 ctx.conc
..$ will thus contain groups of scopes of fresh variables introduced alternatively by
each player.
Hence, the concatenation of all the _even_ elements
forms the scope of variables introduced by the currently passive player, while
the concatenation of the _odd_ elements contains the variables introduced by
the currently active player. Let us define the necessary utilities.

#definition[OGS Context][
  Given a set $S cl base.Type$, the set of _OGS contexts_ is given
  by $ctx.ctxc th S$.

  Assuming a scope structure $ctx.scope_T th S$, further define the _even_ and
  _odd concatenation maps_ $ogs.catE,ogs.catO cl ctx.ctxc th S -> S$ as
  follows.

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

  $ ogs.hg cl game.hg th (ctx.ctxc th S) th (ctx.ctxc th S) kw.whr \
    pat(game.mv th Psi := O^ctx.named th ogs.catE Psi,
        game.nx th {Psi} th o := Psi ctx.conc ctx.domnm th o) \
    \
    ogs.g cl game.g th (ctx.ctxc th S) th (ctx.ctxc th S) kw.whr \
    pat(game.client := ogs.hg,
        game.server := ogs.hg) $
]

=== OGS Strategies and Interaction

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
  Note our slightly peculiar choice of constraining the _output family_ of the
  strategies to be constant.

  In general, the primary use for the output family and the associated
  #itree.retF moves in strategies is compositionality, that is, to allow
  building bigger strategies from smaller components, by sequential
  composition using the monadic _bind_. However, at some point the strategy
  should be "completed" and make no further use of #itree.retF moves. Hence,
  it would be natural to even set once and for all this output to the
  terminal family $kw.fun Psi |-> base.bot$. This would force completed
  strategies to "play the game", disallowing the escape hatch of playing a
  #itree.retF move.

  Still, to cut some corners and avoid going too deep into the categorical
  structure of the OGS game, we _will_ make some use of these #itree.retF moves.
  Their use will be elucidated in the following definition.
]

An important construction on game strategies that we have not yet talked about
is _interaction_. Intuitively, it takes an active strategy over a game $G$ and
a passive _counter_-strategy (i.e., a strategy over the dual game $G^game.opp$)
and makes them "play" against each other. This process can either diverge, which
happens if either strategy diverges or if they keep playing moves indefinitely,
or it can return an output, if either strategy plays a #itree.retF move. Given
$G cl game.g th I th J$, $R_1 cl base.Set^I$ and $R_2 cl base.Set^J$, this
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

#remark[
  We can now see why it is practical to have a _constant_ output $R$. However
  this does not directly explain why we have not set it to $base.bot$.
  Assuming we had fixed $R := base.bot$, the codomain of this interaction,
  $delay.t th base.bot$, would be quite uninteresting as it ensures that the
  interaction behaves like an infinite loop.

  There is an apparent paradox: when using the "proper" definition of
  strategies (with no output), the interaction operator collapses into something trivial.
  The deeper reason for this collapse is that our interaction operator is
  _closed_ in the sense that the interfaces of both strategies match exactly:
  every #itree.visF move by one strategy can be answered by the other and
  vice-versa. To recover interesting behavior, we need to generalize
  from interaction to _open composition_, where both strategies have a common
  interface, but both can also play moves from another _outer_ game. Then, open
  composition _hides_ the common interfaces and computes a strategy for the
  outer game. Assuming some combinator $base.sum$ taking
  a pair of games to the game where both are played in parallel, open
  composition could be typed more or less as follows.

  $ ar game.par ar cl game.stratA_(G base.sum A) th base.bot th (i, j)
                   -> game.stratP_(G^game.opp base.sum A) th base.bot th (i, j)
                   -> game.stratA_A th base.bot th j $

  There are in fact several choices for giving a precise meaning to $base.sum$,
  taking inspiration from the multiplicative disjunction "⅋", familiar in
  game semantics and linear logic #peio[ref?], but also from the #nm[Conway]
  sum of games~#mcite(<Conway76>, supplement: [Chapter 7]).

  While these pursuits are quite interesting, they will take us too deep into
  the theory of games. For our purpose of proving OGS correctness, a simple
  hack suffices. We focus on the simpler closed composition, or _interaction_
  as we have named it, but allow for these non-standard $itree.retF$ moves by
  using non-empty outputs $R$. Moves of the shape $itree.retF th r$ should
  thus be considered as crude approximations of $itree.visF$ moves in some outer
  game, not part of the common interface. We will usually call these moves
  _final moves_.
]

The behavior of the interaction operator is intuitively very simple. To compute
the interaction $s^+ game.par s^-$, start by looking at the first move of $s^+$.

- In case of a return move $itree.retF th r$, the interaction is finished and returns $r$.
- In case of a silent move $itree.tauF th t$, pass it along, continuing as $itree.tauF th (t game.par s^-)$.
- In case of a visible move $itree.visF th m th k$, pass $m$ to the passive strategy, making it
  active, i.e., continue as $s^- th m game.par k$.

This iterative process can be formalized by building upon the theory of iteration
operators developped in @sec-iter, applied to the $delay.t$ monad. As the interaction
operator has two arguments, to apply the theory and express it as the fixed point of
an equation system, we first need to uncurry it. To do so, we introduce a small gadget
which will also be useful later on.

#definition[Family Join][
  Define the _family join_ operator as follows.

  $ ar ogs.join ar th {I} cl base.Type^I -> base.Type^I -> base.Type^I \
    X ogs.join Y := (i : I) base.prod X th i base.prod Y th i $

  Borrowing from the similarly defined named observations, we will use the same
  constructor notation $x ctx.cute y := (i, x, y)$ with the first component
  $i$ left implicit.
]

The domain of the OGS interaction can now be expressed as the family join of
active and passive OGS strategies $(ogs.stratA th R) ogs.join (ogs.stratP th R)$.
We follow up with the interaction equation.

#definition[Interaction Equation][
  #let arg = math.italic("Arg")
  Assuming $ctx.scope_T th S$, given $O cl ctx.bfam th S th T$ and $R cl
  base.Type$, define the _interaction equation_ coinductively as follows,
  with $arg := (ogs.stratA th R) ogs.join (ogs.stratP th R)$.

  $ ogs.compeq cl arg -> delay.t th (arg + R) \
    ogs.compeq th (s^+ ctx.cute s^-) := \
    pat(itree.obs := kw.case s^+ .itree.obs \
      pat(itree.retF th r & := itree.retF th (base.inj2 th r),
          itree.tauF th t & := itree.tauF th (ogs.compeq th (t ctx.cute s^-)),
          itree.visF th m th k & := itree.retF th (base.inj1 th (s^- th m ctx.cute k))))
  $
]

#remark[
  Note the different treatement of iteration in the #itree.tauF case and in the
  #itree.visF case. In the #itree.tauF case, we
  emit a #itree.tauF move, guarding a _coinductive_ self-call, while in the
  #itree.visF case, we instead return into the left component of the equation,
  in a sense performing a _formal_ self-call.

  One way to look at it, is that the interaction works by seeking the first
  visible move (or return move) of the active strategy and that an
  interaction step (i.e. formal loop of the equation) should only happens
  when both strategies truly _interact_.

  More pragmatically, much of the work for proving OGS correctness will be dedicated
  to showing that this equation admits a _strong_ fixed point, i.e., that adding a
  #itree.tauF node to guard the self-call in the $itree.visF$ case is _not_ required.
  On the other hand, adding the #itree.tauF node in the #itree.tauF case is indeed
  always necessary.
]

With this equation in hand we can readily obtain a fixed point by iteration, although
only w.r.t. weak bisimilarity.

#definition[Naive Interaction Operator][
  Assuming $ctx.scope_T th S$, given $O cl ctx.bfam th S th T$ and $R cl
  base.Type$, define the _naive interaction operator_ by iteration (@def-iter)
  of the interaction equation.

  $ ar game.par ar th {Psi} cl ogs.stratA th R th Psi -> ogs.stratP th R th Psi -> delay.t th R \
    s^+ game.par s^- := itree.iter_ogs.compeq th (s^+ ctx.cute s^-) $
]

This concludes our abstract constructions on the OGS game.

== Machine Languages <sec-machine-lang>

To describe the OGS game, that is, the _static_ part of the model, we only
needed to know about the corresponding static part of the language: its types,
scopes and observations. In order to describe OGS strategies arising from the
evaluator of a language, we need to know quite a bit more about this language.
We take this section to introduce the axiomatization of what we call _machine
languages_, owing to the inspiration of abstract-machine-like calculi.

=== Evaluation and Application

To implement the OGS construction we need to know mainly two things: how to
compute our next move and how to resume when we receive an opponent move.
Accordingly this will be reflected in the language axiomatisation with two
maps, evaluation and application. Lets start with the first one.

Recall from the introductory exposition #peio[ref], that the next OGS move is
computed by evaluating the term at hand. In fact, as motivated in the
introduction, we will actually forget about terms and instead only talk about
_configurations_, intuitively the package of a term with its continuation. So,
given some families of _configurations_ $C cl base.Type^S$ and normal form $N
cl base.Type^S$, a possibly non-terminating evaluator for open configurations
can be represented as follows.

$ "eval" th {Gamma} cl C th Gamma -> delay.t th (N th Gamma) $

To actually compute the next move, OGS mandates that these normal
forms be split into three components: the head variable on which it is stuck,
an observation on that variable, and an assignment filling the arguments of the
observation. Instead of axiomatizing a family of normal forms and a splitting
map, exploding each normal form into our three components, we will simply
_define_ normal forms as such triples. Although this might seem overly
restrictive, as we will see later #peio[ref] it makes no real difference on the
implementation side. These _split normal forms_ can be defined as follows.

#definition[Split Normal Forms][
  Assuming a scope structure $ctx.scope_T th S$, given a binding family $O cl
  ctx.bfam th S th T$ and a scoped-and-typed family $V cl base.Type^(S,T)$,
  _split normal forms_ are the scoped family $ctx.norm^(#h(0.15em) O)_V cl base.Type^S$
  defined as follows.

  $ ctx.norm^(#h(0.15em) O)_V th Gamma := (o cl O^ctx.named th Gamma) base.prod (ctx.domnm th o asgn(V) Gamma) $
] <def-split-nf>

Using the newly defined split normal forms, assuming some scoped-and-typed
family of _values_ $V cl base.Type^(S,T)$, the evaluation map of a machine
language can now be typed as follows.

$ "eval" th {Gamma} cl C th Gamma -> delay.t th (ctx.norm^(#h(0.15em) O)_V th Gamma) $

In addition to the evaluation map, the second operator required to make the
OGS construction is the _observation application_ map. Recall that
intuitively, upon receiving a move $(i ctx.cute o)$, the OGS model continues by
looking up the value $v$ associated to $i$ and _applying_ the observation $o$ to $v$,
obtaining a configuration which is then further evaluated to determine the rest of the
strategy. This could be modelled by a map of the following type.

$ "apply" th {Gamma th alpha} cl V th Gamma th alpha -> (o cl O.ctx.Oper th alpha) -> C th (Gamma ctx.cat O.ctx.dom th o) $

Note that the scope of the returned configuration is extended by the observation's
holes, since the filling was not given. In order to have a bit more freedom with
this output scope, thus easing the axiomatization, we make the choice of additionally
passing the observation's arguments to this application map, obtaining the following type.

$ "apply" th {Gamma th alpha} cl V th Gamma th alpha -> (o cl O.ctx.Oper th alpha) -> (O.ctx.dom th o asgn(V) Gamma) -> C th Gamma $

While slightly superfluous for the OGS construction, in presence of variables
and renamings both variants are mutually expressible and we believe that this
second variant is more natural to implement in instances. However, this design
choice should probably be revisited in future work, if only to motivate it
better.

We now package values, configurations, evaluation and application as _bare
language machines_.

#definition[Bare Language Machine][
  Assuming a scope structure $ctx.scope_T th S$ and a binding family $O cl
  ctx.bfam th S th T$, a _bare machine language over observations $O$_ is
  given by records of the following type.

  $ kw.rec ogs.baremachine th O kw.whr \
    pat(
      ogs.val cl base.Type^(S,T),
      ogs.conf cl base.Type^S,
      ogs.eval th {Gamma} cl ogs.conf th Gamma -> delay.t th (ctx.norm^(#h(0.15em) O)_ogs.val th Gamma),
      ogs.apply th {Gamma th alpha} th (v cl ogs.val th Gamma th alpha) th (o cl O.ctx.Oper th alpha) \ quad cl (O.ctx.dom th o asgn(ogs.val) Gamma) -> ogs.conf th Gamma,
    ) $

    Assuming a bare language machine $M$, we will write $ogsapp(v,o,gamma)$ instead of $M.ogs.apply th v th o th gamma$.
    Moreover, assuming a substitution monoid structure on $M.ogs.val$, define the following
    embedding from normal forms into configurations.

    $ ogs.emb cl ctx.norm^(#h(0.15em) O)_(M.ogs.val) ctx.arr M.ogs.conf \
      ogs.emb th ((i ctx.cute o), gamma) := ogsapp(sub.var th i,o, gamma) $

    We will sometimes write $floor(n)$ instead of $ogs.emb th n$ for conciseness. #peio[needed?]
    Finally, define the following _evaluation to (named) observation_.

    $ ogs.evalo th {Gamma} cl M.ogs.conf th Gamma -> delay.t th (O^ctx.named th Gamma) \
      ogs.evalo th c := base.fst itree.fmap M.ogs.eval th c  $
    #peio[todo: def fmap ch2]
]

=== Machine Laws

In order to avoid overwhelming the reader, we have delayed introducing the
requirements on the components of a machine language, hence the prefix "bare".

These requirements, or laws, can be put into two groups: benign and core. The
benign laws should be relatively unsurprising and provide us
with basic tools for working with language machines. More precisely, we will
require that:

- $ogs.val$ forms a substitution monoid,
- $ogs.conf$ forms a substitution module over $ogs.val$,
- $ogs.apply$ commutes with substitution,
- $ogs.apply$ respects pointwise equality of assignments, and
- $ogs.eval$uating an $ogs.emb$eded normal form yields back the same
  normal form.

The core laws, on the other hand, are slightly more intricate and closely
related to the OGS model correction proof. As such we delay their statement yet
again, until we have constructed the model and stated the correction theorem
#peio[ref]. Before packaging up the benign laws, let us precise the extensional
equality of normal forms. Indeed, as normal forms contain an assignment, two
normal forms should only considered _the same_ up to pointwise equality of their
assignments. As before in this thesis, we overload the symbol $approx$ for
extensional equality.

#definition[Normal Form Extensional Equality][
  Assuming a scope structure $ctx.scope_T th S$, given $O cl ctx.bfam th S th
  T$ and $V cl base.Type^(S,T)$, define _normal form extensional equality_ $ar
  approx ar cl rel.irel th ctx.norm^(#h(0.15em) O)_V th ctx.norm^(#h(0.15em)
  O)_V$ by the following data type.
  #margin-note(dy: 2em)[Recall that for assignments, extensional equality $gamma_1
    approx gamma_2$ denotes pointwise equality.]

  $ kw.dat th ar approx ar th {Gamma} kw.whr \
    pat1(cs("refl"_"nf") th {o cl O^ctx.named th Gamma} th {gamma_1 th gamma_2} cl gamma_1 approx gamma_2 -> (o ctx.cute gamma_1) approx (o ctx.cute gamma_2)) $
]

#definition[Lawful Machine Language][
  Assuming a scope structure $ctx.scope_T th S$ and a binding family $O cl
  ctx.bfam th S th T$, a bare machine language $M cl ogs.baremachine th O$ is _lawful_
  if it verifies the following typeclass.
  #margin-note(dy: 12em)[Note that $ogs.evalnf$ requires a _strong_ bisimilarity proof, so that
    evaluation "instantly" returns $n$.]

  $ kw.cls ogs.lawmachine th M kw.whr \
    pat(
      ogs.valsub cl sub.mon th M.ogs.val,
      ogs.confsub cl sub.mod_(M.ogs.val) th M.ogs.conf,
      ogs.appext {Gamma th alpha} th (v cl M.ogs.val th Gamma th alpha) th o \
        quad cl (M.ogs.apply th v th o) xrel(cnorm(approx) rel.arr cnorm(=)) (M.ogs.apply th v th o),
      ogs.appsub th {Gamma th Delta} th (v cl M.ogs.val th Gamma th alpha) th o th gamma th (delta cl Gamma asgn(M.ogs.val) Delta) \
        quad cl ogsapp(v,o,gamma)[delta] = ogsapp(v[delta], o, gamma[delta]),
      ogs.evalnf th {Gamma} th (n cl ctx.norm^(#h(0.15em) O)_(M.ogs.val) th Gamma)
        cl M.ogs.eval th (ogs.emb th n) iteq(approx) itree.ret th n,
    ) $
]

This concludes our axiomatization of language machines for now, as it will be
enough to _construct_ the OGS strategies.

== The Machine Strategy <sec-machine-strat>

At this point of the chapter, given a binding family of observations, we know
how the OGS game looks like. Next, we have engineered some notion of _language
machine_, guided by our intuitions of an informal OGS construction. Now, we need
to actually put it to work by implementing a strategy over the OGS game, given
such a language machine.

=== OGS Environments

Let's start for a moment by considering the naive OGS game (@def-ogs-g-naive).
In the naive OGS game, a pair of scopes $(Gamma, Delta)$ track the variables
introduced by each player. Both player can then query any variable from their
opponent's scope by playing a named observation. In order to know what to do next,
a strategy thus needs to _remember_ the value associated to each variable it has
introduced.

#peio[wip blabla]

For the rest of the chapter, we set a scope structure $ctx.scope_T th S$, a
binding family of observations $O cl ctx.bfam th S th T$ and a language machine
$M cl ogs.baremachine th O$ such that $ogs.lawmachine th M$ holds. We will drop
the prefix $M$ to refer to language machine components, e.g. writing $ogs.val$
instead of $M.ogs.val$.

#definition[Telescopic Environments][
  Given a final scope $Delta cl S$ _active and passive telescopic environments_
  are given by the two families $ogs.teleA$ and $ogs.teleP$ of sort $ctx.ctxc
  th S -> base.Type$ given by the following mutually inductive definitions.

  $ kw.dat ogs.teleA kw.whr \
    pat(
      ogs.tnilA cl ogs.teleA th ctx.nilc,
      ar ogs.tconA th {Psi th Gamma} cl ogs.teleP th Psi -> ogs.teleA th (Psi ctx.conc Gamma),

    ) \
    kw.dat ogs.teleP kw.whr \
    pat(
      ogs.tnilP cl ogs.teleP th ctx.nilc,
      ar ogs.tconP ar th {Psi th Gamma} cl ogs.teleA th Psi -> Gamma asgn(ogs.val) (Delta ctx.cat ogs.catE Psi) -> ogs.teleP th (Psi ctx.conc Gamma),
    ) $

  #peio[j'hésite avec la présentation règle de déduction ci-dessous. Mais si je
        fais ça va falloir que je change toutes les defs pour etre cohérents..]

  #mathpar(block: true, inset: 0.2em,
    inferrule([], $ogs.tnilA cl ogs.teleA th ctx.nilc$),
    inferrule(
      $e cl ogs.teleP th Psi$,
      $e ogs.tconA cl ogs.teleA th (Psi ctx.conc Gamma)$
    ),
    inferrule([], $ogs.tnilP cl ogs.teleP th ctx.nilc$),
    inferrule(
      ($e cl ogs.teleA th Psi$, $gamma cl Gamma asgn(ogs.val) (Delta ctx.cat ogs.catE Psi)$),
      $e ogs.tconP gamma cl ogs.teleP th (Psi ctx.conc Gamma)$
    ),
  )
]

#definition[Telescopic Collapse][
  Given a final scope $Delta cl S$, define the following _active and passive
  telescopic environment collapsing functions_, by mutual induction.

  $ ogs.collA cl ogs.teleA th Psi -> ogs.catO Psi asgn(ogs.val) (Delta ctx.cat ogs.catE Psi) $
  #v(-0.5em)
  $ &ogs.collA th ogs.tnilA     && := [] \
    &ogs.collA th (e ogs.tconA) && := (ogs.collP e)[rho] $
  $ ogs.collP cl ogs.teleP th Psi -> ogs.catE Psi asgn(ogs.val) (Delta ctx.cat ogs.catO Psi) $
  #v(-0.5em)
  $ &ogs.collP th ogs.tnilP           && := [] \
    &ogs.collP th (e ogs.tconP gamma) && := [ogs.collA e, gamma] $

  Where $rho$ is the renaming $(Delta ctx.cat ogs.catO Psi) ctx.ren (Delta ctx.cat (ogs.catO Psi ctx.cat Gamma))$, given
  by $[ctx.rcatl, ctx.rcatr[ctx.rcatl]]$.
]

=== Machine Strategy

#peio[ch2: introduce big-step strategies instead of small-step]

#definition[Machine Strategy][
  Given a final scope $Delta$, define the _machine strategy_ as the big-step strategy
  $ogs.mstrat_M cl strat.bs_(ogs.g) th (O^ctx.named th Delta)$ defined as follows.

  $ ogs.mstrat_M := \
    pat(
      strat.stp th Psi := ogs.conf th (Delta ctx.cat ogs.catE Psi) base.prod ogs.teleA th Psi,
      strat.stn th Psi := ogs.teleP th Psi,
      strat.play th (c, e) := kw.do \
        quad ((i ctx.cute o), gamma) <- ogs.eval th c th ";" \
        quad kw.case (ctx.vcat th i) \
        quad pat(
          ctx.vcatl th i & := itree.ret th (base.inj1 th (i ctx.cute o)),
          ctx.vcatr th j & := itree.ret th (base.inj2 th ((j ctx.cute o), (e ogs.tconP gamma))),
        ),
      strat.coplay th e th (i ctx.cute o) :=
        (ogsapp((ogs.collP e th i)[rho_1], o, rho_2), e ogs.tconA) ,
        /*pat(base.fst & := ogsapp((ogs.collP e th i)[rho_1], o, rho_2),
            base.snd & := e ogs.tconA) ,*/
    ) $

  The renamings $rho_1$ and $rho_2$ are defined as follows.

    $ rho_1 := [ctx.rcatl, ctx.rcatr[ctx.rcatl]] \
      rho_2 := ctx.rcatr[ctx.rcatr] $
]

=== OGS Model and Equivalence

=== OGS Correctness

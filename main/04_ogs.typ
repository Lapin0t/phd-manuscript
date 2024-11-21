#import "/lib/all.typ": *

= Generic Operational Game Semantics <ch-ogs>

In @ch-game we have seen a general definition of games and the structure of
their strategies and in @ch-subst we have seen an axiomatic framework for
intrinsically typed and scoped substitution. Everything is now in place to
define the generic operational game semantics construction. The plan unfolds
as follows.

/*
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
*/

== A Simple OGS Model

=== The OGS Game <sec-ogs-game>

Recall from the informal
introductory description (#peio[ref]) that the OGS model proceeds by computing
the normal form of a given configuration (or term) and then splitting it into
a _head variable_, an _observation_ on it, and a _filling assignment_,
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
$de("Obs") cl base.Type^(S,T)$, #guil[C'est quoi S,T ?] where $o cl de("Obs") th Gamma th alpha$
denotes an observation $o$ on some value of type $alpha$ with arity $Gamma$.
While this representation could work out, it would be quite unnatural to
manipulate. To explain this, let us take a step back.

For other scoped syntactic categories like values or terms, the indexing scope
constrains what variables the term can _mention_. Because we want to think of
variables as pointers into a scope, in terms of conceptual dependency, the scope
is preexisting and the term over it comes afterwards. It is then sensible to
reflect this dependency formally and use scoped-and-typed families, making the
sort of terms _depend_ on a scope (and also on an object type).  On the other
hand, the scope of an observation is not there to constrain anything but to make
known the arity of that observation. Here, the more natural information flow is
to have the scope come _after_ the observation, which would thus only depend on
the type. 

These fine encoding considerations might be dismissed as philosophical or even
aesthetic. But they do  have pragmatic consequences, typically on universe
levels and sizes. As a perhaps more tangible argument, there are in typical
calculi only a finite number of observations at any given type while the set of
scopes is infinite. As such, only a fraction of scopes can be the arity of some
observation, wasting the expressivity of scoped-and-typed families since for
most $Gamma$, $de("Obs") th Gamma th alpha$ would be empty.

#guil[Est-ce-qu'une autre manière de dire les choses en utilisant le vocabulaire du typage bidirectionnel, 
c'est que lorsqu'on type une observation, on infère son scope (i.e. il est généré) ?
C'est en général (par example chez Zeilberger et Krishnaswami) comme ça que l'on présente le jugement de typage des patterns,
qui génère le contexte (linéaire) des variables qu'ils bindent.]

This leads us to axiomatize observations as _binding families_, which we now define.

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

Let us now define OGS moves, which are made of pairs of a variable and an
observation (or in fact _triplets_ accounting for the type which is also
implicitly there).

#definition[Named Observation][
  Assuming a scope structure $ctx.scope_T th S$ and a binding family $O cl
  ctx.bfam th S th T$, the scoped family of _named observations_ $O^ctx.named cl
  base.Type^S$ is defined as follows.

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

#definition[OGS Game][
  Assuming a scope structure $ctx.scope_T th S$, given a binding family $O cl
  ctx.bfam_T th S$, the _OGS game on observations $O$_ is defined as follows.

  $ ogs.hg cl game.hg th (S base.prod S) th (S base.prod S) kw.whr \
    pat(game.mv th (Gamma, Delta) := O^ctx.named th Gamma,
        game.nx th {Gamma, Delta} th o := (Delta ctx.cat ctx.domnm th o, Gamma)) \
    \
    ogs.g cl game.g th (S base.prod S) th (S base.prod S) kw.whr \
    pat(game.client := ogs.hg,
        game.server := ogs.hg) $
] <def-ogs-g-naive>

#remark[
  To avoid needlessly duplicating definitions we have preferred a symmetric game,
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
] <rem-ogs-g-abs-vs-rel>

With the OGS game defined, using the generic description of game strategies
as interaction trees developed in @ch-game, we obtain OGS strategies easily.

#definition[OGS Strategies][
  Assuming an abstract scope structure $ctx.scope_T th S$, given a binding
  family $O cl ctx.bfam_T th S$ _active and passive OGS strategy over $O$_ are
  given as follows.

  $ ogs.stratA := game.stratA_(ogs.g) th (kw.fun th (Gamma, Delta) |-> base.bot) \
    ogs.stratP := game.stratP_(ogs.g) th (kw.fun th (Gamma, Delta) |-> base.bot) $
] <def-ogs-strat>

#guil[À ce moment là on ne sait pas ce que c'est $base.bot$]

=== Diving Into the Machine Strategy

For now we know relatively little about the abstract language for which
we are constructing an OGS model: we know about its scope structure, its set
of types and a binding family describing its observation. To complete the
construction of the OGS model, that is, to implement a strategy for the OGS
game, we will need to know quite a bit more. Concretely, our goal is to
axiomatize something which we call a _language machine_, and to deduce from it
the _machine strategy_, implementing the OGS game. More precisely, we will
implement the machine strategy as a big-step system (#peio[def + ref]) over the
OGS game. As our axiomatization of the language machine is largely guided by
what we need to implement the machine strategy, we introduce both of them in
lock-step, walking gradually through all of their components.

*States* #sym.space.quad The starting point to implement a strategy is to
choose two families for the active and passive states. Recall that intuitively,
during the OGS game, each player introduces fresh variables that their opponent
can subsequently query. As such, the states of the strategy ought to remember
what _value_ was associated to each introduced variable. Because of our tricky
_relative_ point of view we have to take some care with the scopes. Recall that
in a position $(Gamma, Delta)$, if it is _our turn_ to play, then $Gamma$ lists
the opponent-introduced variables, while $Delta$ lists the ones we introduced.
As such, the _active_ states of the machine strategy should contain an
assignment

$ sigma cl Delta asgn("Val") Gamma. $

In contrast, _passive_ strategy states should contain an assignment

$ sigma cl Gamma asgn("Val") Delta. $

For this to make sense, the language machine must have a scoped-and-typed family
$"Val" cl base.Type^(S,T)$ which we call _values_.

In an active position, we need to decide which move to play, so a bit more data is
required besides the assignment $sigma$. Recall that intuitively the OGS model
computes the next move by reducing a program to a normal form. As such active states
need to store such a program. As motivated in the introduction, we
will entirely forget about terms and instead only work with _configurations_,
intuitively the package of a term with its continuation.
We thus postulate
a scoped family $"Conf" cl base.Type^S$ and define the active and passive states of
the machine strategy as follows.

$ ogs.mstratA th (Gamma, Delta) := "Conf" th Gamma base.prod (Delta asgn("Val") Gamma) \
  ogs.mstratP th (Gamma, Delta) := Gamma asgn("Val") Delta $

Next, to implement the machine strategy transitions we need to know two things:
how to compute our next move and how to resume when we receive an opponent
move. Accordingly this will be reflected in the language machine axiomatization
with two maps, evaluation and application. Let us start with the first one.

*Play* #sym.space.quad In the OGS construction the next move is computed
by evaluating the term at hand, hence we need to axiomatize an evaluator. Given
some family of normal form configurations $"Nf" cl base.Type^S$, a possibly
non-terminating evaluator for open configurations can be represented as
follows.

$ "eval" th {Gamma} cl "Conf" th Gamma -> delay.t th ("Nf" th Gamma) $

Then, to actually compute the next move, the OGS construction mandates that
these normal forms be split into three components: the head variable on which
it is stuck, an observation on that variable, and an assignment filling the
arguments of the observation (in other words, a named observation and a filling
assignment). Instead of axiomatizing a family of normal forms and a splitting
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

  Extensional equality of normal is given by the following data type, overloading
  as usual the symbol $approx$.

  $ kw.dat th ar approx ar th {Gamma} kw.whr \
    pat1(cs("refl"_"nf") th {o cl O^ctx.named th Gamma} th {gamma_1 th gamma_2} cl gamma_1 approx gamma_2 -> (o ctx.cute gamma_1) approx (o ctx.cute gamma_2)) $
] <def-split-nf>

Using the newly defined split normal forms, the evaluation map of a machine
language can now be given its final type.

$ ogs.eval th {Gamma} cl "Conf" th Gamma -> delay.t th (ctx.norm^(#h(0.15em) O)_"Val" th Gamma) $

This evaluator is sufficient to implement the active transition function of the machine
strategy as follows.

$ ogs.mstratplay th {Psi} cl ogs.mstratA th Psi -> delay.t th (base.bot base.sum (ogs.hg game.extA ogs.mstratP) th Psi) \
  ogs.mstratplay th (c , sigma) := kw.do \
    quad (o, gamma) <- ogs.eval th c th ";" \
    quad itree.ret th (base.inj2 th (o, [sigma, gamma])) $

#margin-note(dy: -7em)[Here, $base.bot$ stands for the output family of the
machine strategy, which is empty in concordance with @def-ogs-strat.]
The
function starts by computing the normal form $(o, gamma)$, where $o$ is a named
observation and $gamma$ the filling assignment. Then, it plays the move $o$ and
stores the new filling $gamma$ besides the currently stored assignment $sigma$
by copairing of assignments. To detail the typing, assuming $Psi = (Gamma,
Delta)$, we have

$ sigma & cl Delta & asgn("Val") Gamma \
  gamma & cl ctx.domnm th o & asgn("Val") Gamma $

By definition of the OGS game, after playing $o$, the next position is given by $(Delta
ctx.cat ctx.domnm th o, Gamma)$, meaning that we must provide a passive state
of type

$ (Delta ctx.cat ctx.domnm o) asgn("Val") Gamma $

which indeed matches the type of the copairing $[sigma, gamma]$.

*Coplay* #sym.space.quad We now need to define the coplay function, which takes a
passive machine strategy state, a move and returns the next active machine strategy
state. Active states contain a configuration, but also an assignment quite similar to the passive
configuration. This assignment will simply be weakened and passed along: when the opponent
plays a move, we do not introduce any new shared variable, hence, the list of
values we need to remember does not change. #guil[j'ai peur que cette phrase
puisse générer un contre-sens, car Opposant introduit bien des nouvelles variables dans
l'observation qu'il joue.] We can already provide a partial definition.

$ ogs.mstratresp th {Psi} cl ogs.mstratP th Psi -> (ogs.hg game.extP ogs.mstratA) th Psi \
  ogs.mstratresp th sigma th o := \
    pat(base.fst & := th th #box(outset: 0.08em, stroke: 0.5pt, $?$),
        base.snd & := sigma[ctx.rcatl]) $

What is left is to compute the configuration part of the next active
state. Recall that intuitively, upon receiving a move $(i ctx.cute o)$,
the OGS construction obtains the next configuration by looking up the value $v$
associated to $i$ and _applying_ the observation $o$ to $v$. As such, we need
to axiomatize this application operator in the language machine. It could be
modeled by a map of the following type.

$ "apply" th {Gamma th alpha} cl "Val" th Gamma th alpha -> (o cl O.ctx.Oper th alpha) -> "Conf" th (Gamma ctx.cat O.ctx.dom th o) $

Note that the scope of the returned configuration is extended by the observation's
holes, since the filling was not given. While this is precisely the operator needed
for the OGS construction, we chose to generalize it slightly by adding the filling
assignment (i.e., the observation's arguments) as arguments instead of extending
the returned configuration's scope. We thus obtain the following type.

$ ogs.apply th {Gamma th alpha} cl "Val" th Gamma th alpha -> (o cl O.ctx.Oper th alpha) -> (O.ctx.dom th o asgn("Val") Gamma) -> "Conf" th Gamma $

#remark[
While slightly superfluous for the OGS construction, in presence of variables
and substitution, both variants are mutually expressible. My feeling is that this
second variant is more natural to implement in instances as it is the natural encoding
of a generalized eliminator. This design
choice should probably be revisited in future work, if only to motivate it
better.
] <rem-langm-apply-alt>

Using the $ogs.apply$ operator we now finish the definition of the coplay
transition function.

$ ogs.mstratresp th {Psi} cl ogs.mstratP th Psi -> (ogs.hg game.extP ogs.mstratA) th Psi \
  ogs.mstratresp th sigma th (i ctx.cute o) := \
  pat(base.fst & := ogs.apply th (sigma th i)[ctx.rcatl] th o th (ctx.rcatr dot sub.var),
      base.snd & := sigma[ctx.rcatl]) $

Note that this definition crucially requires that values has a pointed renaming
structure. Indeed, both variables and renamings are used to weaken the
assignment part of the state and to "synthesize" the filling assignment passed
to $ogs.apply$.

#guil[J'ai du mal à comprendre le deuxième apply, 
en pratique on ne lui fournit toujours comme value assignment
qu'un weakening ?]

=== The OGS Interpretation

Let us sum up the previous section and properly define the language machines
and then the machine strategy. We have seen that language machines consist of
values, configurations, an evaluation map and an observation application map.

#definition[Language Machine][
  Given a scope structure $ctx.scope_T th S$, a binding family $O cl
  ctx.bfam_T th S$ and families $V cl base.Type^(S,T)$ and $C cl base.Type^S,
  $a _language machine over $O$ with values $V$ and configurations $C$_ is
  given by records of the following type.

  $ kw.rec ogs.machine th O th V th C kw.whr \
    pat(
      ogs.eval th {Gamma} cl C th Gamma -> delay.t th (ctx.norm^(#h(0.15em) O)_V th Gamma),
      ogs.apply th {Gamma th alpha} th (v cl V th Gamma th alpha) th (o cl O.ctx.Oper th alpha) \
        quad cl (O.ctx.dom th o asgn(V) Gamma) -> C th Gamma,
      ogs.appext {Gamma th alpha} th (v cl V th Gamma th alpha) th o \
        quad cl (ogs.apply th v th o) xrel(cnorm(approx) rel.arr cnorm(approx)) (ogs.apply th v th o),
    ) $
]

#remark[
  Note that we added an extensionality lemma to the language machine, stating that
  $ogs.apply$ respects pointwise equality of assignments.
]

/*
Next, for the machine strategy definition to work, we also required that values
come with a pointed renaming structure. In fact we will go a bit further and require
that configurations also have renaming structure and that both $ogs.eval$ and $ogs.apply$
respect it.

#definition[Language Machine Renaming][
  Given a scope structure $ctx.scope_T th S$, a binding family $O cl
  ctx.bfam_T th S$ and a language machine $M cl ogs.machine th O$, a _renaming
  structure on $M$_ is given by the following typeclass.

  $ kw.cls ogs.renmachine th M kw.whr \
    pat(
      kw.ext th sub.pren th M.ogs.val,
      kw.ext th sub.ren th M.ogs.conf,
      ogs.evalren th {Gamma th Delta} th c th (rho cl Gamma ctx.ren Delta) cl M.ogs.eval c[rho] itree.eq (M.ogs.eval th c)[rho],
      ogs.appren th {Gamma th Delta} th v th o th gamma th (rho cl Gamma ctx.ren Delta)
        cl M.ogs.apply th v[rho] th o th gamma[rho] approx (M.ogs.apply th v th o th gamma)[rho],
    ) $
]

#remark[
  Note that the $ogs.evalren$ equation is given w.r.t. $itree.eq$, i.e.,
  strongly bisimilar computation returning extensionally equal normal forms.
]

#remark[
  Further note that in $ogs.evalren$ we implicitely assume a renaming structure on the
  family of "delayed normal forms", i.e., the sorted family $ kw.fun th Gamma |-> delay.t th (ctx.norm^(#h(0.15em) O)_(M.ogs.val) th
  Gamma). $
  We will not detail this too much, but indeed for any $V$, given a renaming
  structure on $V$, we can obtain a renaming structure on
  $ctx.norm^(#h(0.15em) O)_V$, whose action is given by $ ((i ctx.cute o),
  gamma)[rho] := ((rho th i ctx.cute o), gamma[rho]). $
  Moreover, for any $X$, given a renaming structure on $X$, we can obtain a renaming
  structure on $kw.fun th i |-> delay.t th (X th i)$ whose action is given by
  $ u[rho] := ar[rho] itree.fmap u. $
]
*/

Next, assuming a language machine where values and configurations have
renamings, we can give the full definition of the machine strategy.

#definition[Machine Strategy][
  Given a language machine $M cl ogs.machine th O th V th C$
  such that $V$ and $C$ have renamings, i.e., such that $sub.pren th V$
  and $sub.ren th C$ hold, then the _machine strategy_ is the big-step system
  $ogs.mstrat th M cl strat.bs_ogs.g th base.bot$ defined as follows.

  $ ogs.mstrat th M := \
    pat(
      strat.stp th (Gamma, Delta) := C th Gamma base.prod (Delta asgn(V) Gamma),
      strat.stn th (Gamma, Delta) := Gamma asgn(V) Delta,
      strat.play th (c, sigma) := kw.do \
        pat((o, gamma) <- M.ogs.eval th c th ";",
            itree.ret th (base.inj2 th (o, [sigma, gamma]))),
      strat.coplay th sigma th (i ctx.cute o) := \
        pat(base.fst & := M.ogs.apply th (sigma th i)[ctx.rcatl] th o th (ctx.rcatr dot sub.var),
            base.snd & := sigma[ctx.rcatl])
    ) $
]

#guil[Il me semble que la notion de big-step system n'a pas encore été
introduite.] #tom[+1: si je comprends bien il faudrait mettre juste
$strat.t_ogs.g$, ça doit être un leftover d'ancienne notation;
d'ailleurs, attention, il y en a d'autres occurrences.]

We finish up the model construction by embedding the language configurations
into active OGS strategies.

#definition[OGS Interpretation][
  Given a language machine $M cl ogs.machine th O th V th C$
  such that $V$ and $C$ have renamings, i.e., such that $sub.pren th V$
  and $sub.ren th C$ hold, then the _active and passive OGS
  interpretations_ are defined as follows.

  $ ogsinterpA(ar) th {Gamma} cl C th Gamma -> ogs.stratA th (Gamma, ctx.emp) \
    ogsinterpA(c) := itree.unrollA_(ogs.mstrat th M) th (c, []) $

  $ ogsinterpP(ar) th {Gamma th Delta} cl Gamma asgn(V) Delta -> ogs.stratP th (Gamma, Delta) \
    ogsinterpP(gamma) := itree.unrollP_(ogs.mstrat th M) th gamma $
]

=== Correctness?

Now that the OGS interpretation is defined, we can at last state the
correctness property. Intuitively, the goal is to say that if two programs
have bisimilar OGS interpretations, then they are observationally
equivalent. Traditionally, two programs are deemed observationally equivalent,
or more technically _contextually equivalent_, if for any closed context of
some given _ground_ type, when placed in that context either both diverge, or
both reduce to the same value. In our slightly unusual setting which forgoes
any notion of context and instead places configurations at the forefront, the
natural notion of observational equivalence is not _contextual equivalence_ but
instead something we call _substitution equivalence_.

Intuitively, substitution equivalence relates two machine configurations $c_1$
and $c_2$ whenever for any substitution $gamma$, $M.ogs.eval th c_1[gamma]
approx M.ogs.eval th c_2[gamma]$. There are however some subtleties which we
will discuss after the actual definition.

#definition[Substitution Equivalence][
  Assume a language machine $M cl ogs.machine th O th V th C$ such that $V$
  forms a substitution monoid $sub.mon th V$ and that $C$ forms a
  substitution module over it $sub.mod_V th C$. Define _evaluation to (named)
  observation_ as follows.

  $ ogs.evalo th {Gamma} cl C th Gamma -> delay.t th (O^ctx.named th Gamma) \
    ogs.evalo th c := base.fst itree.fmap M.ogs.eval th c $

  #guil[$itree.fmap$ n'a pas encore été introduit.]

  Then, given a scope $Omega cl S$, _substitution equivalence at final scope
  $Omega$_ is the indexed relation on $C$ defined as follows.

  $ ar ogs.subeq ar th {Gamma} cl C th Gamma -> C th Gamma -> base.Prop \
    c_1 ogs.subeq c_2 := (gamma cl Gamma asgn(V) Omega) -> ogs.evalo th c_1[gamma] itree.weq ogs.evalo th c_2[gamma] $
]

The first subtlety is that in the above definition the final _scope_ $Omega$
plays the same role as the ground _type_ of contextual equivalence. The
generalization from a single type to an entire scope is required simply
because in the abstract scope structure axiomatization we did not introduce any
mean to talk about singleton scopes. However, as this scope is freely chosen in
the instances, it may very well be instantiated by a singleton scope, which usually
exist in concrete cases.

Second, instead of directly comparing two normal forms obtained by evaluation,
substitution equivalence first project them onto their named observation part,
disregarding the filling assignments. The reason for this stems from what makes
a "good" ground type. For standard calculi, the ground type of contextual
equivalence is invariably taken to be a very simple type such as booleans or
the unit type. What is important, is that values of this type can be
meaningfully compared syntactically, as this is what contextual equivalence
does.

To see how things could turn bad, let us look at a pathological example that does
not follow this rule. Assume our calculus has a weak reduction that does not
reduce function bodies and now set the ground type of contextual equivalence to
some function type $A -> B$. Then, given two lambda abstractions $u := lambda
x. th U$ and $v := lambda x. th V$ of type $A -> B$, contextual equivalence of
$u$ and $v$ implies that both are syntactically equal. Indeed, under the
trivial context both evaluate to themselves. Hence, two merely pointwise equal
function may be distinguished and this completely breaks important properties of
contextual equivalence, such as characterizing the greatest adequate congruence
relation on terms.

While it might not be very easy to give a clear criterion on what makes a good
ground type in general, our setting makes it is relatively easy. The part of
a normal form which can meaningfully be syntactically compared is exactly its
named observation part (obtained by first projection). One approach would be to
restrict the types of $Omega$ to be such that no observation has any hole,
i.e., such that for any $o cl O.ctx.Oper th alpha$, $O.ctx.dom th o approx
ctx.emp$. This would entail that the projection $base.fst cl
ctx.norm^(#h(0.15em) O)_V th Omega -> O^ctx.named th Omega$ is in fact an
isomorphism. However, we opt for the arguably simpler approach of leaving
$Omega$ unconstrained but dropping the problematic part of the normal forms.

Finally, we can state the much awaited correctness property of the OGS model.

#definition[OGS Correctness][
  Assume a language machine $M cl ogs.machine th O th V th C$ such that $V$
  forms a substitution monoid $sub.mon th V$ and that $C$ forms a
  substitution module over it $sub.mod_V th C$
  #guil[Pourquoi tu n'imposes pas dans la def de language machine que $V$ et $C$ 
  soient des substitution monoid/module ?]. #guil[Ah je vois que tu fais ça 
  dans la def de _Language Machine Respects Substitution_.
  Du coup tu pourrais peut-être annoncer que tu vas raffiner au fur-et-à-mesure
  les axiomes nécessaires pour les languages machines.] Given a scope $Omega cl S$,
  _OGS is correct with respect to substitution equivalence at $Omega$_ if
  the following holds.

  $ forall th {Gamma} th (c_1, c_2 cl C th Gamma) -> ogsinterpA(c_1) itree.weq ogsinterpA(c_2) -> c_1 ogs.subeq c_2 $
]

Alas, from now on, things start to break apart. As explained in the
introduction of this chapter, we will not be able to directly prove correctness
with this simple version of the OGS model. Without going into too many details,
let us see why.

The main tool for proving correctness of OGS, and in fact arguably the prime
reason for introducing game or interactive models in the first hand, is the
definition of a _composition_ operation, taking a player strategy and an opponent
strategy and pitting them to "play" against each other. Indeed, if we manage to
define an operator $ar game.par ar$ such that the following two properties
hold, then we can easily conclude correctness of the OGS model.

$ & ogs.evalo th c[gamma] itree.weq ogsinterpA(c) game.par ogsinterpP(gamma) quad quad && "(adequacy)" \
  & s_1 itree.weq s_2 -> (s_1 game.par t) itree.weq (s_2 game.par t)  && "(congruence)" $

Indeed, given $c_1, c_2 cl C th Gamma$ and assuming $ogsinterpA(c_1) itree.weq
ogsinterpA(c_2)$, we need to prove that for any $gamma cl Gamma asgn(V) Omega$,
$ogs.evalo th c_1[gamma] itree.weq ogs.evalo th c_2[gamma]$.
The proof goes like this.

$ & ogs.evalo th c_1[gamma] && itree.weq ogsinterpA(c_1) game.par ogsinterpP(gamma) quad quad && "by adequacy" \
  &                         && itree.weq ogsinterpA(c_2) game.par ogsinterpP(gamma) && "by congruence on hyp." \
  &                         && itree.weq ogs.evalo th c_2[gamma]                    && "by adequacy" $

Note that for all of this to typecheck, the composition needs to have the following
type.

$ ar game.par ar cl ogs.stratA th (Gamma, ctx.emp)
                  -> ogs.stratP th (Gamma, Omega)
                 -> delay.t th (O^ctx.named th Omega) $


So how would we go about to define composition? Although we have not yet talked
about it, composition is quite a natural thing to do and makes sense for any
game as introduced in @ch-game. After all, games exist to be played! Forgetting
about OGS for a second, intuitively, composition works by inspecting the
beginning of the active strategy, searching for the first _return_ or _visible_
move. In case of a $itree.retF th r$ move, composition ends, returning the
result $r$. In case of a $itree.visF th m th k$ move, $m$ is passed to the
opponent strategy and a _synchronization_ occurs: the active strategy becomes passive,
the passive strategy becomes active, the roles and switched and the composition
starts again. Assuming for simplicity that both the player and the opponent
strategies have a constant output family $R cl base.Type$, given a game $G cl
game.g th I th J$, these intuitions guide us to the following definition.

$ ar game.par ar cl game.stratA_G th (kw.fun th i |-> R) th i
                 -> game.stratP_(G^game.opp) th (kw.fun th j |-> R) th i
                 -> delay.t th R \
  s^+ game.par s^- := \
  pat(itree.obs := kw.case s^+.itree.obs \
      pat(itree.retF th r & := itree.retF th r,
          itree.tauF th t & := itree.tauF th (t game.par s^-),
          itree.visF th m th k & := itree.tauF th (s^- th m game.par k))) $

Our first roadblock is now apparent: instantiating this with the OGS game does
not match the type that we wanted. There are two discrepancies. First,
for two strategies to compose, they must agree on the current game position
$i$. However, for adequacy to typecheck, we need to compose $ogsinterpA(c)$
with $ogsinterpP(gamma)$, respectively at position $(Gamma, ctx.emp)$ and
$(Gamma, Omega)$. Second, OGS strategies as defined in @def-ogs-strat have an
_empty_ output family, i.e., $R := base.bot$. As such, no #itree.retF move will
ever be encountered and the composition operator we have defined will output an
element of $delay.t th base.bot$, in other words an infinite loop!

The definition of composition definitely works as it intuitively should,
so the problem lies in our treatment of $Omega$ in the OGS strategies. To fix
this, the idea is that instead of $Omega$ being part of the game position, it
should appear in the output family. We thus update our definition of OGS
strategies, parametrizing it by this _final scope_.

$ ogs.stratA th Omega := game.stratA_(ogs.g) th (kw.fun th (Gamma, Delta) |-> O^ctx.named th Omega) \
  ogs.stratP th Omega := game.stratP_(ogs.g) th (kw.fun th (Gamma, Delta) |-> O^ctx.named th Omega) $

With this fix, the composition operator can now be specialized to the following
type.

$ ar game.par ar cl ogs.stratA th Omega th (Gamma, Delta) -> ogs.stratP th Omega th (Gamma, Delta) -> delay.t th (O^ctx.named th Omega) $

This is already much more satisfying, although we will need to fix the machine
strategy and the active and passive OGS interpretations to take this new
parameter $Omega$ and the associated return moves into account.

There is however one more roadblock, much more insidious. To understand it, we
need to dive yet deeper into the correctness proof. Proving congruence of
composition will be entirely straightforward and the meat of the correctness
proof is concentrated in the much trickier adequacy proof. Attacking adequacy
directly, by starting to construct a bisimulation, is largely unfeasible
because of the complexity of the right hand side. Hence, we again need to cut
this statement into smaller pieces and devise a more structured proof strategy.
As it happens, composition can be presented as the fixed point of an equation
in the #delay.t monad, in the sense of @sec-iter. Moreover, without too much
work we can show that the left-hand side, $ogs.evalo th c[gamma]$, seen as a
function of $c$ and $gamma$, is also a fixed point of the same equation. Then,
since both sides are fixed points of the same equation, to conclude adequacy it
is sufficient to show that this composition equation has unicity of fixed
points #guil[up-to bisimulation ?]. To ensure this, we build upon our new theory of fixed points and prove
that the composition equation is _eventually guarded_.

What eventual guardedness means in this case, is that synchronizations (move
exchanges) do not happen _too often_. More precisely, in the output of
composition, silent moves have two sources: the ones arising from seeking the
next non-silent move of the active strategy, and the ones arising from a
synchronization. Then, eventual guardedness of composition means that
"move-seeking" #itree.tauF#""s happen infinitely often 
#guil[Je suis perdu,
je pensais que l'eventual guardedness c'était qu'il n'y avait qu'un nombre fini
de synchronization entre deux move-seeking #itree.tauF#"".]. 

This is no small
property and it does not hold for the composition of arbitrary strategies,
only for _visible_ ones. Essentially, visibility mandates that in a position
$(Gamma, Delta)$ when a strategy is queried on a given variable in its scope,
say $i cl Gamma ctx.var alpha$, it must only query variables in $Delta$ that
were introduced _before_ $i$ during the play. However, and this is the problem,
because we have kept the two scopes $Gamma$ and $Delta$ separate, it is not
evident which variables in $Delta$ were introduced before some given variable
in $Gamma$.
#peio[j'ai bougé ton commentaire]
#guil[
  Dans la preuve de soundness, 
  on a besoin de cette restriction uniquement 
  que lorsqu'on n'a pas le droit d'effectuer une évaluation
  entre l'observation sur $i$ et celle que l'on déclenche sur $j$
  (ce qui corresponds aux prémisses de l'hypothèse mystère).
  C'est pour ça que l'on reste sound dans un cadre avec references d'ordre supérieure,
  où l'on n'est plus visible. Dans ce cas là, on a besoin d'aller récupérer dans
  l'état mémoire le nom $j$ (s'il n'est pas dans notre vue),
  ce qui nécessite une étape d'évaluation.
  Du coup je pense qu'il faut soit préciser, soit supprimer 
  le lien avec la visibilité.
]

Our solution to this second problem is conceptually quite simple: we will
switch to a more informative set of positions for the OGS game. Instead of
using a pair of scopes, we will use a single _list of scopes_, containing an
alternation of scopes of variables introduced by each player, hence keeping
track of their relative order.

#remark[
  Note that to avoid getting too deep into the theory of OGS strategies, we
  will entirely side-step the definition of the visibility condition and
  instead only prove eventual guardedness for composition of two instances of
  the machine strategy, which happens to behave satisfyingly.
]

The next section is thus devoted to the definition of an OGS game refined with
our two patches: final moves and interlaced positions. We will then fix the
machine strategy, properly define composition and state the correctness theorem.

== A Refined OGS Model

=== Interlaced Positions

As explained in the previous section, instead of tracking the OGS position
using two scopes, where after each move the fresh increment
is concatenated into one of the components, we now keep a common _list_ $Psi cl
ctx.ctxc th S$ of these context increments. Such lists $ctx.nilc ctx.conc
Gamma_0 ctx.conc Delta_0 ctx.conc Gamma_1 ctx.conc Delta_1 ctx.conc ..$ will
thus contain groups of scopes of fresh variables introduced alternatively by
each player. Hence, the concatenation of all the _even_ elements forms the
scope of variables introduced by the currently passive player, while the
concatenation of the _odd_ elements contains the variables introduced by the
currently active player. Let us define the necessary utilities.

#definition[Interlaced OGS Context][
  Given a set $S cl base.Type$, the set of _interlaced OGS contexts_ is given
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

=== Final Moves and Composition

Besides refining the OGS positions, our second patch is to add _final moves_
to the OGS strategies. Intuitively, OGS strategies will now be parametrized
by a _final scope_ $Omega$, and will be allowed to use #itree.retF moves to
play a named observation on $Omega$. While these moves are quite similar
to the usual ones (also being named observations), they bear no continuation.
Instead, they should be thought of as _final moves_, ending the game.

#definition[OGS Strategies][
  Assuming an abstract scope structure $ctx.scope_T th S$, given a binding
  family $O cl ctx.bfam_T th S$ and a scope $Omega cl S$,
  _active and passive OGS strategy over $O$ with final scope $Omega$_ are given as
  follows.

  $ ogs.stratA th Omega := game.stratA_(ogs.g) th (kw.fun th Psi |-> O^ctx.named th Omega) \
    ogs.stratP th Omega := game.stratP_(ogs.g) th (kw.fun th Psi |-> O^ctx.named th Omega) $
]

As explained before, this is now enough to define a meaningful composition
operator. However, instead of the direct construction we have shown earlier, we
will construct composition as the fixed point of an equation in the #delay.t
monad. As the composition operator has two arguments, to express it as the
fixed point of an equation system, we first need to uncurry it. As the type of
its uncurried argument is a bit of a mouthful, we express it with a small
gadget which will also be useful later on.

#definition[Family Join][
  Define the _family join_ operator as follows.

  $ ar ogs.join ar th {I} cl base.Type^I -> base.Type^I -> base.Type^I \
    X ogs.join Y := (i : I) base.prod X th i base.prod Y th i $

  Borrowing from the similarly structured named observations, we will use the
  same constructor notation $x ctx.cute y := (i, x, y)$ with the first
  component $i$ left implicit.
]

The domain of the OGS interaction can now be expressed as the family join of
active and passive OGS strategies $(ogs.stratA th Omega) ogs.join (ogs.stratP
th Omega)$. We follow up with the composition equation.

#definition[Composition Equation][
  #let arg = math.italic("Arg")
  Assuming $ctx.scope_T th S$, given $O cl ctx.bfam th S th T$ and $Omega cl
  S$, define the _composition equation_ coinductively as follows, with $arg
  := (ogs.stratA th Omega) ogs.join (ogs.stratP th Omega)$.

  $ ogs.compeq cl arg -> delay.t th (arg + O^ctx.named th Omega) \
    ogs.compeq th (s^+ ctx.cute s^-) := \
    pat(itree.obs := kw.case s^+ .itree.obs \
      pat(itree.retF th r & := itree.retF th (base.inj2 th r),
          itree.tauF th t & := itree.tauF th (ogs.compeq th (t ctx.cute s^-)),
          itree.visF th m th k & := itree.retF th (base.inj1 th (s^- th m ctx.cute k))))
  $
] <def-compo-eqn>

#guil[Je suis un peu perdu par cette def. Est-ce-que ça ne serait pas
plus éclairant de juste fournir les équations explicites ?
Tu pourrais aussi faire un renvoi à la section sur Iteration Operators ici.]
#remark[
  Note the different treatment of iteration in the #itree.tauF case and in the
  #itree.visF case. In the #itree.tauF case, we
  emit a #itree.tauF move, guarding a _coinductive_ self-call, while in the
  #itree.visF case, we instead return into the left component of the equation,
  in a sense of performing a _formal_ self-call.

  One way to look at it, is that the interaction works by seeking the first
  visible move (or return move) of the active strategy and that an
  interaction step (i.e. a formal loop of the equation) should only happens
  when both strategies truly _interact_.

  More pragmatically, much of the work for proving OGS correctness will be dedicated
  to showing that this equation admits a _strong_ fixed point, i.e., that adding a
  #itree.tauF node to guard the self-call in the $itree.visF$ case is _not_ required.
  On the other hand, adding the #itree.tauF node in the #itree.tauF case is indeed
  always necessary.
]

With this equation in hand we can readily obtain a fixed point by iteration, although
only w.r.t. weak bisimilarity.

#definition[Composition Operator][
  Assuming $ctx.scope_T th S$, given $O cl ctx.bfam th S th T$ and $Omega cl
  S$, define the _composition operator_ by iteration (@def-iter)
  of the interaction equation.

  $ ogs.comp cl (ogs.stratA th Omega) ogs.join (ogs.stratP th Omega) -> delay.t th (O^ctx.named th Omega) \
    ogs.comp := itree.iter_ogs.compeq $

  $ ar game.par ar th {Psi} cl ogs.stratA th Omega th Psi -> ogs.stratP th Omega th Psi -> delay.t th (O^ctx.named th Omega) \
    s^+ game.par s^- := ogs.comp th (s^+ ctx.cute s^-) $
] <def-compo-opaq>

This concludes our abstract constructions on the refined OGS game.

=== Precise Scopes for the Machine Strategy

Thankfully, the axiomatization of language machines has been left intact by our
two patches to the OGS game. We however need to modify the machine strategy.
First, we need to take into account the final scope $Omega$, and second,
we need to take advantage of the new information available in the
positions.

To avoid some clutter, in this section we globally set a scope structure
$ctx.scope_T th S$, a binding family of observations $O cl ctx.bfam th S th T$,
two families $V cl base.Type^(S,T)$ and $C cl base.Type^S$ such that $sub.pren
th V$ and $sub.ren th C$, and a language machine $M cl ogs.machine th O th V th
C$.

Recall that with the simple OGS game, machine strategy states were defined as
follows.

$ ogs.mstratA th (Gamma, Delta) := C th Gamma base.prod (Delta asgn(V) Gamma) \
  ogs.mstratP th (Gamma, Delta) := Gamma asgn(V) Delta $

With the new interlaced game positions we can still recompute the two scopes,
so that adding the final scope $Omega$ to the mix, we could be tempted to
define the new states as follows.

$ ogs.mstratA th Psi := C th (Omega ctx.cat ogs.catE Psi) base.prod (ogs.catO Psi asgn(V) (Omega ctx.cat ogs.catE Psi)) \
  ogs.mstratP th Psi := ogs.catE Psi asgn(V) (Omega ctx.cat ogs.catO Psi) $

This would indeed work, but now that we have more information we can be much
more precise in tracking the scopes of each value stored in the assignments.
This is quite important since every ounce of precise specification we can cram
into the typing will be something less to worry about during manipulation and
proofs. Taking a step back, let us consider what must actually be stored inside
these assignments. Taking the point of view of the machine strategy, at every
point of the game where we play a move, we have a normal form, we emit its
named observation part and we must remember the filling assignment part. As such,
the exact scope used by this filling is the opponent scope _at that point in
the game_ (and as always the final scope $Omega$). We concretize this idea with
the following definition of _telescopic environment_, defined inductively over
the interleaved OGS position.

#definition[Telescopic Environments][
  Given a final scope $Omega cl S$, _active and passive telescopic environments_
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
      ar ogs.tconP ar th {Psi th Gamma} cl ogs.teleA th Psi -> Gamma asgn(ogs.val) (Omega ctx.cat ogs.catE Psi) -> ogs.teleP th (Psi ctx.conc Gamma),
    ) $

  #guil[C'est quoi $ogs.tconA$ ?]

  #peio[j'hésite avec la présentation règle de déduction ci-dessous. Mais si je
        fais ça va falloir que je change toutes les defs pour etre cohérents..]
  #guil[Je trouve ça beaucoup plus lisible avec les règles de déductions.
  Qu'est-ce-que tu devrais changer dans les autres defs pour être cohérent ?]

  #mathpar(block: true, inset: 0.2em,
    inferrule([], $ogs.tnilA cl ogs.teleA th ctx.nilc$),
    inferrule(
      $e cl ogs.teleP th Psi$,
      $e ogs.tconA cl ogs.teleA th (Psi ctx.conc Gamma)$
    ),
    inferrule([], $ogs.tnilP cl ogs.teleP th ctx.nilc$),
    inferrule(
      ($e cl ogs.teleA th Psi$, $gamma cl Gamma asgn(ogs.val) (Omega ctx.cat ogs.catE Psi)$),
      $e ogs.tconP gamma cl ogs.teleP th (Psi ctx.conc Gamma)$
    ),
  )
]

This data is enough to recover the original assignments of the simple OGS model,
as witnessed by the following _collapsing functions_.

#definition[Telescopic Collapse][
  Given a final scope $Omega cl S$, define the following _active and passive
  telescopic environment collapsing functions_, by mutual induction.

  $ ogs.collA cl ogs.teleA th Psi -> ogs.catO Psi asgn(ogs.val) (Omega ctx.cat ogs.catE Psi) $
  #v(-0.5em)
  $ &ogs.collA th ogs.tnilA     && := [] \
    &ogs.collA th (e ogs.tconA) && := (ogs.collP e)[rho] $
  $ ogs.collP cl ogs.teleP th Psi -> ogs.catE Psi asgn(ogs.val) (Omega ctx.cat ogs.catO Psi) $
  #v(-0.5em)
  $ &ogs.collP th ogs.tnilP           && := [] \
    &ogs.collP th (e ogs.tconP gamma) && := [ogs.collA e, gamma] $

  Where $rho$ is the renaming $(Omega ctx.cat ogs.catO Psi) ctx.ren (Omega ctx.cat (ogs.catO Psi ctx.cat Gamma))$, given
  by $[ctx.rcatl, ctx.rcatr[ctx.rcatl]]$.
] <def-tele-collapse>

The refined machine strategy is now simply a matter of adapting to the new telescopic
environment, and routing the moves properly, depending on whether they concern the
final scope $Omega$ or "normal" variables.

#definition[Machine Strategy][
  Given a final scope $Omega cl S$, define the _machine strategy_ as the big-step strategy
  $ogs.mstrat_M cl strat.bs_(ogs.g) th (O^ctx.named th Omega)$ defined as follows.

  $ ogs.mstrat_M := \
    pat(
      strat.stp th Psi := ogs.conf th (Omega ctx.cat ogs.catE Psi) base.prod ogs.teleA th Psi,
      strat.stn th Psi := ogs.teleP th Psi,
      strat.play th (c, e) := kw.do \
        quad ((i ctx.cute o), gamma) <- ogs.eval th c th ";" \
        quad kw.case (ctx.vcat th i) \
        quad pat(
          ctx.vcatl th i & := itree.ret th (base.inj1 th (i ctx.cute o)),
          ctx.vcatr th j & := itree.ret th (base.inj2 th ((j ctx.cute o), (e ogs.tconP gamma))),
        ),
      strat.coplay th e th (i ctx.cute o) :=
        (ogs.apply th (ogs.collP e th i)[rho_1] th o th rho_2, e ogs.tconA) ,
        /*pat(base.fst & := ogsapp((ogs.collP e th i)[rho_1], o, rho_2),
            base.snd & := e ogs.tconA) ,*/
    ) $

  The renamings $rho_1$ and $rho_2$ are defined as follows.

    $ rho_1 := [ctx.rcatl, ctx.rcatr[ctx.rcatl]] \
      rho_2 := ctx.rcatr[ctx.rcatr] $
] <def-machine-strat>

#peio[ch2: introduce big-step strategies instead of small-step]

OGS interpretation can now be defined just like before, by unrolling of the big-step system
defined by the machine strategy.

#definition[OGS Interpretation][
  Given a final scope $Omega cl S$, define the _active and passive OGS interpretations_ as
  follows.

  $ ogsinterpA(ar) th {Gamma} cl C th Gamma -> ogs.stratA th Omega th (ctx.nilc ctx.conc Gamma) \
    ogsinterpA(c) := itree.unrollA_(ogs.mstrat th M) th (c[ctx.rcatr], ogs.tnilP ogs.tconA) $

  $ ogsinterpP(ar) th {Gamma} cl (Gamma asgn(V) Omega) -> ogs.stratP th Omega th (ctx.nilc ctx.conc Gamma) \
    ogsinterpP(gamma) := itree.unrollP_(ogs.mstrat th M) th (ogs.tnilA ogs.tconP gamma[ctx.rcatl]) $
] <def-ogs-interp>

=== Correctness!

Finally we arrive at correctness. The statement is still the same as for the simple OGS model:

$ forall th {Gamma} th (c_1 th c_2 cl C th Gamma) -> ogsinterpA(c_1) itree.weq ogsinterpA(c_2) -> c_1 ogs.subeq c_2 $

Now, though, we will not stop at the mere statement, but provide the actual
theorem. As such, we need to introduce a couple hypotheses on which the theorem
depends.

*Respecting Substitution* #sym.space.quad Until now, we have required very
little on the language machine. For the machine strategy construction, we have
required renaming structures on values and configurations, while for the
correctness statement we have required substitution monoid and module
structures on values and configurations. In both cases, we did not constrain
in any way $M.ogs.eval$ and $M.ogs.apply$, this is of course unrealistic!
For correctness to work, we will crucially need to know that both maps of
the machine respect substitution.
Let us introduce these core hypotheses.

#definition[Language Machine Respects Substitution][
#margin-note[It would definitely be interesting
to define language machines respecting _renamings_, but as substitutions subsume
renamings we will skip over this notion.]
  Assume a scope structure $ctx.scope_T th S$, a binding family $O cl ctx.bfam
  th S th T$, two families $V$, $C$, and a language machine $M cl ogs.machine
  th O th V th C$ such that moreover $sub.mon th V$ and $sub.mod_V th C$.
  Define the embedding of normal forms into configurations as follows.

  $ ogs.emb cl ctx.norm^(#h(0.15em) O)_V ctx.arr C \
    ogs.emb th ((i ctx.cute o), gamma) := M.ogs.apply th (sub.var th i) th o th gamma $

  Then, the language machine $M$ _respects substitution_ if there is an instance
  to the following typeclass.

  $
#margin-note[
  Note that the laws $ogs.evalsub$ and $ogs.evalnf$ are specified w.r.t. _strong bisimilarity_, with
  _extensional equality_ at the leaves (which in both cases are normal forms).
]kw.cls th ogs.submachine th M kw.whr \
    pat(
      ogs.evalsub th {Gamma th Delta} th (c cl C th Gamma) th (sigma cl Gamma asgn(V) Delta) \
        quad cl M.ogs.eval th c[sigma] itree.eq (M.ogs.eval th c itree.bind kw.fun th n |-> M.ogs.eval th (ogs.emb th n)[sigma]),
      ogs.appsub th {Gamma th Delta th alpha} th (v cl V th Gamma th alpha) th o th gamma th (sigma cl Gamma asgn(V) Delta) \
        quad cl M.ogs.apply th v[sigma] th o th gamma[sigma] approx (M.ogs.apply th v th o th gamma)[sigma],
      ogs.evalnf th {Gamma} th (n cl ctx.norm^(#h(0.15em) O)_V th Gamma) \
        quad cl M.ogs.eval th (ogs.emb th n) itree.eq itree.ret th n
    ) $
] <def-machine-resp-sub>

Our statement of the law $ogs.appsub$ should be relatively straightforward.
However, $ogs.evalsub$ is a bit more tricky. Indeed, there is no hope of
stating a simple law such as
$ M.ogs.eval th c[gamma] itree.eq (M.ogs.eval th c)[c] $

since it is a well-known fact that normal forms are never stable by
substitution. Instead, after evaluating $c$ to a normal form $n$, we need to
embed it into configurations, substitute it _and then_ evaluate the result
again. The last law $ogs.evalnf$ should have a clear meaning: it justifies
calling normal forms _normal_ as it requires them to be stable under
evaluation #guil["it requires them to be already fully evaluated" plutôt que stable under evaluation ?]. Although, it might be a bit surprising to find it in this package
since it does not seem to have anything to do with substitution. The reason
for including it here, is that assuming $ogs.submachine th M$, although there
is no hope of defining substitution of normal forms, we can show that the family
$Gamma |-> delay.t th (ctx.norm^(#h(0.15em) O)_V th Gamma)$ is a substitution
module over values, crucially depending on $ogs.evalnf$ for proving the
substitution identity law.

$ de("NfSub") cl sub.mod_V th (delay.t compose ctx.norm^(#h(0.15em) O)_V) \
  de("NfSub") := \ pat(
    sub.act th u th sigma := u itree.bind kw.fun th n |-> M.ogs.eval th (ogs.emb th n)[sigma],
    ..
  ) $

#guil[Est-ce-que tu peux donner plus de détails sur le lien entre
eval-nf et la substitution identity law ?]

We are now done with the core hypotheses, but there are two more technical
hypotheses we must require.

*Decidable Variables* #sym.space.quad The argument for the eventual guardedness
of the composition equation requires us to case-split on whether or not some
given value is a variable. "Being a variable" can be neatly expressed as
belonging to the image of $sub.var$, in other words, exhibiting an element of
the fiber of $sub.var$ over some value.

$ sub.isvar th {Gamma th alpha} cl V th Gamma th alpha -> base.Type \
  sub.isvar th v := subs.fiber th sub.var th v $

Then, our case-splitting requirement can be formalized by asking that
$sub.isvar th v$ is decidable for all $v$. We define the standard decidability
data type as follows.

$ kw.dat base.decidable th (X cl base.Type) cl base.Type kw.whr \
  pat(
    base.yes th (x cl X),
    base.no th (r cl X -> base.bot)
  ) $


We package this into a typeclass, together with some additional requirements
making $sub.isvar$ well-behaved.

#definition[Decidable Variables][
  Assume a scope structure $ctx.scope_T th S$ and a family $V cl base.Type^(S,T)$
  with a pointed renaming structure $sub.pren th V$, _$V$ has decidable variables_
  if there is an instance to the following typeclass.

  $ kw.cls sub.decvar th V kw.whr \
    pat(
      sub.isvardec th {Gamma th alpha} th (v cl V th Gamma th alpha) cl base.decidable th (sub.isvar th v),
      sub.isvarirr th {Gamma th alpha} th {v cl V th Gamma th alpha} th (p_1 th p_2 cl sub.isvar th v) cl p_1 = p_2,
      sub.isvarren th {Gamma th Delta th alpha} th (v cl V th Gamma th alpha) th (rho cl Gamma ctx.ren Delta) cl sub.isvar th v[rho] -> sub.isvar th v
    ) $
] <def-dec-var>

$sub.isvarirr$ is quite powerful, it states that there is at most one way to
show that a value is a variable. Assuming unicity of identity proofs (axiom K)
on values, this is equivalent to the more common fact that $sub.var$ is
injective. The second law, $sub.isvarren$, validates the fact that if the
renaming of a value is a variable, then it must have been a variable in the
first place. Note that we do not need to ask the reverse implication: since
$(sub.var th i)[rho] approx sub.var th (rho th i)$, we can deduce that
$sub.isvar th v -> sub.isvar th v[rho]$. In fact, thanks to $sub.isvarirr$, we
can even deduce that these two implications are inverse to each other.

*Finite Redexes* #sym.space.quad The last technical hypothesis is perhaps the
most mysterious. To me it was, at least, and I was quite surprised when I
realized I could _still_ not conclude the eventual guardedness proof of the
composition equation.

In essence, what interlaced positions and telescopic environment buy us, is a
bound on the number of what we call _chit-chats_. These chit-chats are
synchronizations events during the composition, for which the exchanged move
$(i ctx.cute o)$ targets a variable $i$ that is associated in the opponent's
environment to a value which happens to be some variable $j$. As such, the
composition continues with some new active configuration $M.ogs.apply th
(sub.var th j) o th gamma$, which by $ogs.evalnf$ evaluates instantly to
$((j ctx.cute o), gamma)$. Hence, in case of such a chit-chat, the original
move $(i ctx.cute o)$ is immediately "bounced" #guil[copycat ?] back to the original player with
the move $(j ctx.cute o)$. Recalling that to prove eventual guardedness, the
goal is to find a #itree.tauF move in the reduction of the active configuration,
it is quite nice to be able to limit the number of such bounces.

As such, we can assume that after some amount of chit-chat, the active
configuration will be of the form $M.ogs.apply th v th o th gamma$, where $v$
_is not_ a variable. At this point, we are however completely stuck without any
further hypothesis. The natural thing to do would be to postulate that such a
configuration $M.ogs.apply th v th o th gamma$ where $v$ is not a variable
has a _redex_, in the sense that its evaluation necessarily starts with a
#itree.tauF move, i.e., a reduction step. This requirement would intuitively
make sense: $o$ typically stands for an elimination, so applying an elimination
to something which is not a variable should yield a redex. Alas, I realized
that this was severely restricting the language machine. Even the
simply-typed #short.llc fails this hypothesis!
#margin-note[
  To be completely honest, the particular example of the #short.llc can be made
  to verify the redex hypothesis by designing the observations more smartly,
  but still, we would like to have maximal latitude to design the language
  machine as we wish.
] We thus need a weaker hypothesis.

Concretely the statement of the hypothesis is quite technical, but the idea is
relatively simple, we simply ask for a bound on the number of consecutive times
that the redex hypothesis can fail. As such, although the configuration may not
have a redex _right now_, we know that after some more composition steps we will
eventually find one.

Technically, it is formulated as follows. If the redex hypothesis fails, it
means that the configuration $M.ogs.apply th v th o th gamma$ happens to be
some normal form which will thus immediately trigger a new message, say $(i,
o')$. This defines a relation $o' ogs.badinst o$ on observations. We then require
that this relation is well-founded.

#definition[Finite Redexes][
  Assume a scope structure $ctx.scope_T th S$, a binding family $O cl ctx.bfam
  th S th T$, two families $V$, $C$, and a language machine $M cl ogs.machine
  th O th V th C$. Pose $tilde(O) := (alpha cl T) base.prod O.ctx.Oper th alpha$
  and define the _redex failure relation_
  $ar ogs.badinst ar cl rel.rel th tilde(O) th tilde(O)$ as follows.

  #inferrule(
    ($i cl Gamma ctx.var alpha_1$,
     $o_1 cl O.ctx.Oper th alpha_1$,
     $gamma_1 cl O.ctx.dom th o_1 asgn(V) Gamma$,
     $v cl V th Gamma th alpha_2$,
     $o_2 cl O.ctx.Oper th alpha_2$,
     $gamma_2 cl O.ctx.dom th o_2 asgn(V) Gamma$,
     $H_1 cl sub.isvar th v -> base.bot$,
     $H_2 cl M.ogs.eval th (M.ogs.apply th v th o_2 th gamma) itree.eq itree.ret th ((i ctx.cute o_1), gamma_1)$
    ),
    $ogs.badc th H_1 th H_2 cl o_1 ogs.badinst o_2$
  )

  Then, the machine _$M$ has finite redexes_ if the redex failure relation is well-founded.

  $ ogs.finred th M := de("WellFounded") th ogs.badinst $
] <def-finite-redex>

#remark[
  Recall that in type theory, well-foundedness is defined in terms of inductive _accessibility_.

  $ kw.dat de("Acc") th {X} th (R cl rel.rel th X th X) th (a cl X) cl base.Type \
    pat1(cs("acc") cl (forall th {b} -> R th b th a -> de("Acc") th R th b) -> de("Acc") th R th a
    ) \
    \
    de("WellFounded") th {X} cl rel.rel th X th X -> base.Type \
    de("WellFounded") th R := (a cl X) -> de("Acc") th R th a $

  Then, well-founded induction is simply obtained by induction on the accessibility proof.

]

We are finally in a position to state the correctness theorem.

#theorem[OGS Correctness][
  Assuming
  - a scope structure $ctx.scope_T th S$,
  - a binding family $O cl ctx.bfam th S th T$,
  - a substitution monoid of values $V cl base.Type^(S,T)$ with decidable variables,
  - a substitution module over values of configurations $C cl base.Type^S$,
  - a language machine $M cl ogs.machine th O th V th C$ which respects substitution
    and which has finite redexes,
  /*
  - a family $V cl base.Type^(S,T)$ such that $sub.mon th V$ and $sub.decvar th V$,
  - a family $C cl base.Type^S$ such that $sub.mod_V th C$,
  - a language machine $M cl ogs.machine th O th V th C$ such that $ogs.submachine th M$ and $ogs.finred th M$,
  */
  then, for any final
  scope $Omega cl S$, the OGS interpretation is correct with respect to
  substitution equivalence at $Omega$, i.e., the following property holds.

  $ forall th {Gamma} th (c_1 th c_2 cl C th Gamma) -> ogsinterpA(c_1) itree.weq ogsinterpA(c_2) -> c_1 ogs.subeq c_2 $
] <thm-correctness>

#peio[wip finir un peu moins abrupte]




/*
TODO: utiliser cette remarque sur la compo générale (ouverte)
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
*/

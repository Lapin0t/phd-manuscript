#import "/lib/all.typ": *
#pagebreak()

#v(0.5fr)

== Abstract

This thesis constructs an operational game semantics (OGS) model entirely formally
in the language of type theory, and proves it correct w.r.t. observational
equivalence. An accompagnying code artifact implements these results using the
Rocq Prover. The OGS model construction and correctness proof are generic over
an axiomatized programming language and its evaluator. The axiomatization in the style of
abstract machines handles simply-typed languages with arbitrary control-flow
effects (non-termination, call/cc), of which we provide three examples:
Jump-with-Argument, polarized #short.uuc with recursive types, and
pure untyped #short.llc under weak head reduction. The OGS model construction
builds upon a notion of game by #nm[Levy] & #nm[Staton], and strategies are
represented coinductively by generalizing the definition of interaction tree by
#nm[Xia] _et al._ to indexed containers. We further introduce a novel unique
fixed point construction for eventually guarded equation systems on (indexed)
interaction trees, as well as a generic normal form bisimulation model
construction and its correctness proof.

#v(1fr)

#heading(level: 2, outlined: false)[Résumé]

Cette thèse construit un modèle de sémantique des jeux opérationelle (OGS) de manière
entièrement formelle dans le langage de la théorie des types, et prouve
sa correction vis-à-vis de l'équivalence observationelle. Un artefact de code
implémente ces résultats en utilisant le Rocq Prover.
La construction du modèle d'OGS et sa correction sont génériques par
rapport à un langage de programmation axiomatisé et à son évaluateur. L'axiomatisation
dans le style des machines abstraites capture les langages simplement typés avec
effets de contrôle arbitraires (non-terminaison, call/cc), et nous en
présentons trois exemple: Jump-with-Argument, #box[#mumutl\-calcul] polarisé avec types
récursifs, et #box[#sym.lambda\-calcul] pur non-typé en réduction de tête faible. La
construction du modèle d'OGS se base sur une notion de jeu de #nm[Levy] & #nm[Staton], et
les stratégies sont représentées coinductivement en généralisant la définition
d'arbre d'intéraction de #nm[Xia] _et al._ aux conteneurs indexés. Nous
introduisons également une nouvelle construction de point fixe
pour les systèmes d'équations ultimement gardés sur les arbres d'intéraction
(indexés), ainsi qu'une construction générique d'un modèle de bisimulation de
forme normale et sa preuve de correction.

#v(1fr)

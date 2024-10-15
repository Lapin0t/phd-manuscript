#let big(size: 14pt, it) = block(text(size: size, weight: "bold", it))

#page(numbering: none, margin: 0mm, {
  set text(font: "Latin Modern Sans", size: 9.5pt)

  stack(dir: ltr,
    // gray margin
    box(
      height: 100%,
      width: 25%,
      fill: color.luma(80%)
    ),
    // text area
    box(height: 100%, width: 75%, {
      align(right, box(inset: (right: 0.5cm), image("/images/logo-usmb-bw.png", width: 7cm)))

      block(inset: (top: 0cm, rest: 0.5cm), [
        #big[THÈSE]
        Pour obtenir le grade de
        #big[DOCTEUR DE L'UNIVERSITÉ SAVOIE MONT BLANC]
        Spécialité: Mathématiques et Informatique \
        Arrêté ministériel: 25 Mai 2016

        #v(1fr)

        Présentée par
        #big[Peio BORTHELLE]

        #v(1fr)

        Thèse dirigée par *M. Tom HIRSCHOWITZ* et \
        codirigée par *M. Guilhem JABER*,

        #v(0.3fr)

        préparée au sein du *LAMA* \
        dans l'École Doctorale *MSTII*.

        #v(1fr)

        #big(size: 17pt)[
          Sémantique des Jeux Operationelle \
          en Théorie des Types
        ]

        #v(1fr)

        Thèse soutenue publiquement le 1#super[er] Janvier 2025 \
        devant le jury composé de#sym.space.punct: \
        #par(leading: 0.5em, [
          *M. David MONNIAUX* \
          Directeur de Recherche, Université Grenoble Alpes, Président \
          *Mme. Stephanie WEIRICH* \
          Professeure, University of Pennsylvania, Rapportrice \
          *M. Damien POUS* \
          Directeur de Recherche, CNRS, ENS Lyon, Rapporteur \
          *M. Hugo HERBELIN* \
          Directeur de Recherche, INRIA, Université Paris Cité, Examinateur\
          *Mme. Kathrin STARK* \
          Professeure Assistante, Heriot-Watt University, Examinatrice\
          *M. Pierre-Évariste DAGAND* \
          Chargé de Recherche, CNRS, Université Paris Cité, Examinateur\
          *M. Paul Blain LEVY* \
          Maître de Conférence, University of Birmingham, Examinateur\
          *M. Yannick ZAKOWSKI* \
          Chargé de Recherche, INRIA, ENS Lyon, Invité (Co-encadrant)\
        ])

        #v(0.3fr)
      ])
    })
  )
})

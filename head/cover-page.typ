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

        Thèse dirigée par *M. Tom HIRSCHOWITZ*

        #v(0.3fr)

        préparée au sein du *LAMA* \
        dans l'École Doctorale *MSTII*.

        #v(1fr)

        #big(size: 17pt)[
          Sémantique des Jeux Operationelle \
          en Théorie des Types
        ]

        #v(1fr)

        Thèse soutenue publiquement le *12 Mars 2025* \
        devant le jury composé de#sym.space.punct: \
        #par(leading: 0.5em, [
          *M. David MONNIAUX* \
          Directeur de Recherche, CNRS, Université Grenoble Alpes, Président \
          *Mme. Stephanie WEIRICH* \
          Distinguished Professor, University of Pennsylvania, Rapportrice \
          *M. Damien POUS* \
          Directeur de Recherche, CNRS, ENS de Lyon, Rapporteur \
          *M. Pierre-Évariste DAGAND* \
          Chargé de Recherche, CNRS, Université Paris Cité, Examinateur\
          *M. Hugo HERBELIN* \
          Directeur de Recherche, INRIA, Université Paris Cité, Examinateur\
          *M. Paul Blain LEVY* \
          Senior Lecturer, University of Birmingham, Examinateur\
          *Mme. Kathrin STARK* \
          Assistant Professor, Heriot-Watt University, Examinatrice\
          *M. Tom HIRSCHOWITZ* \
          Directeur de Recherche, CNRS, Université Savoie Mont Blanc, Directeur de thèse\
          *M. Guilhem JABER* \
          Maître de Conférences, Nantes Université, Invité, Co-encadrant de thèse\
          *M. Yannick ZAKOWSKI* \
          Chargé de Recherche, INRIA, ENS de Lyon, Invité, Co-encadrant de thèse\
        ])

        #v(0.3fr)
      ])
    })
  )
})

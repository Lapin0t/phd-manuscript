//#import "@preview/scholarly-epfl-thesis:0.1.0": template, front-matter, main-matter, back-matter
#import "template.typ": template, front-matter, main-matter, back-matter

#show: template.with(
    title: [WIP PhD],
    author: "Peio Borthelle",
)

#set page(numbering: none)

#include "head/cover-page.typ"
#pagebreak()
#pagebreak()
#include "head/dedication.typ"

#show: front-matter

/*
#include "head/acknowledgements.typ"
#include "head/preface.typ"
#include "head/abstracts.typ"
*/

#outline(title: "Contents")
#outline(title: "List of Figures", target: figure.where(kind: image))
#outline(title: "List of Tables", target: figure.where(kind: table))
// #outline(title: "List of Listings", target: figure.where(kind: raw))

#show: main-matter

#include "main/01_introduction.typ"
#include "main/02_games.typ"
#include "main/03_substitution.typ"
#include "main/04_ogs.typ"
#include "main/05_soundness.typ"

#show: back-matter

#include "tail/instances.typ"
#include "tail/biblio.typ"
// #include "tail/cv/cv"

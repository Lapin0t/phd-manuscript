#import "/lib/theorems.typ": thmrules
#show: thmrules

#import "lib/template.typ": template, front-matter, main-matter, back-matter
#show: template.with(
  title: [Generic Operational Game Semantics in Type Theory],
  author: "Peio Borthelle",
)

#show: front-matter

#include "head/cover-page.typ"
#pagebreak()
#pagebreak()
#include "head/dedication.typ"

#outline(title: "Contents")
//#outline(title: "List of Figures", target: figure.where(kind: image))
//#outline(title: "List of Tables", target: figure.where(kind: table))

#show: main-matter

#include "main/01_introduction.typ"
#include "main/02_games.typ"
#include "main/03_substitution.typ"
#include "main/04_ogs.typ"
#include "main/05_soundness.typ"
#include "main/07_nf_bisim.typ"
#include "main/06_instances.typ"
#include "main/08_conclusion.typ"

#show: back-matter

#include "tail/biblio.typ"

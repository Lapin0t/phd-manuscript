#import "/lib/all.typ": *

#pagebreak(to: "odd")
#counter(page).update(1)

#v(1fr)

#align(center)[
    #set text(size: 19pt, weight: "bold")
    Operational Game Semantics in Type Theory
]

#v(0.2fr)

#align(center + horizon)[
    #set text(size: 13pt)
    Peio Borthelle
]

#v(2fr)

#pagebreak()

#v(1fr)

#align(left)[
  Sémantique des jeux operationelle en théorie des types \
  #sym.copyright~Peio Borthelle, 2024 \
  Cette oeuvre est distribué sous la licence
  #link("https://creativecommons.org/licenses/by-nc-sa/4.0/ ")[CC BY-NC-SA 4.0]
  ~#box(move(dy: 0pt, image("/images/cc.svg", height: 0.7em)))
  #box(move(dy: 0pt, image("/images/by.svg", height: 0.7em)))
  #box(move(dy: 0pt, image("/images/nc.svg", height: 0.7em)))
  #box(move(dy: 0pt, image("/images/sa.svg", height: 0.7em))) \
  \
  This work is typeset using #link("https://typst.app/")[Typst] 0.12 \
]

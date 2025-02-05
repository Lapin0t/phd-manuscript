#v(1fr)

#let cc-one(path) = box(move(dy: 0pt, image(path, height: 0.7em)))
#let cc-all() = [
  #cc-one("/images/cc.svg")
  #cc-one("/images/by.svg")
  #cc-one("/images/nc.svg")
  #cc-one("/images/sa.svg")
]

#align(left)[
  Sémantique des jeux operationelle en théorie des types \
  #sym.copyright~Peio Borthelle, 2024 \
  Cette thèse est distribuée sous la licence
  #link("https://creativecommons.org/licenses/by-nc-sa/4.0/")[
    CC BY-NC-SA 4.0
  ]~#cc-all() \
  \
  Cette thèse a été composée en #link("https://typst.app/")[Typst] avec les
  polices EB Garamond, New Computer Modern Math, Latin Modern Sans et Fira
  Code.
]

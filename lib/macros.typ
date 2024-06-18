#import "@preview/ctheorems:1.0.0": thmplain

#let my_thm(head) = return thmplain(
  "theorem",
  head,
  inset: 0em,
  base: "heading",
  base_level: 1,
)

#let theorem = my_thm("Theorem")
#let lemma = my_thm("Lemma")
#let definition = my_thm("Definition")
#let example = my_thm("Example")

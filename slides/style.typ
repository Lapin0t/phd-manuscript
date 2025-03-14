#import "@preview/touying:0.5.5": *
#import "metropolis.typ": *

#import "@preview/numbly:0.1.0": numbly

#let colors = (
  primary: rgb("#e25c4b"),           // redish
  primary-light: rgb("#ccb2af"),     // redish-light
  secondary: rgb("#2c1d4c"),         // blueish
  neutral-lightest: rgb("#fafafa"),  // background
  neutral-dark: rgb("#2c1d4c"),
  neutral-darkest: rgb("#2c1d4c"),
)

#let my-theme(doc) = {

  show: metropolis-theme.with(
    aspect-ratio: "4-3",
    footer: none,
    config-info(
      title: box(width: 120%)[Operational Game Semantics in Type Theory],
      subtitle: [PhD Defense],
      author: [Peio Borthelle],
      date: [March 12#super[th], 2025],
      institution: [Université Savoie Mont Blanc --- LAMA],
      logo: [],
    ),
    config-colors(..colors),
  )

  set list(marker: [•])

  set heading(numbering: numbly("{1}.", default: "1.1"))
  set text(font: "Inria Sans", size: 23pt, weight: "light")
  show math.equation: set text(font: ("Inria Sans", "New Computer Modern Math",), weight: "light", features: ("cv01",))

  show outline.entry: it => {
    v(12pt, weak: true)
    it.body
  }

  doc
}

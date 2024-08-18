#import "@preview/hydra:0.4.0": hydra
#import "/lib/macros.typ": *

#let in-outline = state("in-outline", false)
#let flex-caption(long, short) = context {
  if in-outline.get() { short } else { long }
}

#let header() = context {
  let hyd = hydra()
  if hyd == none { return [] }

  let title = block(inset: 0.3cm, hyd)
  let num = block(inset: 0.3cm, counter(page).display())

  if calc.even(here().page()) {
    place(top + left, dx: -2.6cm, dy: 0cm,
      block(height: page.margin.top/2, align(bottom, title))
    )
    place(top + left, dx: -2.6cm, dy: 0cm,
      line(length: 1.6cm, angle: 90deg)
    )
    place(top + left, dx: -4.6cm, dy: 0cm,
      block(height: page.margin.top/2, width: 2cm, align(bottom + right, num))
    )
  } else {
    place(top + right, dx: 2.6cm, dy: 0cm,
      block(height: page.margin.top/2, align(bottom, title))
    )
    place(top + right, dx: 2.6cm, dy: 0cm,
      line(length: 1.6cm, angle: 90deg)
    )
    place(top + right, dx: 4.6cm, dy: 0cm,
      block(height: page.margin.top/2, width: 2cm, align(bottom + left, num))
    )
  }
}

#let front-matter(it) = {
  set page(numbering: "i")
  set heading(numbering: none)
  counter(page).update(1)
  it
}

#let main-matter(it) = {
  set page(
    margin: (
      bottom: 2.17cm,
      top: 3.51cm,
      inside: 2.1835cm,
      outside: 2.1835cm + 4.4cm,
    ),
    numbering: "1",
    header: header(),
  )
  set heading(numbering: "1.1")
  counter(page).update(1)
  counter(heading).update(0)
  it
}

#let back-matter(it) = {
  set heading(numbering: "A.1", supplement: [Appendix])
  counter(heading.where(level: 1)).update(0)
  counter(heading).update(0)
  it
}

#let template(
  title: [Your Title],
  author: "Author",
  date: none,
  body,
) = {
  // GENERAL
  set document(
    title: title,
    author: author,
    date: if date != none { date } else { auto },
  )
  set text(font: ("EB Garamond"), size: 9.5pt, weight: "regular", number-width: "proportional")
  set page(
    width: 189mm,
    height: 246mm,
    margin: (
      bottom: 2.17cm,
      top: 3.51cm,
      inside: 2.1835cm,
      outside: 2.1835cm,
    ),
    numbering: "1",
    number-align: right,
    footer: [],
  )

  // HEADINGS
  set heading(numbering: "1.1", supplement: "§" + h(-0.2em))
  show heading: set text(hyphenate: false)
  show heading: it => v(2.5em, weak: true) + it + v(2em, weak: true)

  show heading.where(level: 1): it => context {
    pagebreak(to: "odd")
    set text(size: 22pt, weight: "bold")

    if heading.numbering == none {
       block(it.body + v(1em))
    } else {
      let title = block(inset: 0.3cm, align(right, it.body))
      let deco = line(length: page.margin.top, angle: -90deg)
      let cnt = counter(heading.where(level: 1)).display()
      let num = block(inset: 0.3cm, text(size: 60pt, cnt))

      layout(size => {
        let title-size = measure(block(width: size.width, title))
        let num-size = measure(block(width: size.width, num))

        place(top + right, dy: -title-size.height, title)
        place(top + right, dx: 0.3cm, deco)
        place(top + right, dx: 0.6cm + num-size.width, dy: -num-size.height, num)
        v(2em)
      })
    }
  }

  // OUTLINE
  set outline(indent: auto, fill: repeat([#h(2.5pt) . #h(2.5pt)]))

  show outline: it => {
    in-outline.update(true)
    set heading(outlined: true)
    it
    in-outline.update(false)
  }

  show outline.entry: it => {
    // only apply styling if we're in the table of contents (not list of
    // figures or list of tables, etc.)
    if (it.element.func() == heading and it.level == 1) {
      v(1.5em, weak: true)
      strong(it)
    } else {
      it
    }
  }

  // PARAGRAPH
  set par(leading: 0.7em, justify: true, linebreaks: "optimized")
  show par: set block(spacing: 1.35em)

  // EQUATIONS
  set math.equation(numbering: none)
  show math.equation.where(block: true): it => {
    set align(left)
    pad(left: 1.5em, it)
  }
  show math.equation: set text(font: ("EB Garamond", "New Computer Modern Math",), features: ("cv01",))

  // FIGURES
  set figure(numbering: n => {
    let h1 = counter(heading).get().first()
    numbering("1.1", h1, n)
  }, gap: 1.5em)
  set figure.caption(separator: [ -- ])

  show figure.caption: it => {
    if it.kind == table {
      align(center, it)
    } else {
      align(left, it)
    }
  }
  show figure.where(kind: table): it => {
    set figure.caption(position: top)
    set block(breakable: true)
    it
  }
  set table(stroke: none)

  // RAW BLOCKS
  show raw: set text(font: ("FiraCode Nerd Font",), size: 9pt)
  show raw.where(block: true): block.with(inset: (x: 5pt))

  // LINKS
  show link: it => underline(offset: 1.5pt, stroke: (dash: "densely-dotted"), it)

  // NUMBERED LISTS
  show enum: set enum(numbering: "(1)")

  // REPLACEMENTS
  show "Agda": txsc("Agda")
  show "Coq": txsc("Coq")
  show "OGS": txsc("ogs")
  show "coq-coinduction": txtt("coq-coinduction")

  body
}

#import "@preview/hydra:0.5.1": hydra
#import "/lib/all.typ": *

#let in-outline = state("in-outline", false)
#let flex-caption(long, short) = context {
  if in-outline.get() { short } else { long }
}

#let header-post() = context {
  let hyd = hydra()
  if hyd == none { return [] }

  let title = block(inset: 0.3cm, hyd)
  let num = block(inset: 0.3cm, counter(page).display())

  if calc.even(here().page()) {
    place(top + left, dx: 0.7cm, dy: 0cm,
      block(height: page.margin.top/2, align(bottom, title))
    )
    place(top + left, dx: 0.7cm, dy: 0cm,
      line(length: 1.6cm, angle: 90deg)
    )
    place(top + left, dx: -1.3cm, dy: 0cm,
      block(height: page.margin.top/2, width: 2cm, align(bottom + right, num))
    )
  } else {
    place(top + right, dx: -0.7cm, dy: 0cm,
      block(height: page.margin.top/2, align(bottom, title))
    )
    place(top + right, dx: -0.7cm, dy: 0cm,
      line(length: 1.6cm, angle: 90deg)
    )
    place(top + right, dx: 1.3cm, dy: 0cm,
      block(height: page.margin.top/2, width: 2cm, align(bottom + left, num))
    )
  }
}

#let header() = context {
  let hyd = hydra()
  if hyd == none { return [] }

  let pg = here().page()
  let is-start-chapter = query(heading.where(level:1))
    .map(it => it.location().page())
    .contains(pg)
  if not state("content.switch", false).get() or is-start-chapter {
    return []
  }

  let title = block(inset: 0.3cm, hyd)
  let num = block(inset: 0.3cm, counter(page).display())

  if calc.even(here().page()) {
    place(top + left, dx: -3.7cm, dy: 0cm,
      block(height: page.margin.top/2, align(bottom, title))
    )
    place(top + left, dx: -3.7cm, dy: 0cm,
      line(length: 1.6cm, angle: 90deg)
    )
    place(top + left, dx: -5.7cm, dy: 0cm,
      block(height: page.margin.top/2, width: 2cm, align(bottom + right, num))
    )
  } else {
    place(top + right, dx: 3.7cm, dy: 0cm,
      block(height: page.margin.top/2, align(bottom, title))
    )
    place(top + right, dx: 3.7cm, dy: 0cm,
      line(length: 1.6cm, angle: 90deg)
    )
    place(top + right, dx: 5.7cm, dy: 0cm,
      block(height: page.margin.top/2, width: 2cm, align(bottom + left, num))
    )
  }
}

/*
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
*/

#let front-matter(it) = {
  set page(numbering: "i", footer: context {
    if counter(page).get().at(0) < 3 { return [] }
    if not state("content.switch", false).get()  { return [] }
    align(center, counter(page).display("i"))
  })
  /*set page(footer: context {
    let cnt = counter(page).display("i")
    if calc.even(here().page()) {
        cnt + h(1fr)
    } else {
        h(1fr) + cnt
    }
  })*/
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
    footer: [],
  )
  set heading(numbering: "1.1")
  //set heading(numbering: (n1, ..x) => numbering("1.1", n1 - 1, ..x))
  counter(page).update(1)
  counter(heading).update(0)
  it
}

#let back-matter(it) = {
  set heading(numbering: "A.1", supplement: [Appendix])
  set page(header: context header-post())
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
      top: 2.17cm,
      inside: 2.1835cm,
      outside: 2.1835cm,
    ),
    numbering: "1",
    number-align: right,
    footer: [],
  )

  // HEADINGS
  set heading(numbering: "1.1")
  set heading(supplement: box("§" + h(-0.2em)))
  show heading.where(level: 1): set heading(supplement: "Ch.")
  show heading: set text(hyphenate: false)
  show heading: it => v(2.5em, weak: true) + it + v(2em, weak: true)

  show heading.where(level: 1): it => context {
    state("content.switch").update(false)
    pagebreak(to: "odd")
    state("content.switch").update(true)

    set text(size: 22pt, weight: "bold")

    if heading.numbering == none {
       block(it.body + v(1em))
    } else {
      let title = block(inset: 0.3cm, align(right, it.body))
      let deco = line(length: page.margin.top, angle: -90deg)
      let cnt = counter(heading.where(level: 1)).display()
      let num = block(inset: 0.3cm, text(size: 60pt, cnt))

      layout(size => {
        let title-size = measure(title)
        let num-size = measure(num)

        place(top + right, dy: -title-size.height, title)
        place(top + right, dx: 0.3cm, deco)
        place(top + right, dx: 0.6cm + num-size.width, dy: -num-size.height, num)
        v(2em)
      })
    }
  }

  // OUTLINE
  set outline(indent: auto)
  set outline.entry(fill: repeat([#h(2.5pt) . #h(2.5pt)]))

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
  set par(leading: 0.7em, justify: true, linebreaks: "optimized", spacing: 1.35em)

  // EQUATIONS
  set math.equation(numbering: none)
  show math.equation.where(block: true): it => {
    set align(left)
    pad(left: 1.5em, it)
  }
  show math.equation.where(block: false): box
  show math.equation: set text(font: ("EB Garamond", "New Computer Modern Math",), features: ("cv01",))
  //show math.equation: set block(breakable: true)


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
  show raw: set text(font: ("Fira Mono",), size: 9pt)
  show raw.where(block: true): block.with(inset: (x: 5pt))

  // LINKS
  show link: it => underline(offset: 1.5pt, stroke: (dash: "densely-dotted"), it)

  // NUMBERED LISTS
  show enum: set enum(numbering: "(1)")

  // REPLACEMENTS
  show "Agda": txsc("Agda")
  show "Coq": txsc("Coq") // txsc("Rocq")
  show "Rocq": txsc("Rocq")
  show "OGS": txsc("Ogs")
  show "NF": txsc("Nf")
  show "JWA": txsc("Jwa")
  show "CBPV": txsc("Cbpv")
  show "coq-coinduction": txtt("coq-coinduction")

  body
}

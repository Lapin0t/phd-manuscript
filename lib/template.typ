#import "@preview/hydra:0.4.0": hydra

// Place content with relative to top-left of physical paper.
//
// Hack works by placing an invisible anchor and getting its location,
// enabling to find its absolute location.
// Shout-out to https://github.com/ntjess/typst-drafting
#let absolute-place(dx: 0em, dy: 0em, content) = {
  [ #metadata("absolute-place") <absolute-place> ]
  style(styles => {
    let dx = measure(h(dx), styles).width
    let dy = measure(v(dy), styles).height
    context {
      let pos = query(<absolute-place>).last().location().position()
      place(dx: -pos.x + dx, dy: -pos.y + dy, content)
    }
  })
}

// The `in-outline` mechanism is for showing a short caption in the list of figures
// See https://sitandr.github.io/typst-examples-book/book/snippets/chapters/outlines.html#long-and-short-captions-for-the-outline
#let in-outline = state("in-outline", false)
#let flex-caption(long, short) = context {
  if in-outline.get() {
    short
  } else {
    long
  }
}

#let front-matter(body) = {
  set page(numbering: "i")
  counter(page).update(1)

  set heading(numbering: none)
  /*show heading.where(level: 1): it => {
    it
    v(6%, weak: true)
  }*/

  body
}

#let header() = context {
  let hyd = hydra()
  if hyd == none { return [] }

  let title = block(inset: 0.3cm, hyd)
  let num = block(inset: 0.3cm, counter(page).display())
  //layout(size => {
    //let num-size = measure(block(height: size.height, width: size.width, num))

    if calc.even(here().page()) {
      place(top + left, dx: -2.6cm, dy: 0cm, block(height: page.margin.top/2, align(bottom, title)))
      place(top + left, dx: -2.6cm, dy: 0cm, line(length: 1.6cm, angle: 90deg))
      place(top + left, dx: -4.6cm, dy: 0cm, block(height: page.margin.top/2, width: 2cm, align(bottom + right, num)))
    } else {
      place(top + right, dx: 2.6cm, dy: 0cm, block(height: page.margin.top/2, align(bottom, title)))
      place(top + right, dx: 2.6cm, dy: 0cm, line(length: 1.6cm, angle: 90deg))
      place(top + right, dx: 4.6cm, dy: 0cm, block(height: page.margin.top/2, width: 2cm, align(bottom + left, num)))
    }
  //})
}

#let main-matter(body) = {
  set page(
    margin: (
      bottom: 2.17cm,
      top: 3.51cm,
      inside: 2.1835cm,
      outside: 2.1835cm + 4.4cm,
    ),
  )

  set page(numbering: "1")
  set heading(numbering: "1.1")

  set page(header: header())

  counter(page).update(1)
  counter(heading).update(0)

  body
}

#let back-matter(body) = {
  set heading(numbering: "A.1", supplement: [Appendix])
  counter(heading.where(level: 1)).update(0)
  counter(heading).update(0)

  body
}

#let fill-line(left-text, right-text) = [#left-text #h(1fr) #right-text]

#let template(
  title: [Your Title],
  author: "Author",
  date: none,
  body,
) = {
  set document(
    title: title,
    author: author,
    date: if date != none { date } else { auto },
  )
  set text(font: ("EB Garamond"), size: 11pt, weight: "regular")
  set page(
    //paper: "uk-crown",
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
  )

  set page(footer: context {
    let side = if calc.even(here().page()) { left } else { right }
    align(side, counter(page).display())
  })

  // Configure paragraph properties.
  // Default leading is 0.65em.
  set par(leading: 0.7em, justify: true, linebreaks: "optimized")
  // Default spacing is 1.2em.
  show par: set block(spacing: 1.35em)

  show heading: it => {
    v(1.5em) + it + v(1em)
  }

  // Style chapter headings.
  show heading.where(level: 1): it => context {
    pagebreak(to: "odd")
    set text(size: 22pt, weight: "bold")
    //set text(font: ("EB Garamond"), size: 11pt, weight: "regular")
    if heading.numbering != none {
      layout(size => {
        let title = block(inset: 0.3cm, align(right, it.body))
        let deco = line(length: page.margin.top, angle: -90deg)
        let cnt = counter(heading.where(level: 1)).display()
        let num = block(inset: 0.3cm, text(size: 60pt, cnt))

        let title-size = measure(block(width: size.width, title))
        let num-size = measure(block(width: size.width, num))

        place(top + right, dy: -title-size.height, title)
        place(top + right, dx: 0.3cm, deco)
        place(top + right, dx: 0.6cm + num-size.width, dy: -num-size.height, num)
        v(2em)
      })
    } else {
       block(it.body + v(1em))
    }
  }

  set heading(numbering: "1.1")
  show heading: set text(hyphenate: false)

  // The `in-outline` is for showing a short caption in the list of figures
  // See https://sitandr.github.io/typst-examples-book/book/snippets/chapters/outlines.html#long-and-short-captions-for-the-outline
  show outline: it => {
    in-outline.update(true)
    // Show table of contents, list of figures, list of tables, etc. in the table of contents
    set heading(outlined: true)
    it
    in-outline.update(false)
  }

  // Indent nested entries in the outline.
  set outline(indent: auto, fill: repeat([#h(2.5pt) . #h(2.5pt)]))

  show outline.entry: it => {
    // Only apply styling if we're in the table of contents (not list of figures or list of tables, etc.)
    if it.element.func() == heading {
      if it.level == 1 {
        v(1.5em, weak: true)
        strong(it)
      } else {
        it
      }
    } else {
      it
    }
  }

  // Configure equation numbering.
  set math.equation(numbering: none)
  /*set math.equation(numbering: n => {
    let h1 = counter(heading).get().first()
    numbering("(1.1)", h1, n)
  })*/

  /* FIXME: disable in headings
  show math.equation: it => {
    set align(left)
    // Indent
    pad(left: 2em, it)
  }*/

  // FIXME: Has no effect?
  //set place(clearance: 2em)

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
    // Break large tables across pages.
    set block(breakable: true)
    it
  }
  set table(stroke: none)

  // Set raw text font.
  show raw: set text(font: ("Iosevka", "Fira Mono"), size: 9pt)

  // Display inline code in a small box that retains the correct baseline.
  // show raw.where(block: false): box.with(
  //   fill: luma(250).darken(2%), inset: (x: 3pt, y: 0pt), outset: (y: 3pt), radius: 2pt,
  // )

  // Display block code with padding.
  show raw.where(block: true): block.with(inset: (x: 5pt))

  body
}

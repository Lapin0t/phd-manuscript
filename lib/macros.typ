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

// Hack works by placing an invisible anchor and getting its location,
// enabling to find its absolute location.
// Shout-out to https://github.com/ntjess/typst-drafting
#let with-absolute-pos(fun) = {
  [ #metadata("with-absolute-pos") <with-absolute-pos> ]
  context {
    let target = selector(<with-absolute-pos>).before(here())
    let pos = query(target).last().location().position()
    fun(pos)
  }
}

#let margin-note(dy: 0em, content) = {
  let note = block(width: 4cm, {
    set text(size: 0.75em)
    content
  })
  box(with-absolute-pos(pos => {
    let dx = {
      if calc.even(here().page()) {
        page.margin.outside - 4.4cm
      } else {
        page.width - page.margin.outside + 0.4cm
      }
    }
    place(dx: dx - pos.x, dy: dy - 0.6em, note)
  }))
}

#let mcite(key, dy: 0em, ..args) = {
  cite(key, style: "/ieee-fullname.csl", ..args)
  margin-note(dy: dy, cite(key, style: "/ieee-author-title.csl", ..args))
}

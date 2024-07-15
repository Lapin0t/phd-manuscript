#import "@preview/ctheorems:1.0.0": thmplain

#let my_thm(head) = return thmplain(
  "theorem",
  head,
  radius: 0em,
  inset: (left: 1em, rest: 0.5em),
  stroke: (left: stroke(thickness: 1pt, dash: "loosely-dotted"), rest: 0pt),
  base: "heading",
  base_level: 1,
)

#let theorem = my_thm("Theorem")
#let lemma = my_thm("Lemma")
#let definition = my_thm("Definition")
#let example = my_thm("Example")
#let remark = my_thm("Remark")

// NOTES
#let peio(it) = box(inset: 0em, fill: color.rgb("#ff700080"))[P: #it]
#let tom(it)  = box(inset: 0em, fill: color.rgb("#ff700080"))[T: #it]
#let guil(it) = box(inset: 0em, fill: color.rgb("#ff700080"))[G: #it]
#let yann(it) = box(inset: 0em, fill: color.rgb("#ff700080"))[Y: #it]

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
    place(dx: dx - pos.x, dy: dy - 0.5em, note)
  }))
}

#let num-cite(key, ..args) = cite(key, style: "/ieee-fullname.csl", ..args)
#let text-cite(key, ..args) = cite(key, style: "/ieee-author-title.csl", ..args)

#let mcite(key, dy: 0em, ..args) = {
  num-cite(key, ..args)
  sym.zwj
  margin-note(dy: dy, text-cite(key, ..args))
}

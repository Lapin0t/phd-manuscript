#import "/lib/theorems.typ": thmplain, thmproof

#let my_thm(head) = return thmplain(
  "theorem",
  head,
  radius: 0em,
  stroke: (left: stroke(thickness: 1pt, dash: "loosely-dotted"), rest: 0pt),
  inset: (left: 1em, rest: 0em),
  base: "heading",
  base_level: 1,
)

#let proof = thmproof("proof", inset: (left: 1em, rest: 0em), "Proof")
#let theorem = my_thm("Theorem")
#let lemma = my_thm("Lemma")
#let definition = my_thm("Definition")
#let example = my_thm("Example")
#let remark = my_thm("Remark")

#let centering(it) = align(center, box(it))

// NOTES
#let note(it) = box(inset: 0em, outset: (top: 0.3em, bottom: 0.3em, rest: 0.1em),
                    fill: color.rgb("#ff700080"), it)
#let peio(it) = note[P: #it]
#let tom(it)  = note[T: #it]
#let guil(it) = note[G: #it]
#let yann(it) = note[Y: #it]
/*
#let peio(it) = []
#let tom(it)  = []
#let guil(it) = []
#let yann(it) = []
*/

#let mathpar(spacing: 1em, block: false, inset: 0em, ..it) = {
  it.pos()
    .map(x => box(inset: inset, math.equation(block: block, x)))
    .join(h(weak: true, spacing))
    //.join(sym.space)
}

#let to-array(it) = {
  if type(it) == array { it }
  else { (it,) }
}

/*
#let inferrule(hyp, conc, suppl: "") = {
  let fmt(it) = centering(mathpar(..to-array(it)))
  box(stack(
      box(fmt(hyp)),
      line(stroke: (thickness: 0.5pt, cap: "round")),
      box(fmt(conc)),
    ) + suppl)
}
*/
#let inferrule(hyp, conc, suppl: "") = {
  math.equation(block: true,
    math.frac(
      box(inset: 0.2em, centering(mathpar(..to-array(hyp)))),
      box(inset: 0.2em, centering(mathpar(..to-array(conc))))
    ) + suppl
  )
}

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

#let margin-note(mark: false, dy: 0em, content) = {
  let note = block(width: 4cm, {
    set text(size: 0.75em)
    if mark { box(move(dy: 0.2em, scale(150%, "* "))) }
    content
  })
  box({
    if mark { "*" }
    with-absolute-pos(pos => {
      let dx = {
        if calc.even(here().page()) {
          page.margin.outside - 4.4cm
        } else {
          page.width - page.margin.outside + 0.4cm
        }
      }
      place(dx: dx - pos.x, dy: dy - 0.5em, note)
    })
  })
}

#let num-cite(key, ..args) = cite(key, style: "/ieee-fullname.csl", ..args)
#let text-cite(key, ..args) = cite(key, style: "/ieee-author-title.csl", ..args)

#let mcite(key, dy: 0em, ..args) = {
  num-cite(key, ..args)
  sym.zwj
  margin-note(dy: dy, text-cite(key, ..args))
}

#let par-eqn(it) = {
  linebreak()
  box(width: 100%, inset: (y: 0.5em), it)
  linebreak()
}

#let full-page(content) = context {
  let dx = if calc.even(here().page()) { - 4.4cm } else { 0cm }
  align(left, move(dx: dx, block(width: 100% + 4.4cm, align(center, content))))
}

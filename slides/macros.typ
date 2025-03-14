#import "/style.typ": colors

#let alrt(x) = {
  set text(fill: colors.primary)
  x
}

#let bk(x) = {
  set text(fill: colors.secondary)
  x
}

#let blue(x) = text(fill: color.blue, x)
#let red(x) = text(fill: color.red, x)

#let centering(it) = align(center, box(it))

// typing colon
#let cl = h(0.2em) + ":" + h(0.3em)
// thin space (function application)
#let th = h(0.25em)
// binding argument
//#let ar = cop(move(sym.bracket.b, dy: -0.24em))

#let cnorm(x) = math.class("normal", x)
#let cbin(x) = math.class("binary", x)
#let cop = math.op

#let bold(it) = {
  set text(weight: "bold")
  it
}

#let small(it) = {
  set text(size: 0.9em)
  it
}

#let nm = smallcaps

#let txtt(it) = text(size: 0.8em, font: "Fira Mono", it)

#let to-array(it) = {
  if type(it) == array { it }
  else { (it,) }
}


#let mathpar(spacing: 1em, block: false, inset: 0em, ..it) = {
  it.pos()
    .map(x => box(inset: inset, math.equation(block: block, x)))
    .join(h(weak: true, spacing))
}

#let inferrule(hyp, conc, suppl: "") = {
  math.equation(block: true,
    math.frac(
      box(inset: 0.2em, centering(mathpar(..to-array(hyp)))),
      box(inset: 0.2em, centering(mathpar(..to-array(conc))))
    ) + suppl
  )
}

#let base = (
  type: txtt("Set"),
  delay: txtt("Delay"),
)

#let stlc = (
  tt: txtt("tt"),
  ff: txtt("ff"),
  fst: cop(txtt("fst")),
  snd: cop(txtt("snd")),
  xif: txtt("if"),
  lam: $lambda$,
  bool: txtt("bool"),
  y: txtt("fix"),
)

#let ogs = (
  call: cop(txtt("call")),
  ret: cop(txtt("ret")),
  ty: txtt("Typ"),
  scope: txtt("Scope"),
  cfg: txtt("Conf"),
  var: txtt("var"),
  val: txtt("Val"),
  sub: txtt("sub"),
  obs: txtt("Obs"),
  args: txtt("args"),
  apply: txtt("apply"),
  eval: txtt("eval"),
  nf: txtt("Nf"),
  pos: txtt("OGS-pos"),
  hg: txtt("OGS-half"),
  g: txtt("OGS"),
  pat: cnorm(sym.arrow.t),
  fil: cnorm(sym.arrow.b),
)

#let game = (
  g: txtt("Game"),
  hg: txtt("Half-Game"),
  mv: txtt("Move"),
  nx: txtt("next"),
  cli: txtt("client"),
  srv: txtt("server"),
  sp: $txtt("Strat")^+$,
  sn: $txtt("Strat")^-$,
)

//#let cfg(a, b) = $angle.l #a || #b angle.r$
#let cfg(a, b) = $#a th ; #b$

#let bind = cbin($> #h(-0.42em) > #h(-0.37em) =$)



#let mumu = "µµ" + box(move(dx: -0.15em, "\u{0303}"))

#let eqv(sub: []) = math.attach(sym.approx, br: sub)
#let interp(..x, s: []) = $bracket.double.l #x.pos().join(",") bracket.double.r_#s$

#let puzzle = box(baseline: 2pt, image(width: 0.8em, height: 0.8em, "/img/puzzle.png"))
#let puzzle-ctx = box(baseline: 2pt, image(width: 0.8em, height: 0.8em, "/img/puzzle-negative.png")) + h(2pt)

#let pat(short: false, ..xs) = context {
  let paren = [()]
  let paren-len = measure(paren).width
  let gadget = hide(paren) + h(0.2em - paren-len)
  let arg = xs.pos().map(x => gadget + x)
  if short [
    #h(0.2em) $lr("[", size: #140%) #arg.at(0)$ //#th ]
  ] else [
    #h(0.2em)
    #math.display(math.cases(delim: "[", ..arg, ..xs.named()))
  ]
}

#let cl = [#h(0.1em) : #h(0.25em)]
#let th = [#h(0.25em)]

#let colors = (
  kw: color.rgb("#ff9900"),
  pr: color.rgb("#ff0099"),
  cs: color.rgb("#33bb33"),
  de: color.rgb("#4488ff"),
)

#let kw = (
  rec: [ #text(colors.kw, "record") ],
  dat: [ #text(colors.kw, "data") ],
  cls: [ #text(colors.kw, "class") ],
  ins: [ #text(colors.kw, "instance") ],
  wit: [ #text(colors.kw, "with") ],
  //whr: [ #text(colors.kw, "where") ],
  whr: $:=$,
)

#let pr = x => text(colors.pr, x)
#let cs = x => text(colors.cs, x)
#let de = x => text(colors.de, x)

#let base = (
  Prop: de("Prop"),
  Set: de("Set"),
  Type: de("Type"),
  Cat: de("Cat"),
)

#let subs = (
  Pow: de("Pow"),
  Fam: de("Fam"),
  dom: pr("supp"),
  idx: pr("index"),
)

#let inst(it) = [ ⟬ #th #it #th ⟭ ]

#let delay = (
  t: de("Delay"),
)

#let itree = (
  t: de("ITree"),
  obs: pr("observe"),
  F: de("Action"),
  retF: cs("\u{2035}ret"),
  tauF: cs("\u{2035}tau"),
  visF: cs("\u{2035}vis"),
  unrollA: de($"unroll"^+$),
  unrollP: de($"unroll"^-$),
)

#let icont = (
  t: de("Container"),
  qry: pr("Query"),
  rsp: pr("Reply"),
  nxt: pr("next"),
)

#let game = (
  hg: de("HGame"),
  mv: pr("Move"),
  nx: pr("next"),
  emv: pr("move"),
  g: de("Game"),
  client: pr("client"),
  server: pr("server"),
  hsim: de("HSim"),
  hstr: pr("hs-move"),
  hscoh: pr("hs-next"),
  sim: de("Sim"),
  scli: pr("s-client"),
  ssrv: pr("s-server"),
  reixl: de(sym.angle.double.r),
  reixr: de(sym.angle.double.l),
  //extA: de(sym.times.circle),
  extA: de(move(text("▶", size: 0.61em), dy: -0.055em) + h(-0.723em) + sym.dot.circle),
  extP: de(sym.arrow.r.triple),
  stratA: de($"Strat"^+$),
  stratP: de($"Strat"^-$),
)

#let strat = (
  t: de("System"),
  stp: pr([$"state"^+$]),
  stn: pr([$"state"^-$]),
  play: pr("play"),
  coplay: pr("coplay"),
)

#let ctx = (
  ctxc: de("Ctx"),
  nilc: cs($epsilon$),
  conc: cs($triangle.r.filled.small$),
  varc: de($in.rev$),
  topc: cs("top"),
  popc: cs("pop"),
)

//#let icont_x (i: none, j: none) = if (i and j) [$"ICont" th #i th #j $] else [ICont]

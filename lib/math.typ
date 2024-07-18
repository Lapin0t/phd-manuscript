#let cl = [#h(0.2em) : #h(0.3em)]
#let th = [#h(0.25em)]
#let ar = move(sym.bracket.b, dy: -0.3em)

#let colors = (
  kw: color.rgb("#ff9900"),
  pr: color.rgb("#ff0099"),
  cs: color.rgb("#33bb33"),
  de: color.rgb("#4488ff"),
)

#let kw = (
  rec: text(colors.kw, "record"),
  dat: text(colors.kw, "data"),
  cls: text(colors.kw, "class"),
  ins: text(colors.kw, "instance"),
  wit: text(colors.kw, "with"),
  //whr: [ #text(colors.kw, "where") ],
  whr: $:=$,
  do: text(colors.kw, "do"),
)

#let pr = x => text(colors.pr, x)
#let cs = x => text(colors.cs, x)
#let de = x => text(colors.de, x)

#let crel(it) = math.class("relation", it)
//#let crel(it) = math.class("binary", it)
#let cnorm(it) = math.class("normal", it)
//#let cnorm(it) = text(it)

#let base = (
  Prop: de(math.op("Prop")),
  Set: de(math.op("Set")),
  Type: de(math.op("Type")),
  Cat: de(math.op("Cat")),
  endo: de(math.op("endo")),
  unit: de(math.bold("1")),
  tt: cs(sym.star),
)

#let subs = (
  Pow: de(math.op("Pow")),
  Fam: de(math.op("Fam")),
  dom: pr("supp"),
  idx: pr("index"),
  fiber: de(math.op("Fiber")),
  fib: cs(math.op("fib")),
)

#let inst(it) = [ ⟬ #th #it #th ⟭ ]

#let delay = (
  t: de(math.op("Delay")),
)

#let relr = math.italic(math.bold("r"))

#let rel = (
  //r: math.sans("REL"),
  r: relr,
  irel: de(math.op("IRel")),
  rel: de(math.op("Rel")),
  diag: de(math.op("diag")),
  diagS: de(math.op($Delta^relr$)),
  rev: de(math.op("rev")),
  revS: de(math.upright(math.sans("T"))),
  seq: de(math.op("seq")),
  seqS: de(crel("⨾")),
  lat: de(math.op(math.frak("L"))),
  forall: math.attach(sym.forall, tr: relr),
  //isum: crel(math.attach("+", tr: relr)), NEEDED?
  arr: crel(math.attach(sym.arrow, tr: relr)),
  iarr: crel(math.attach(sym.arrow.double, tr: relr)),
)

#let xrel(it) = $th class("opening", angle.l.double) it class("closing", angle.r.double) th$

#let tower = (
  t: de(math.op("Tower")),
  tb: cs(math.op("T-step")),
  tinf: cs(math.op("T-inf")),
  tind: de(math.op("tower")),
  nu: de(sym.nu),
)

#let iteq(it) = math.class("relation")[$de(approx.eq) #h(-0.1em) de("[") #it de("]")$]
#let iteqn(it) = math.class("normal")[$de(approx.eq) #h(-0.1em) de("[") #it de("]")$]
#let itweq(it) = math.class("relation")[$de(approx) #h(-0.1em) de("[") #it de("]")$]

#let itree = (
  t: de(math.op("ITree")),
  tp: de(sym.prime.double.rev + "ITree"),
  obs: pr("observe"),
  F: de(math.op("Action")),
  RS: [$de("Action")^de(rel.r)_Sigma$],
  retF: cs(math.op("\u{2035}ret")),
  tauF: cs(math.op("\u{2035}tau")),
  visF: cs(math.op("\u{2035}vis")),
  ret: de(math.op("ret")),
  tau: de(math.op("tau")),
  vis: de(math.op("vis")),
  retR: cs(math.op($"\u{2035}ret"^rel.r$)),
  tauR: cs(math.op($"\u{2035}tau"^rel.r$)),
  visR: cs(math.op($"\u{2035}vis"^rel.r$)),
  unrollA: de(math.op($"unroll"^+$)),
  unrollP: de(math.op($"unroll"^-$)),
  sb: de(math.op("sbisim")),
  wb: de(math.op("wbisim")),
  eq: de(sym.approx.eq),
  weq: de(sym.approx),
  eat: de(math.op("Eat")),
  eatR: cs(math.op("eat-refl")),
  eatS: cs(math.op("eat-step")),
  eatlr: de(crel(math.attach(sym.arrow.stroked.br, tr: "e"))),
  eatrl: de(crel(math.attach(sym.arrow.stroked.bl, tr: "e"))),
  subst: de(math.op("subst")),
  bind: crel(de($> #h(-0.42em) > #h(-0.37em) =$)),
  kbind: crel(de($> #h(-0.37em) = #h(-0.55em) >$)),
  gtau: de(math.op($"tau"!$)),
  gvis: de(math.op($"vis"!$)),
)

#let icont = (
  t: de(math.op("Container")),
  qry: pr("Query"),
  rsp: pr("Reply"),
  nxt: pr("next"),
)

#let game = (
  hg: de(math.op("HGame")),
  mv: pr("Move"),
  nx: pr("next"),
  emv: pr("move"),
  g: de(math.op("Game")),
  client: pr("client"),
  server: pr("server"),
  hsim: de(math.op("HSim")),
  hstr: pr("hs-move"),
  hscoh: pr("hs-next"),
  sim: de(math.op("Sim")),
  scli: pr("s-client"),
  ssrv: pr("s-server"),
  reixl: de(crel(sym.angle.double.r)),
  reixr: de(crel(sym.angle.double.l)),
  //extA: de(sym.times.circle),
  extA: de(crel(move(text("▶", size: 0.61em), dy: -0.055em) + h(-0.723em) + sym.dot.circle)),
  extP: de(crel(sym.arrow.r.triple)),
  stratA: de(math.op($"Strat"^+$)),
  stratP: de(math.op($"Strat"^-$)),
)

#let strat = (
  t: de(math.op("System")),
  stp: pr($"state"^+$),
  stn: pr($"state"^-$),
  play: pr("play"),
  coplay: pr("coplay"),
)

#let ctx = (
  ctxc: de(math.op("Ctx")),
  nilc: cs(math.op($epsilon$)),
  conc: cs(crel($triangle.r.filled.small$)),
  varc: de(crel($in.rev$)),
  topc: cs(math.op("top")),
  popc: cs(math.op("pop")),
)

//#let icont_x (i: none, j: none) = if (i and j) [$"ICont" th #i th #j $] else [ICont]

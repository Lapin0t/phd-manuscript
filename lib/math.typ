// typing colon
#let cl = [#h(0.2em) : #h(0.3em)]
// thin space (function application)
#let th = [#h(0.25em)]
// binding argument
#let ar = move(sym.bracket.b, dy: -0.3em)

#let colors = (
  kw: color.rgb("#ff9900"),  // keyword
  //kw: color.rgb("#e0af68"),  // keyword
  pr: color.rgb("#ff0099"),  // projection
  cs: color.rgb("#33bb33"),  // constructor
  de: color.rgb("#4488ff"),  // definition
)

#let kw = (
  rec: text(colors.kw, "record"),
  dat: text(colors.kw, "data"),
  codat: text(colors.kw, "codata"),
  cls: text(colors.kw, "class"),
  ins: text(colors.kw, "instance"),
  wit: text(colors.kw, "with"),
  where: text(colors.kw, "where"),
  whr: $:=$,
  do: text(colors.kw, "do"),
  fun: text(colors.kw, $lambda$),
)

#let pr = x => text(colors.pr, x)
#let cs = x => text(colors.cs, x)
#let de = x => text(colors.de, x)

// force math symbol class
#let crel(it) = math.class("relation", it)
#let cnorm(it) = math.class("normal", it)
#let cop(it) = math.op(it)

#let base = (
  Prop: de(cop("Prop")),
  Set: de(cop("Set")),
  Type: de(cop("Type")),
  Cat: de(cop("Cat")),
  endo: de(cop("endo")),
  unit: de(math.bold("1")),
  tt: cs(sym.star),
  inj1: cs(cop($"inj"_1$)),
  inj2: cs(cop($"inj"_2$)),
)

#let subs = (
  Pow: de(cop("Pow")),
  Fam: de(cop("Fam")),
  dom: pr("supp"),
  idx: pr("index"),
  fiber: de(cop("Fiber")),
  fib: cs(cop("fib")),
)

//#let inst(it) = [ ⟬ #th #it #th ⟭ ]

#let delay = (
  t: de(cop("Delay")),
)

#let xrel(it) = $th class("opening", angle.l.double) it class("closing", angle.r.double) th$
#let relr = math.italic(math.bold("r"))

#let rel = (
  r: relr,
  irel: de(cop("IRel")),
  rel: de(cop("Rel")),
  diag: de(cop("diag")),
  diagS: de(cop($Delta^relr$)),
  rev: de(cop("rev")),
  revS: de(math.upright(math.sans("T"))),
  seq: de(cop("seq")),
  seqS: de(crel("⨾")),
  lat: de(cop(math.frak("L"))),
  forall: math.attach(sym.forall, tr: relr),
  //isum: crel(math.attach("+", tr: relr)), NEEDED?
  arr: crel(math.attach(sym.arrow, tr: relr)),
  iarr: crel(math.attach(sym.arrow.double, tr: relr)),
)

#let tower = (
  t: de(cop("Tower")),
  tb: cs(cop("T-step")),
  tinf: cs(cop("T-inf")),
  tind: de(cop("tower")),
  nu: de(sym.nu),
)

#let iteq(it) = crel($de(approx.eq) #h(-0.1em) de("[") #it de("]")$)
#let iteqn(it) = cnorm(iteq(it))
#let itweq(it) = crel($de(approx) #h(-0.1em) de("[") #it de("]")$)
#let itweqn(it) = cnorm(itweq(it))

#let itree = (
  t: de(cop("ITree")),
  tp: de(sym.prime.double.rev + "ITree"),
  obs: pr("observe"),
  F: de(cop("Action")),
  RS: [$de("Action")^de(rel.r)_Sigma$],
  retF: cs(cop("\u{2035}ret")),
  tauF: cs(cop("\u{2035}tau")),
  visF: cs(cop("\u{2035}vis")),
  ret: de(cop("ret")),
  tau: de(cop("tau")),
  vis: de(cop("vis")),
  retR: cs(cop($"\u{2035}ret"^rel.r$)),
  tauR: cs(cop($"\u{2035}tau"^rel.r$)),
  visR: cs(cop($"\u{2035}vis"^rel.r$)),
  unrollA: de(cop($"unroll"^+$)),
  unrollP: de(cop($"unroll"^-$)),
  sb: de(cop("sbisim")),
  wb: de(cop("wbisim")),
  eq: de(sym.approx.eq),
  weq: de(sym.approx),
  eat: de(cop("Eat")),
  eatR: cs(cop("eat-refl")),
  eatS: cs(cop("eat-step")),
  eatlr: de(crel(math.attach(sym.arrow.stroked.br, tr: "e"))),
  eatrl: de(crel(math.attach(sym.arrow.stroked.bl, tr: "e"))),
  subst: de(cop("subst")),
  bind: de(crel($> #h(-0.42em) > #h(-0.37em) =$)),
  bindbk: crel($> #h(-0.42em) > #h(-0.37em) =$),
  kbind: de(crel($> #h(-0.37em) = #h(-0.55em) >$)),
  xtau: de(cop("tau!")),
  xvis: de(cop("vis!")),
  spin: de(cop("spin")),
  iter: de(cop("iter")),
  actguard: de(cop(sym.prime.double.rev + "guarded")),
  actevguard: de(cop(sym.prime.double.rev + "ev-guarded")),
  guard: de(cop("guarded")),
  evguard: de(cop("ev-guarded")),
  eqguard: de(cop("eqn-guarded")),
  eqevguard: de(cop("eqn-ev-guarded")),
  gret: cs(cop("g-ret")),
  gtau: cs(cop("g-vis")),
  gvis: cs(cop("g-vis")),
  evs: cs(cop("ev-step")),
  evg: cs(cop("ev-guard")),
  giter: de(cop("g-iter")),
  eviter: de(cop("ev-iter")),
  gstep: de(cop("g-step")),
  evunroll: de(cop("unroll")),
  equnroll: de(cop("eq-unroll")),
  copr: de(crel($⊞$))
)

#let icont = (
  t: de(cop("Container")),
  qry: pr("Query"),
  rsp: pr("Reply"),
  nxt: pr("next"),
)

#let game = (
  hg: de(cop("HGame")),
  mv: pr("Move"),
  nx: pr("next"),
  emv: pr("move"),
  g: de(cop("Game")),
  client: pr("client"),
  server: pr("server"),
  hsim: de(cop("HSim")),
  hstr: pr("hs-move"),
  hscoh: pr("hs-next"),
  sim: de(cop("Sim")),
  scli: pr("s-client"),
  ssrv: pr("s-server"),
  reixl: de(crel(sym.angle.double.r)),
  reixr: de(crel(sym.angle.double.l)),
  //extA: de(sym.times.circle),
  extA: de(crel(h(0.1em) + move(text($▶$, size: 0.61em), dy: -0.055em) + h(-0.723em) + sym.dot.circle + h(-0.1em))),
  extP: de(crel(sym.arrow.r.triple)),
  stratA: de(cop($"Strat"^+$)),
  stratP: de(cop($"Strat"^-$)),
)

#let strat = (
  t: de(cop("System")),
  stp: pr($"state"^+$),
  stn: pr($"state"^-$),
  play: pr("play"),
  coplay: pr("coplay"),
)

#let asgn(x) = crel($- #h(-0.2em) [ #x ] #h(-0.2em) ->$)

#let ctx = (
  ctxc: de(cop("Ctx")),
  nilc: cs(cop($epsilon$)),
  conc: cs(crel($triangle.r.filled.small$)),
  varc: de(crel($in.rev$)),
  topc: cs(cop("top")),
  popc: cs(cop("pop")),
  emp: pr(cop(sym.emptyset)),
  cat: pr(crel($triangle.r.filled.small #h(-0.3em) triangle.r.filled.small$)),
  var: pr(cop(math.bold("V"))),
  //cat: pr(crel($+ #h(-0.3em) triangle.r.filled.small$)),
)

//#let icont_x (i: none, j: none) = if (i and j) [$"ICont" th #i th #j $] else [ICont]

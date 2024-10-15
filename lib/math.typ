#let colors = (
  kw: color.rgb("#ff9900"),  // keyword
  //kw: color.rgb("#e0af68"),  // keyword
  pr: color.rgb("#ff0099"),  // projection
  cs: color.rgb("#33bb33"),  // constructor
  de: color.rgb("#4488ff"),  // definition
)


#let bk = x => text(black, x)
#let ckw = x => text(colors.kw, x)
#let pr = x => text(colors.pr, x)
#let cs = x => text(colors.cs, x)
#let de = x => text(colors.de, x)

// force math symbol class
#let crel(it) = math.class("relation", it)
#let cnorm(it) = math.class("normal", it)
#let cop(it) = math.op(it)
#let cbin(it) = math.class("binary", it)


// typing colon
#let cl = h(0.2em) + ":" + h(0.3em)
// thin space (function application)
#let th = h(0.25em)
// binding argument
#let ar = cop(move(sym.bracket.b, dy: -0.24em))
//#let ar = cop("-")

#let mutl = "µ" + box(move(dx: -0.25em, "\u{0303}"))
#let mumutl = "µ" + mutl

#let short = (
  llc: sym.lambda + "-calculus",
  uuc: mumutl + "-calculus",
)

#let kw = (
  rec: ckw("record"),
  dat: ckw("data"),
  codat: ckw("codata"),
  cls: ckw("class"),
  ext: ckw("extends"),
  ins: ckw("instance"),
  wit: ckw("with"),
  case: ckw("case"),
  where: ckw("where"),
  whr: $:=$,
  do: ckw("do"),
  fun: ckw($lambda$),
)

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
#let pat1(x) = pat(short: true, x)
#let pat0 = pat(short: true, h(-0.3em))

#let funpat(..xs) = {
  let pos = xs.pos().map(x => bk(x))
  kw.fun + h(-0.2em) +  pat(..pos, ..xs.named())
}

#let base = (
  Prop: de(cop("Prop")),
  Set: de(cop("Set")),
  Type: de(cop("Type")),
  Cat: de(cop("Cat")),
  endo: de(cop("endo")),
  unit: de(math.bold("1")),
  tt: cs(sym.star),
  sum: de(cbin(sym.plus)),
  inj1: cs(cop("inl")),
  inj2: cs(cop("inr")),
  prod: de(cbin(sym.times)),
  fst: pr("fst"),
  snd: pr("snd"),
  bot: de(cop(sym.bot)),
  exfalso: de(cop("ex-falso")),
  int: de(cnorm("∫")),
  vsum: de(cop("SumView")),
  vlft: cs(cop($"v-left"$)),
  vrgt: cs(cop($"v-right"$)), 
  ext: de(cop("Extensional")),
  refl: cs(cop("refl")),
  decidable: de(cop("Decidable")),
  yes: cs(cop("yes")),
  no: cs(cop("no")),
  nat: de(cop($ℕ$)),
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
  tp: de(sym.prime.rev + "ITree"),
  obs: pr("out"),
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
  fmap: de(cbin($angle.l #h(-0.1em) #move($\$$) #h(-0.1em) angle.r$)),
  xtau: de(cop("tau!")),
  xvis: de(cop("vis!")),
  spin: de(cop("spin")),
  iter: de(cop("iter")),
  actguard: de(cop(sym.prime.rev + "guarded")),
  actevguard: de(cop(sym.prime.rev + "ev-guarded")),
  guard: de(cop("guarded")),
  evguard: de(cop("ev-guarded")),
  eqguard: de(cop("eqn-guarded")),
  eqevguard: de(cop("eqn-ev-guarded")),
  gret: cs(cop("g-ret")),
  gtau: cs(cop("g-tau")),
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
  //extA: de(crel(h(0.1em) + move(text($▶$, size: 0.61em), dy: -0.055em) + h(-0.723em) + sym.dot.circle + h(-0.1em))),
  //extA: de(crel(h(0.1em) + move($*$, dy: -0.093em) + h(-0.64em) + sym.dot.circle + h(-0.1em))),
  //extA: de(crel(sym.dot.circle + h(-0.645em) + move($*$, dy: -0.09em))),
  extA: de(crel(sym.ast.circle)),
  extP: de(crel(sym.arrow.r.triple)),
  stratA: de(cop($"Strat"^+$)),
  stratP: de(cop($"Strat"^-$)),
  opp: de($dagger$),
  par: de(crel(sym.parallel)),
)

#let strat = (
  t: de(cop("System")),
  stp: pr($"state"^+$),
  stn: pr($"state"^-$),
  play: pr("play"),
  coplay: pr("coplay"),
  bs: de(cop("BS-System")),
)

//#let asgn(x) = de(crel($- #h(-0.2em) [bk(#x)] #h(-0.2em) ->$))
#let asgn(x) = de(crel($- #h(-0.2em) [bk(#x)] #h(-0.2em) ->$))
#let ctxhom(a, b) = [#de(sym.bracket.double.l) #a #de(",") #b #de(sym.bracket.double.r)]

#let ctxfill(x) = $de(angle.double.l) #x de(angle.double.r)$
#let eltfill(x) = $cs(angle.l) #x cs(angle.r)$
#let ctx = (
  ctxcat: de(cop(math.cal("C"))),
  ctxc: de(cop("Ctx")),
  nilc: cs(cop($epsilon$)),
  conc: cs(crel($triangle.r.filled.small$)),
  varc: de(crel($in.rev$)),
  topc: cs(cop("top")),
  popc: cs(cop("pop")),
  ope: de(cop("OPE")),
  end: cs(cop("end")),
  keep: cs(cop("keep")),
  skip: cs(cop("skip")),
  prescope: de(cop("PreScope")),
  emp: pr(sym.emptyset),
  //emp: pr("⍉"),
  catc: de(crel($triangle.r.filled.small #h(-0.25em) triangle.r.filled.small$)),
  cat: pr(crel("⧺")),
  vvar: pr(math.bold("V")),
  var: pr(crel($in.rev$)),
  rcatl: pr($"r-cat"_l$),
  rcatr: pr($"r-cat"_r$),
  //ren: de(crel($arrow.squiggly$)),
  ren: de(crel($subset.eq$)),
  catV: de(cop("ViewCat")),
  vcatl: cs(cop($"v-cat"_l$)),
  vcatr: cs(cop($"v-cat"_r$)), 
  scope: de(cop("Scope")),
  vemp: pr("view-emp"),
  vcat: pr("view-cat"),
  vcatirr: pr("view-cat-eq"),
  arr: crel("⇾"),
  tens: de($dot.circle$),
  all: de(cop("All")),
  fam0: de(cop($"SFam"_1$)),
  fam: de(cop($"SFam"$)),
  fam2: de(cop($"SFam"_2$)),
  bfam: de(cop("BFam")),
  Oper: pr("Op"),
  dom: pr("holes"),
  domnm: de($"holes"^text(font: "EB Garamond", weight: "bold", aleph)$),
  //fill: de(crel("@")), 
  oper: pr("op"),
  args: pr("args"),
  cute: cs(cbin(sym.square.filled.tiny)),
  named: de(h(0.05em) + text(font: "EB Garamond", weight: "bold", sym.aleph)),
  norm: de(cop("Nf")),
  //nf2obs: de(cop($"nf"cnorm(->)"obs"$)),
  //named: de(math.cal(math.bold("N"))),
  lenc: de(cop("length")),
)

#let sub = (
  mon: de(cop("SubstMonoid")),
  mod: de(cop("SubstModule")),
  ren: de(cop("RenModule")),
  pren: de(cop("PointedRenModule")),
  var: pr("var"),
  sub: pr("sub"),
  sext: pr("sub-ext"), 
  idl: pr($"sub-id"_l$),
  idr: pr($"sub-id"_r$),
  assoc: pr("sub-assoc"),
  act: pr("act"),
  aext: pr("act-ext"), 
  aid: pr("act-id"),
  acomp: pr("act-comp"),
  avar: pr("act-var"),
  box: de(sym.square),
  decvar: de("DecidableVar"),
  isvar: de("is-var"),
  isvardec: pr("is-var?"),
  isvarirr: pr("is-var-irr"),
  isvarren: pr("is-var-ren"),
)

#let ogs = (
  naivehg: de(cop($"OGS-hg"^"naive"_bk(O)$)),
  naiveg: de(cop($"OGS-g"^"naive"_bk(O)$)),
  hg: de(cop($"OGS"^#smallcaps("hg")_bk(O)$)),
  g: de(cop($"OGS"^#smallcaps(sym.zwj + "g")_bk(O)$)),
  ctx: de(cop("O-Ctx")),
  catE: de(math.class("opening", math.attach(sym.arrow.b, tr: sym.plus))),
  catO: de(math.class("opening", math.attach(sym.arrow.b, tr: sym.minus))),
  stratA: de(cop($"OGS"^+_bk(O)$)),
  stratP: de(cop($"OGS"^-_bk(O)$)),
  //join: de(crel($|#h(-0.12em)|#h(-0.12em)|$)),
  join: de(crel(sym.join)),
  compeq: de(cop("compo-eqn")),
  comp: de(cop("compo")),
  baremachine: de(cop("BareMachine")),
  conf: pr("Conf"),
  val: pr("Val"),
  eval: pr("eval"),
  apply: pr("apply"),
  machine: de(cop("LangMachine")),
  emb: de(cop("nf-emb")),
  //evalo: de($"eval"^text(font: "EB Garamond", "o")$),
  evalo: de("eval-to-obs"),
  evalnf: pr("eval-nf"),
  appext: pr("apply-ext"),
  renmachine: de(cop("LangMachineRen")),
  submachine: de(cop("LangMachineSub")),
  valren: pr("val-ren"),
  confren: pr("conf-ren"),
  evalren: pr("eval-ren"),
  appren: pr("apply-ren"),
  valsub: pr("val-sub"),
  confsub: pr("conf-sub"),
  evalsub: pr("eval-sub"),
  appsub: pr("apply-sub"),
  teleA: cop($de("Tele")^de(+)_Omega$),
  teleP: cop($de("Tele")^de(-)_Omega$),
  tnilA: cs($epsilon^+$),
  tnilP: cs($epsilon^-$),
  tconA: cs(crel($triangle.r.filled.small^+ circle.dotted$)),
  tconP: cs(crel($triangle.r.filled.small^-$)),
  collA: de(cop($attach(arrow.b, tr:+)$)),
  collP: de(cop($attach(arrow.b, tr: -)$)),
  mstrat: de(cop("mstrat")),
  nf2mv: de(cop("nf" + sym.arrow + "move")),
  mstratA: de(cop($"ogs"^+$)),
  mstratP: de(cop($"ogs"^-$)),
  mstratplay: de(cop("mstrat-play")),
  mstratresp: de(cop("mstrat-coplay")),
  subeq: crel(math.attach(de(sym.approx), br: de(smallcaps("sub")), tr: sym.Omega)),
  badinst: crel(de(sym.prec)),
  badc: cs(cop("bad")),
  finred: de(cop("FiniteRedexes")),
  mcompeq: de(cop("m-compo-eqn")),
  mcomp: de(cop("m-compo")),
  mcarg: de("MCArg"),
  zipev: de(cop("zip-then-eval")),
  zlr: de(crel(sym.arrow.cw.half)),
  zrl: de(crel(sym.arrow.ccw.half)),
  depthA0: de(cop($"depth"^+_0$)),
  depthP0: de(cop($"depth"^-_0$)),
  depthA: de(cop($"depth"^+$)),
  depthP: de(cop($"depth"^-$)),
)

#let ogsinterpA(x) = $de(bracket.double.l) #x de(bracket.double.r)^de(+)_M$
#let ogsinterpP(x) = $de(bracket.double.l) #x de(bracket.double.r)^de(-)_M$

//#let ogsapp(v,o,g) = $#v de(∗) #o #h(0.2em) de("⟬") #g de("⟭")$
//#let ogsapp(v,o,g) = $#v pr(∗) #o #h(0.2em) pr("⟬") #g pr("⟭")$
#let ogsapp(v,o,g) = $#v ∗ #o #h(0.2em) "⟬" #g "⟭"$

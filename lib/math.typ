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
#let mtxt(it) = text(font: "New Computer Modern Math", it)

#let txtt(it) = text(size: 8pt, font: "Fira Mono", it)
#let txsc(it) = smallcaps(it)

// surnames
// TODO: to smallcaps or not to smallcaps??
#let nm(it) = txsc(it)
//#let nm(it) = it

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
  top: de(cop(sym.top)),
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
  fin: de(cop("Fin")),
  ze: cs(cop("ze")),
  su: cs(cop("su")),
  fwkn: de(cop("fin-weaken")),
  fshft: de(cop("fin-shift")),
)

#let stlc = (
  tt: txtt("tt"),
  ff: txtt("ff"),
  xif: txtt("if"),
  lam: $lambda^"rec"$,
  bool: txtt("bool"),
  y: txtt("fix"),
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
  carr: crel(math.attach("⇾", tr: relr)),
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
  eqA: de(math.attach(sym.approx.eq, tr: $+$)),
  weqA: de(math.attach(sym.approx, tr: $+$)),
  eqP: de(math.attach(sym.approx.eq, tr: $-$)),
  weqP: de(math.attach(sym.approx, tr: $-$)),
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
  bfam: de(cop("Bind")),
  btfam: de(cop("BindTgt")),
  Oper: pr("Op"),
  dom: pr("holes"),
  tgt: pr("target"),
  domnm: de($"holes"^text(font: "EB Garamond", weight: "bold", aleph)$),
  //fill: de(crel("@")), 
  oper: pr("op"),
  args: pr("args"),
  cute: cs(cbin(sym.square.filled.tiny)),
  named: de(h(0.05em) + text(font: "EB Garamond", weight: "bold", sym.aleph)),
  norm: de(cop("Nf")),
  nret: cs(cop("nf-ret")),
  ncall: cs(cop("nf-call")),
  //nf2obs: de(cop($"nf"cnorm(->)"obs"$)),
  //named: de(math.cal(math.bold("N"))),
  lenc: de(cop("length")),
  eltupg: de(cop("elt-upgr")),
  untyped: de(cop("UntypedScope")),
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
  language: de(cop("Language")),
  resume: pr("resume"),
  elim: pr("elim"),
  resumesub: pr("resume-sub"),
  elimsub: pr("elim-sub"),
  emb: de(cop("nf-emb")),
  //evalo: de($"eval"^text(font: "EB Garamond", "o")$),
  evalo: de("eval-to-obs"),
  evalnf: pr("eval-nf"),
  appext: pr("apply-ext"),
  renmachine: de(cop("LangMachineRen")),
  submachine: de(cop("LangMachineSub")),
  sublang: de(cop("LanguageSub")),
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

#let nfinterpA(x) = $de(bracket.double.l) #x de(bracket.double.r)^de("NF")_M$
#let nfinterpP(x) = $de(bracket.double.l) #x de(bracket.double.r)^de("NF")_M$

//#let ogsapp(v,o,g) = $#v de(∗) #o #h(0.2em) de("⟬") #g de("⟭")$
//#let ogsapp(v,o,g) = $#v pr(∗) #o #h(0.2em) pr("⟬") #g pr("⟭")$
#let ogsapp(v,o,g) = $#v ∗ #o #h(0.2em) "⟬" #g "⟭"$

#let nf = (
  g: de(cop($"NF"^#smallcaps(sym.zwj + "g")_bk(O)$)),
  stratA: de(cop($"NF"^+_bk(O)$)),
  stratP: de(cop($"NF"^-_bk(O)$)),
  ogs2nfA: de(cop($"OGS-to-NF"^+$)),
  ogs2nfP: de(cop($"OGS-to-NF"^-$)),
  renA: de(cop($"NF-ren"^+$)),
  renP: de(cop($"NF-ren"^-$)),
  nf2ogsA: de(cop($"NF-to-OGS"^+$)),
  nf2ogsP: de(cop($"NF-to-OGS"^-$)),
  nf2ogs: de(cop("NF-to-OGS")),
  mstrat: de(cop("NF-mstrat")),
)

#let jwa = (
  cmd: de(cop("cmd")),
  val: de(cop("val")),
  typ: de(cop("typ")),
  isneg: de(cop("is-neg")),
  //ntyp: de(cop($not"-typ"$)),
  //nctx: de(cop($not"-ctx"$)),
  ntyp: de(cop($"typ"^"neg"$)),
  nctx: de(cop($"ctx"^"neg"$)),
  pat: de(cop("pat")),
  dom: de(cop("dom")),
  obs: de(cop("obs")),
  p2v: de(cop($"p-emb"$)),
  v2p: de(cop($"split-pat"$)),
  v2a: de(cop($"split-fill"$)),
  jcmd: de(crel(math.attach("⊢", tr: "c"))),
  jval: de(crel(math.attach("⊢", tr: "v"))),
  prod: cs(cbin($times$)),
  sum: cs(cbin($+$)),
  base: cs(cop($BB$)),
  neg: cs($not$),
  capp: cs(cbin($arrow.tr$)),
  vvar: cs(cop("var")),
  vlam: cs(cop($gamma$)),
  vinl: cs(cop("inl")),
  vinr: cs(cop("inr")),
  vyes: cs(cop("true")),
  vno: cs(cop("false")),
  //plam: cs(cop(circle($not$, stroke: 0.5pt + colors.cs, inset: 0pt, outset: -0.5pt))),
  plam: cs(cop($square.filled$)),
  //plam: cs(cop(h(1pt) + box($not^p$, stroke: 0.5pt + colors.cs, outset: (bottom: 1pt, top: 0.5pt, left: 0.5pt, right: 0.2pt), radius: 1pt))),
  pinl: cs(cop($"inl"^p$)),
  pinr: cs(cop($"inr"^p$)),
  pyes: cs(cop($"true"^p$)),
  pno: cs(cop($"false"^p$)),
  refold: de(cop("refold")),
  eval: de(cop("eval")),
  evalstep: de(cop("eval-step")),
  apply: de(cop("apply")),
  jwa: de(cop("JWA")),
  patX: de(cop($"pat"^*$)),
  domX: de(cop($"dom"^*$)),
  embX: de(cop($"p-emb"^*$)),
)
#let jwavpair(x, y) = $cs(angle.l) #x cs(",") #y cs(angle.r)$
#let jwappair(x, y) = $cs(angle.l) #x cs(",") #y cs(angle.r^p)$
#let jwaletin(x, y) = $cs("split") #x cs("in") #y$
#let jwaxxletin(x, y) = $cs("let") #x cs("in") #y$
//#let jwacasein(x, y, z) = $cs("if") #x cs("then") #y cs("else") #z$
#let jwacasein(x, y, z) = $cs("case") #x cs("in") cs("[") #y cs(",") #z cs("]")$

#let uut = (
  uut: de(cop($Mu tilde(Mu)$)),
  pol: de(cop("pol")),
  pp: cs($+$),
  pn: cs($-$),
  xtyp: de(cop($"typ"^o$)),
  typ: de(cop("typ")),
  tvar: cs(cop("tvar")),
  tzer: cs($0$),
  ttop: cs($top$),
  tbot: cs($bot$),
  tone: cs($1$),
  tten: cs($times.circle$),
  tpar: cs($cbin(⅋)$),
  tplu: cs($plus.circle$),
  tand: cs($cbin(\&)$),
  tdw: cs($cnorm(arrow.b)$),
  tup: cs($cnorm(arrow.t)$),
  tmin: cs($cnorm(minus.circle)$),
  tneg: cs($not$),
  tmu: cs($mu$),
  tnu: cs($nu$),
  tsub: de($slash$),
  styp: de(cop($"typ"^s$)),
  sneg: de($dagger$),
  ctx: de(cop("ctx")),
  tv: cs(cnorm(move(dy: -4pt, $script(+)$))),
  tk: cs(cnorm(move(dy: -4pt, $script(-)$))),
  cmd: de(cop("conf")),
  val: de(cop("val")),
  tm: de(cop("term")),
  wht: de(cop("whn")),
  jc: de(crel(math.attach("⊢", tr: "c"))),
  //jval: de(crel(math.attach("⊢", tr: "v"))),
  jt: de(crel(math.attach("⊢", tr: "t"))),
  jw: de(crel(math.attach("⊢", tr: "w"))),
  mu: cs(cop($mu$)),
  mut: cs(cop($tilde(mu)$)),
  vw: cs(cop("whn")),
  vvar: cs(cop("var")),
  vtt: cs($()$),
  vff: cs($[]$),
  vinl: cs(cop("inl")),
  vinr: cs(cop("inr")),
  vfst: cs(cop("fst")),
  vsnd: cs(cop("snd")),
  vdw: cs(cnorm($arrow.b$)),
  vup: cs(cnorm($arrow.t$)),
  vmin: cs(cnorm($minus.circle$)),
  vneg: cs($not$),
  vmu: cs(cop("con")),
  vnu: cs(cop("out")),
  ptt: cs($()^p$),
  pff: cs($[]^p$),
  pinl: cs(cop($"inl"^p$)),
  pinr: cs(cop($"inr"^p$)),
  pfst: cs(cop($"fst"^p$)),
  psnd: cs(cop($"snd"^p$)),
  pdw: cs(cnorm($attach(arrow.b, tr: p)$)),
  pup: cs(cnorm($attach(arrow.t, tr: p)$)),
  pmin: cs(cnorm($minus.circle^p$)),
  pneg: cs($not^p$),
  pmu: cs(cop($"con"^p$)),
  pnu: cs(cop($"out"^p$)),
  lam: cs($lambda$),
  colam: cs(scale(x: -100%, $lambda$)),
  ntyp: de(cop($"typ"^"priv"$)),
  nctx: de(cop($"ctx"^"priv"$)),
  isneg: de(cop("is-priv")),
  pat: de(cop("pat")),
  dom: de(cop("dom")),
  obs: de(cop("obs")),
  p2v: de(cop($"p-emb"$)),
  v2p: de(cop($"split-pat"$)),
  v2a: de(cop($"split-fill"$)),
  eval: de(cop("eval")),
  evalstep: de(cop("eval-step")),
  apply: de(cop("apply")),
  pbox: cs(cop($square.filled$)),
)
#let uutcfg(x, y) = $cs(angle.l) #x & cs(cbin(||)) & #y cs(angle.r)$
#let uutcfgp(p, x, y) = $cs(angle.l) #x cbin(cs(cnorm(|))cnorm(#p)cs(cnorm(|))) #y cs(angle.r)$
#let uutvpair(x, y) = $cs("(") #x cs(",") #y cs(")")$
#let uutvcase(x, y) = $cs("[") #x cs(",") #y cs("]")$
#let uutppair(x, y) = $cs("(") #x cs(",") #y cs(")"^p)$
#let uutpcase(x, y) = $cs("[") #x cs(",") #y cs("]"^p)$
#let uutpbox(x, y) = $uut.pbox^#box(x)_#y$
#let uutpm(s, ..xs) = {
  $uut.colam_#s$
  cs("{")
  xs.pos().join(cs(","))
  cs("}")
}
#let uutabs(s, ..xs) = {
  $uut.lam_#s$
  cs("{")
  xs.pos().join(cs(","))
  cs("}")
}

#let fil = (
  mon: de(cop("FillMonoid")),
  mod: de(cop("FillModule")),
  hole: pr(cop(sym.bullet)),
  fill: pr(cop("fill")),
  fillext: pr(cop("fill-ext")),
  idl: pr(cop($"fill-id"_l$)),
  idr: pr(cop($"fill-id"_r$)),
  assoc: pr(cop($"fill-assoc"$)),
  act: pr(cop("f-act")),
  actext: pr(cop("f-act-ext")),
  actid: pr(cop("f-act-id")),
  actcomp: pr(cop("f-act-comp")),
  smon: de(cop("FillMonoidSubst")),
  smod: de(cop("FillModuleSubst")),
  fillsub: pr(cop("sub-fill")),
  holesub: pr(cop($"sub-"cnorm(bullet)$)),
  actsub: pr(cop("sub-f-act")),
)

#let llc = (
  llc: de(cop("Lambda")),
  v2t: de(cop("v-to-t")),
  term: de(cop("term")),
  norm: de(cop("norm")),
  val: de(cop("val")),
  nval: cs(cop("value")),
  split: de(cop("split")),
  fold: de(cop("fold")),
  nstuck: cs(cop("stuck")),
  evc: de(cop("ev-ctx")),
  fterm: de(cop($"term"'$)),
  fval: de(cop($"val"'$)),
  fevc: de(cop($"ev-ctx"'$)),
  pat: de(cop("pat")),
  elim: de(cop("elim")),
  var: cs(cop("var")),
  vvar: cs(cop($"var"^v$)),
  ehole: cs(cop($bullet$)),
  eappl: cs(cop($dot_l$)),
  eappr: cs(cop($dot_r$)),
  app: cs(cop($dot$)),
  lam: cs(cop($lambda$)),
  vlam: cs(cop($lambda^v$)),
  eval: de(cop("eval")),
)

#let kriv = (
  kriv: de(cop(nm("Krivine"))),
  sort: de(cop("sort")),
  ctx: de(cop("ctx")),
  obs: de(cop("obs")),
  fobs: de(cop("o-fam")),
  dom: de(cop("o-dom")),
  stm: cs(cop("tm")),
  sreq: cs(cop("req")),
  sstk: cs(cop("stk")),
  syn: de(cop("syn")),
  conf: de(cop("conf")),
  app: cs($dot$),
  lam: cs($lambda$),
  cons: cs($colon.double$),
  var: cs(cop("var")),
  grab: cs(cop("grab")),
  force: cs(cop("force")),
  push: cs(cop("push")),
  eval: de(cop("eval")),
  evalstep: de(cop("eval-step")),
  apply: de(cop("apply")),
)

#let krivreq(x) = $cs(floor.l) #x cs(floor.r_r)$
#let krivcfg(x, y) = $cs(angle.l) th #x cs(cbin(||)) #y th cs(angle.r)$

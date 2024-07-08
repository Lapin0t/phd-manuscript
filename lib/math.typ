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
  dom: pr("support"),
  idx: pr("index"),
)

#let inst(it) = [ ⟬ #th #it #th ⟭ ]

#let itree = (
  t: de("ITree"),
  obs: pr("observe"),
  F: de("IStep"),
  coalg: de("ICoalg"),
  sort: pr("State"),
  out: pr("out"),
  subst: de("subst"),
)

#let icont = (
  t: de("Event"),
  qry: pr("Query"),
  rsp: pr("Reply"),
  nxt: pr("next"),
  ext: de("Ext"),
  eqry: pr("query"),
  ekon: pr("resume"),
)

#let game = (
  hg: de("HGame"),
  mv: pr("Move"),
  nx: pr("next"),
  emv: pr("move"),
  g: de("Game"),
  client: pr("client"),
  server: pr("server"),
  /*hsim: de("HSim"),
  hstr: pr("hsim-tr"),
  hscoh: pr("hsim-coh"),
  sim: de("Sim"),
  scli: pr("sim-client"),
  ssrv: pr("sim-server"),*/
  extA: de(sym.times.circle),
  extP: de(sym.arrow.r.triple),
  actF: de("Action"),
  retF: cs("'ret"),
  tauF: cs("'tau"),
  visF: cs("'vis"),
)

#let strat = (
  t: de("Strategy"),
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

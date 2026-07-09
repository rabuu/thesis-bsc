#let _lang(x) = box(smallcaps(x))

#let Fun = _lang("Fun")
#let Core = _lang("Core")
#let AxCut = _lang("AxCut")
#let RISC-V = _lang("RISC-V")

#let f2c(x, with: none) = $scr(C) bracket.l.stroked #x bracket.r.stroked_#with$
#let bindval(x, c) = $scr(B)_v (#x)[#c]$
#let bindvals(x, c) = $scr(L)_v (#x)[#c]$

#let c2a(x, ctx: none) = $scr(X) bracket.l.stroked #x bracket.r.stroked_#ctx$
#let a2m(x) = $scr(M) bracket.l.stroked #x bracket.r.stroked$

#let focus(x) = $scr(F)(#x)$
#let bind(x, c) = $scr(B)(#x)[#c]$
#let bindargs(x, c) = $scr(L)(#x)[#c]$

#let shrink(x) = $scr(S)(#x)$

// colors
#let orange = rgb("#E69F00")
#let green = rgb("#009E73")
#let lightgreen = rgb("#B8E986")
#let yellow = rgb("#F0E442")
#let blue = rgb("#0072B8")
#let lightblue = rgb("#56B4E9")
#let red = rgb("#D0021B")
#let purple = rgb("#9013FE")

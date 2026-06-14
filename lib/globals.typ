#let _lang(x) = smallcaps(x)

#let Fun = _lang("Fun")
#let Core = _lang("Core")
#let AxCut = _lang("AxCut")
#let RISC-V = _lang("RISC-V")

#let f2c(x, with: none) = $C bracket.l.stroked #x bracket.r.stroked_#with$
#let bindval(x, c) = $scr(B)_v (#x)[#c]$
#let bindvals(x, c) = $scr(L)_v (#x)[#c]$

#let c2a(x, ctx: none) = $scr(X) bracket.l.stroked #x bracket.r.stroked_#ctx$
#let a2m(x) = $scr(M) bracket.l.stroked #x bracket.r.stroked$

#let focus(x) = $scr(F)(#x)$
#let bind(x, c) = $scr(B)(#x)[#c]$
#let bindargs(x, c) = $scr(L)(#x)[#c]$

#let shrink(x) = $scr(S)(#x)$

#let _lang(x) = smallcaps(x)

#let Fun = _lang("Fun")
#let Core = _lang("Core")
#let AxCut = _lang("AxCut")
#let RISC-V = _lang("RISC-V")

#let f2c(x, with: none) = $C bracket.l.stroked #x bracket.r.stroked_#with$
#let a2m(x) = $scr(M) bracket.l.stroked #x bracket.r.stroked$

#let focus(x) = $scr(F)(#x)$
#let bind(x, c) = $scr(B)(#x)[#c]$
#let bindargs(x, c) = $scr(L)(#x)[#c]$

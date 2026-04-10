#let _kw(kw) = text(weight: "bold", raw(kw))

#let LET = _kw("let")
#let IF = _kw("if")
#let ELSE = _kw("else")
#let CASE = _kw("case")
#let NEW = _kw("new")
#let LABEL = _kw("label")
#let GOTO = _kw("goto")
#let EXIT = _kw("exit")
#let DATA = _kw("data")
#let CODATA = _kw("codata")
#let DEF = _kw("def")

#let i64 = _kw("i64")
#let cns = `cns`

#let var(x) = $#x$
#let covar(a) = $#a$

#let empty = sym.diamond.small

#let braces(..inner) = [{ #inner.pos().join($,$) }]
#let sp = sym.space.nobreak

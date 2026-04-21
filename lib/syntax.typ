#let _kw(kw) = text(weight: "bold", raw(kw))
#let _macro(m) = smallcaps(m)
#let _rv(s) = text(fill: blue, raw(s))

#let DEF = _kw("def")
#let DATA = _kw("data")
#let CODATA = _kw("codata")

#let LET = _kw("let")
#let IF = _kw("if")
#let ELSE = _kw("else")
#let CASE = _kw("case")
#let NEW = _kw("new")

#let i64 = _kw("i64")

#let cns = `cns`
#let prd = `prd`

// Fun
#let LABEL = _kw("label")
#let GOTO = _kw("goto")
#let EXIT = _kw("exit")

// AxCut
#let INVOKE = _kw("invoke")
#let SWITCH = _kw("switch")
#let CREATE = _kw("create")
#let LIT = _kw("lit")
#let SUBSTITUTE = _kw("substitute")

// codegen macros
#let STORE = _macro("Store")
#let REG = _macro("Reg")
#let VTABLE = _macro("VTable")

// RISC-V
#let LI = _rv("li")
#let LA = _rv("la")

#let var(x) = $#x$
#let covar(a) = $#a$

#let empty = sym.diamond.small

#let braces(..inner) = [{ #inner.pos().join($,$) }]
#let cut(p, c) = $chevron.l #p | #c chevron.r$

#let sp = sym.space.nobreak

#let syntax-config(it) = {
  show sym.colon: math.scripts
  it
}

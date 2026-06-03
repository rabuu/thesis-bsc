#let _kw(it) = text(weight: "bold", raw(it))
#let _macro(it) = smallcaps(it)
#let _reg(it) = raw(it)
#let _rv(it) = text(fill: blue, raw(it))

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
#let STOREV = _macro("StoreV")
#let REG = _macro("Reg")
#let OFFSET = _macro("Offset")
#let VTABLE = _macro("VTable")
#let ACQUIRE = _macro("Acquire")
#let ERASEFIELDS = _macro("EraseFields")

// registers
#let reg(num) = raw("x" + str(num))
#let TEMP = _reg("temp")
#let HEAP = _reg("heap")
#let TODO = _reg("todo")

// RISC-V
#let LI = _rv("li")
#let LA = _rv("la")
#let SW = _rv("sw")
#let LW = _rv("lw")
#let MV = _rv("mv")
#let BEQ = _rv("beq")
#let ADDI = _rv("addi")
#let JUMP = _rv("j")

#let var(x) = $#x$
#let covar(a) = $#a$

#let empty = sym.diamond.small

#let br(..inner) = [{ #inner.pos().join($,$) }]
#let cut(p, c) = $chevron.l #p | #c chevron.r$

#let sp = sym.space.nobreak

#let syntax-config(it) = {
  show sym.colon: math.scripts
  it
}

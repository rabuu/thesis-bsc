#import "settings.typ"

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

// AxCut
#let INVOKE = _kw("invoke")
#let SWITCH = _kw("switch")
#let CREATE = _kw("create")
#let LIT = _kw("lit")
#let SUBSTITUTE = _kw("substitute")

// codegen macros
#let LOAD = _macro("Load")
#let LOADV = _macro("LoadV")
#let STORE = _macro("Store")
#let STOREV = _macro("StoreV")
#let ACQUIRE = _macro("Acquire")
#let RELEASE = _macro("Release")
#let REG = _macro("Reg")
#let OFFSET = _macro("Offset")
#let NEXTBLOCKOFFSET = _macro("NextBlockOffset")
#let REFCOUNTOFFSET = _macro("RefCountOffset")
#let INDEX = _macro("Index")
#let VTABLE = _macro("VTable")
#let VTABLEB = _macro("VTableB")
#let JTABLE = _macro("JTable")
#let JTABLEB = _macro("JTableB")
#let SHARE = _macro("Share")
#let SHAREBLOCK = _macro("ShareBlock")
#let SHAREFIELDS = _macro("ShareFields")
#let ERASE = _macro("Erase")
#let ERASEBLOCK = _macro("EraseBlock")
#let ERASEFIELDS = _macro("EraseFields")
#let MOVE = _macro("Move")
#let NUMREFS = _macro("NumRefs")
#let METAIF = text(font: settings.font-serif, weight: "bold", "if")

// RISC-V
#let reg(num) = raw("x" + str(num))
#let TEMP = _reg("temp")
#let HEAP = _reg("heap")
#let TODO = _reg("todo")
#let lab(num) = raw("l" + str(num))
#let imm(num) = text(fill: purple, raw(str(num)))
#let LI = _rv("li")
#let LA = _rv("la")
#let SW = _rv("sw")
#let LW = _rv("lw")
#let MV = _rv("mv")
#let BEQ = _rv("beq")
#let BNE = _rv("bne")
#let ADD = _rv("add")
#let ADDI = _rv("addi")
#let JUMP = _rv("j")
#let JR = _rv("jr")

#let var(x) = $#x$
#let covar(a) = $#a$

#let empty = sym.diamond.small

#let br(..inner) = [{ #inner.pos().join($,$) }]
#let cl = math.chevron.l
#let cr = math.chevron.r
#let cut(p, c) = $cl #p | #c cr$

#let sp = sym.space.nobreak

#let syntax-config(it) = {
  show sym.colon: math.scripts
  it
}

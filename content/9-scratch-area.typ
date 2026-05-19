#import "/lib/lib.typ": *

#import syntax: *
#show: syntax.syntax-config

= Scratch Area

== Syntax for Linear Context Bindings
#bnf(
  (markhl($q$), markhl("Quantity")),
  markhl(alt(
    $1$,
    $omega quad "(mostly ommitted)"$,
  )),

  ($Gamma$, "Typing Contexts"),
  alt(
    $empty$,
    $Gamma, sp v :_markhl(q)^chi tau$,
  ),
)

== Translation from #Fun to #Core
#figure[
  $f2c(dot) : "Declaration"_Fun -> "Declaration"_Core$
  $
    f2c(DEF f(Gamma) : i64 braces(p)) & := DEF f(Gamma, alpha markhl(:_1^cns) tau) braces(f2c(p, with: alpha)) quad(alpha "fresh") \
    f2c(DEF "main"(Gamma) : i64 braces(p)) & := DEF "main"(Gamma) braces(f2c(p, with: tilde(mu)x.EXIT x)) \
    f2c(CODATA T braces(D_1(Gamma_1): tau_1, ...)) & := CODATA T braces(D_1(Gamma_1, alpha_1 markhl(:_1^cns) tau_1), ...) quad(alpha_1, ... "fresh") \
    f2c(DATA T braces(K_1(Gamma_1), ...)) & := DATA T braces(K_1(Gamma_1), ...)
  $
]

#line(length: 80%)

#figure[
  $f2c(dot) : "Producer"_Fun -> "Producer"_Core$
  $
    f2c(x) & := x \
    f2c(n) & := n \
    f2c(p_1 + p_2) & := f2c(p_1) + f2c(p_2) \
    f2c(K(sigma)) & := K(f2c(sigma)) \
    f2c(NEW braces(D_1(Gamma_1) => p_1, ...)) & := NEW braces(D_1(Gamma_1, alpha_1) => f2c(p_1, with: alpha_1), ...) \
    markhl(color: #red, f2c(LABEL sp alpha sp braces(p)) &:= mu alpha. f2c(p, with: alpha)) \
    markhl(f2c(f(sigma)) & := mu_1 alpha. f(f2c(sigma), alpha)) \
    f2c(p) & := mu alpha. f2c(p, with: alpha) quad "for all other producers" p \
  $
]

#line(length: 80%)

#figure[
  $f2c(dot, with: dot.o) : "Producer"_Fun times "Consumer"_Core -> "Statement"_Core$
  $
    f2c(n, with: c) & := && cut(n, c) \
    f2c(p_1 + p_2, with: c) & := && cut(f2c(p_1) + f2c(p_2), c) \
    f2c(x, with: c) & := && cut(x, c) \
    f2c(f(sigma), with: c) & := && f(f2c(sigma), c) \
    f2c(EXIT p, with: c) & := && EXIT f2c(p) \
    f2c(LABEL alpha braces(p), with: c) & := && cut(mu alpha. f2c(p, with: alpha), c) \
    f2c(GOTO alpha sp (p), with: c) & := && f2c(p, with: alpha) \
    f2c(LET x = p_1\; sp p_2, with: c) & := && f2c(p_1, with: tilde(mu)x. f2c(p_2, with: c)) \
    f2c(LET x = p_1\; sp p_2, with: c) & := && cut(f2c(p_1), tilde(mu)x. f2c(p_2, with: c))\
    "where" & && p_1 : CODATA T braces(...) \
    f2c(K(sigma), with: c) & := && cut(K(f2c(sigma)), c) \
    f2c(p.D(sigma), with: c) & := && f2c(p, with: D(f2c(sigma), c)) \
    f2c(NEW braces(D_1(Gamma_1) => p_1, ...), with: c) & := && cut(NEW braces(D_1(Gamma_1, alpha_1) => f2c(p_1, with: alpha_1), ...), c) \
    f2c(p.CASE braces(K_1(Gamma_1) => p_1, ...), with: c) & := && f2c(p, with: CASE braces(K_1(Gamma_1) => f2c(p_1, with: c_0), ...)) \
    "where" & && c_0 equiv tilde(mu)x. j(Gamma)\
    "with" & && DEF j(Gamma) braces(cut(x, c)) \
    "and" & && Gamma := "freeVars"(c), x :^prd tau \
    f2c(IF p equiv 0 braces(p_1) ELSE braces(p_2), with: c) & := && IF f2c(p) equiv 0 braces(f2c(p_1, with: c_0)) ELSE braces(f2c(p_2, with: c_0)) \
    "where" & && c_0 equiv tilde(mu)x. j(Gamma)\
    "with" & && DEF j(Gamma) braces(cut(x, c)) \
    "and" & && Gamma := "freeVars"(c), x :^prd tau \
  $
]

#line(length: 80%)

#figure[
  $f2c(dot) : "Arguments"_Fun -> "Arguments"_Core$
  $
            f2c(empty) & := empty \
        f2c(sigma\, p) & := f2c(sigma), f2c(p) \
    f2c(sigma\, alpha) & := f2c(sigma), alpha
  $
]

== Code Generation
$
  a2m(CREATE v = Gamma_0 sp b\; sp s) & := && STORE (REG_1 sp v) sp Gamma_0 & \
  & && LA (REG_2 sp v) sp l & \
  & && a2m(s) & \
  & && l: quad VTABLE sp b sp Gamma_0 & quad quad (l "fresh") \
  STORE r sp Gamma & := && STOREV Gamma & \
  &&& ACQUIRE r & \
  STOREV (Gamma, v :^chi tau) & := && SW (REG_2 sp v) sp (OFFSET_2 sp v) sp HEAP & \
  &&& SW (REG_1 sp v) sp (OFFSET_1 sp v) sp HEAP & \
  &&& STOREV Gamma \
  ACQUIRE r & := && MV r HEAP \
  &&& LW HEAP 0 HEAP \
  &&& BEQ HEAP #reg(0) l_1 \
  &&& quad SW #reg(0) 0 sp r \
  &&& quad JUMP l_2 \
  && l_1: & MV HEAP TODO \
  &&& LW TODO 0 TODO \
  &&& BEQ TODO #reg(0) l_3 \
  &&& quad SW #reg(0) 0 HEAP \
  &&& quad ERASEFIELDS HEAP \
  &&& quad JUMP l_2 \
  &&& l_3: ADDI TODO HEAP 32 \
  && l_2: & \
$

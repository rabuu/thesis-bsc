#import "/lib/lib.typ": *

#import syntax: *
#show: syntax.syntax-config

= Scratch Area

== Syntax for Linear Context Bindings
#bnf(
  (markhl($rho$), markhl("Quantity")),
  markhl(alt(
    $1$,
    $omega quad "(mostly ommitted)"$,
  )),

  ($Gamma$, "Typing Contexts"),
  alt(
    $empty$,
    $Gamma, sp v :_markhl(rho)^chi tau$,
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
    f2c(LABEL alpha braces(p)) &:= mu alpha. f2c(p, with: alpha) \
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

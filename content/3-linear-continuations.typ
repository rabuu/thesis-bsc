#import "/lib/lib.typ": *

#import syntax: *
#show: syntax-config

= Linear Continuations

== Restricting the Surface Language #Fun

== Linearity in #Core

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

#line(length: 100%)

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

#line(length: 100%)

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

#line(length: 100%)

#figure[
  $f2c(dot) : "Arguments"_Fun -> "Arguments"_Core$
  $
            f2c(empty) & := empty \
        f2c(sigma\, p) & := f2c(sigma), f2c(p) \
    f2c(sigma\, alpha) & := f2c(sigma), alpha
  $
]


== The Focusing Transformation

#figure[
  $focus(dot) : "Definition"_Core -> "Definition"_("Focused" Core)$
  $
    focus(DEF f(Gamma) braces(s)) & := && DEF f(Gamma) braces(focus(s))
  $
]

#line(length: 100%)

#figure[
  $focus(dot) : "Statement"_Core -> "Statement"_("Focused" Core)$
  $
    focus(cut(p_1 + p_2, c)) & := && bind(p_1, lambda a_1. bind(p_2, lambda a_2. cut(a_1 + a_2, focus(c)))) \
    focus(cut(K(sigma), c)) & := && bindargs(sigma, lambda overline(a). cut(K(overline(a)), focus(c))) \
    focus(cut(p, D(sigma))) & := && bindargs(sigma, lambda overline(a). cut(focus(p), D(overline(a)))) \
    focus(cut(p, c)) & := && cut(focus(p), focus(c)) \
    focus(IF p equiv 0 braces(s_1) ELSE braces(s_2)) & := && bind(p, lambda a. IF a equiv 0 braces(focus(s_1)) ELSE braces(focus(s_2))) \
    focus(f(sigma)) & := && bindargs(sigma, lambda overline(a). f(overline(a))) \
    focus(EXIT p) & := && bind(p, lambda a. EXIT a)
  $
]

#line(length: 100%)

#figure[
  $focus(dot) : "Producer"_Core -> "Producer"_("Focused" Core)$
  $
    focus(x) & := && x \
    focus(mu alpha. s) & := && mu alpha. focus(s) \
    focus(NEW braces(D_1(Gamma_1) => s_1, ...)) & := && NEW braces(D_1(Gamma_1) => focus(s_1), ...) \
    focus(K(sigma)) &&& "does not occur" \
    focus(n) & := && n \
    focus(p_1 + p_2) &&& "does not occur"
  $
]

#line(length: 100%)

#figure[
  $focus(dot) : "Consumer"_Core -> "Consumer"_("Focused" Core)$
  $
    focus(alpha) & := && alpha \
    focus(tilde(mu) x. s) & := && tilde(mu) x. focus(s) \
    focus(CASE braces(K_1(Gamma_1) => s_1, ...)) & := && CASE braces(K_1(Gamma_1) => focus(s_1), ...) \
    focus(D(sigma)) &&& "does not occur" \
  $
]

#line(length: 100%)

#figure[
  $bind(dot, dot) : "Producer"_Core times ("Var" -> "Statement"_("Focused" Core)) -> "Statement"_("Focused" Core)$
  $
    bind(x, k) & := && k(x) \
    bind(mu alpha. s, k) & := && cut(mu alpha. focus(s), tilde(mu) x. k(x)) \
    bind(K(sigma), k) & := && bindargs(sigma, lambda overline(a). cut(K(overline(a)), tilde(mu) x. k(x))) \
    bind(NEW braces(D_1(Gamma_1) => s_1, ...), k) & := && cut(NEW braces(D_1(Gamma_1) => focus(s_1), ...), tilde(mu) x. k(x)) \
    bind(n, k) & := && cut(n, tilde(mu) x. k(x)) \
    bind(p_1 + p_2, k) & := && bind(p_1, lambda a_1. bind(p_2, lambda a_2. cut(a_1 + a_2, tilde(mu) x. k(x))))
  $
]

#line(length: 100%)

#figure[
  $bind(dot, dot) : "Consumer"_Core times ("Covar" -> "Statement"_("Focused" Core)) -> "Statement"_("Focused" Core)$
  $
    bind(alpha, k) & := && k(alpha) \
    bind(tilde(mu) x. s, k) & := && cut(mu alpha. k(alpha), tilde(mu) x. focus(s)) \
    bind(D(sigma), k) & := && bindargs(sigma, lambda overline(a). cut(mu alpha. k(alpha), D(overline(a)))) \
    bind(CASE braces(K_1(Gamma_1) => s_1, ...), k) & := && cut(mu alpha. k(alpha), CASE braces(K_1(Gamma_1) => focus(s_1), ...)) \
  $
]

#line(length: 100%)

#figure[
  $bindargs(dot, dot) : "Arguments"_Core times ("Context" -> "Statement"_("Focused" Core)) -> "Statement"_("Focused" Core)$
  $
    bindargs(empty, k) & := && k(empty) \
    bindargs(e :: sigma, k) & := && bind(e, lambda a. bindargs(sigma, lambda overline(a). k(a :: overline(a))))
  $
]

== The Shrinking Transformation

== Linearity in #AxCut

== Translation from #Core to #AxCut

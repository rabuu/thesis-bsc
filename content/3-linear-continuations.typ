#import "/lib/lib.typ": *

#import syntax: *
#show: syntax-config

= Linear Continuations

== Restricting the Surface Language #Fun

=== Syntax
#figure[
  #bnf(
    ($p$, "Producers / Terms"),
    alt(
      var($x$),
      $LET var(x) = p; sp p$,
      $f(sigma)$,
    ),
    alt(
      $n$,
      $p + p$,
      $IF p equiv 0 br(p) ELSE br(p)$,
    ),
    alt(
      $K(sigma)$,
      $p.CASE br(K(Gamma) => p, ...)$,
    ),
    alt(
      $p.D(sigma)$,
      $NEW br(D(Gamma) => p, ...)$,
    ),
    $EXIT p$,
    erase(alt(
      $LABEL alpha br(p)$,
      $GOTO alpha sp (p)$,
    )),

    ($tau$, "Types"),
    alt(
      $i64$,
      $T$,
    ),

    ($sigma$, "Arguments"),
    alt(
      $empty$,
      $sigma, sp p$,
      erase($sigma, sp c$),
    ),

    ($Gamma$, "Typing Contexts"),
    alt(
      $empty$,
      $Gamma, sp x : tau$,
      erase($Gamma, sp alpha :^cns tau$),
    ),

    ($delta$, "Declarations"),
    $DEF f(Gamma) : tau br(p)$,
    alt(
      $DATA T br(K(Gamma), ...)$,
      $CODATA T br(D(Gamma) : tau, ...)$,
    ),

    ($Theta$, "Programs"),
    alt(
      $empty$,
      $Theta, sp delta$,
    ),
  )
]

=== Typing Rules
#figure[
  _Argument Typing:_ $Theta mid Gamma tack sigma : Gamma'$
  #rule-set(
    prooftree(rule(
      name: rn($#smallcaps("Arg") _1$),
      $Theta mid Gamma tack empty : empty$,
    )),
    prooftree(rule(
      name: rn($#smallcaps("Arg") _2$),
      $Theta mid Gamma tack sigma : Gamma'$,
      $Theta mid Gamma tack p : tau$,
      $Theta mid Gamma tack (sigma,p) : (Gamma', sp x:tau)$,
    )),
  )

  #rule-set(
    erase(prooftree(rule(
      name: rn($#smallcaps("Arg") _3$),
      $Theta mid Gamma tack sigma : Gamma'$,
      $Theta mid Gamma tack c :^cns tau$,
      $Theta mid Gamma tack (sigma,c) : (Gamma', sp alpha:^cns tau)$,
    ))),
  )

  #line(length: 100%)

  _Producer Typing:_ $Theta mid Gamma tack p : tau$
  #rule-set(
    prooftree(rule(
      name: rn("Var"),
      $x : tau in Gamma$,
      $Gamma tack x : tau$,
    )),
    prooftree(rule(
      name: rn("Lit"),
      $Gamma tack n : i64$,
    )),
    prooftree(rule(
      name: rn("Let"),
      $Gamma tack p_1 : tau_1$,
      $Gamma, sp x:tau_1 tack p_2 : tau_2$,
      $Gamma tack LET x = p_1; sp p_2 : tau_2$,
    )),
    prooftree(rule(
      name: rn("Plus"),
      $Gamma tack p_1 : i64$,
      $Gamma tack p_2 : i64$,
      $Gamma tack p_1 + p_2 : i64$,
    )),
    prooftree(rule(
      name: rn("IfZ"),
      $Gamma tack p : i64$,
      $Gamma tack p_1 : tau$,
      $Gamma tack p_2 : tau$,
      $Gamma tack IF p equiv 0 br(p_1) ELSE br(p_2) : tau$,
    )),
    prooftree(rule(
      name: rn("Exit"),
      $Gamma tack p : i64$,
      $Gamma tack EXIT p : tau$,
    )),
    prooftree(rule(
      name: rn("Ctor"),
      $DATA T br(..., K(Gamma'), ...) in Theta$,
      $Theta mid Gamma tack sigma : Gamma'$,
      $Theta mid Gamma tack K(sigma) : T$,
    )),
    prooftree(rule(
      name: rn("Case"),
      $DATA T br(K_1(Gamma_1), ...) in Theta$,
      $Gamma tack p : T$,
      $forall i: Gamma, Gamma_i tack p_i : tau$,
      $Theta mid Gamma tack p.CASE br(K_1(Gamma_1) => p_1, ...) : tau$,
    )),
    prooftree(rule(
      name: rn("Dtor"),
      $CODATA T br(..., D(Gamma') : tau, ...) in Theta$,
      $Gamma tack p : T$,
      $Theta mid Gamma tack sigma : Gamma'$,
      $Theta mid Gamma tack p.D(sigma) : tau$,
    )),
    prooftree(rule(
      name: rn("New"),
      $CODATA T br(D_1(Gamma_1) : tau_1, ...) in Theta$,
      $forall i: Gamma, Gamma_i tack p_i : tau_i$,
      $Theta mid Gamma tack NEW br(D_1(Gamma_1) => p_1, ...) : T$,
    )),
    prooftree(rule(
      name: rn("Call"),
      $DEF f(Gamma') : tau br(...) in Theta$,
      $Theta mid Gamma tack sigma : Gamma'$,
      $Theta mid Gamma tack f(sigma) : tau$,
    )),
  )

  #rule-set(
    erase(prooftree(rule(
      name: rn("Label"),
      $Gamma, alpha :^cns tau tack p : tau$,
      $Gamma tack LABEL alpha br(p) : tau$,
    ))),
    erase(prooftree(rule(
      name: rn("Goto"),
      $Gamma tack p : tau$,
      $alpha :^cns tau in Gamma$,
      $Gamma tack GOTO alpha sp (p) : tau$,
    ))),
  )

  #line(length: 100%, stroke: gray)

  #erase[_Consumer Typing:_ $Theta mid Gamma tack c :^cns tau$]
  #rule-set(
    erase(prooftree(rule(
      name: rn("Covar"),
      $alpha :^cns tau in Gamma$,
      $Gamma tack alpha :^cns tau$,
    ))),
  )
]

=== Intuitionistic!
#todo[Maybe a section about how Fun now loses classical expression and gets intuitionsistic.]

== Linearity in #Core

=== Syntax
#figure[
  #bnf(
    ($p$, "Producers"),
    alt(
      $var(x)$,
      $mark(mu_q) alpha. s$,
      $K(sigma)$,
      $NEW br(D(Gamma) => s, ...)$,
    ),
    alt(
      $n$,
      $p + p$,
    ),

    ($c$, "Consumers"),
    alt(
      $covar(alpha)$,
      $mark(tilde(mu)_q) x. s$,
      $D(sigma)$,
      $CASE br(K(Gamma) => s, ...)$,
    ),

    ($s$, "Statements"),
    alt(
      $cut(p, c)$,
      $IF p equiv 0 br(s) ELSE br(s)$,
      $f(sigma)$,
    ),
    alt(
      $EXIT p$,
    ),

    ($sigma$, "Arguments"),
    alt(
      $empty$,
      $sigma, sp p$,
      $sigma, sp c$,
    ),

    ($v$, "(Co)Variables"),
    alt(
      $var(x)$,
      $covar(alpha)$,
    ),

    ($tau$, "Types"),
    alt(
      $i64$,
      $T$,
    ),

    ($chi$, "Chirality"),
    alt(
      $prd$,
      $cns$,
    ),

    (mark($q$), highlight("Quantity")),
    mark(alt(
      $1$,
      $omega$,
    )),

    ($Gamma$, "Typing Contexts"),
    alt(
      $empty$,
      $Gamma, sp v :^chi_mark(q) tau$,
    ),

    ($pi$, "Polarity"),
    alt(
      $DATA$,
      $CODATA$,
    ),

    ($delta$, "Declarations"),
    alt(
      $DEF f(Gamma) : tau br(p)$,
      $pi sp T br(K(Gamma), ...)$,
    ),

    ($Theta$, "Programs"),
    alt(
      $empty$,
      $Theta, sp delta$,
    ),
  )
]

=== Typing Rules
#todo[TODO]

== Translation from #Fun to #Core
#figure[
  $f2c(dot) : "Declaration"_Fun -> "Declaration"_Core$
  $
    f2c(DEF f(Gamma) : i64 br(p)) & := DEF f(Gamma, alpha mark(:_1^cns) tau) br(f2c(p, with: alpha)) quad(alpha "fresh") \
    f2c(DEF "main"(Gamma) : i64 br(p)) & := DEF "main"(Gamma) br(f2c(p, with: mark(tilde(mu)_1)x.EXIT x)) \
    f2c(CODATA T br(D_1(Gamma_1): tau_1, ...)) & := CODATA T br(D_1(Gamma_1, alpha_1 mark(:_1^cns) tau_1), ...) quad(alpha_1, ... "fresh") \
    f2c(DATA T br(K_1(Gamma_1), ...)) & := DATA T br(K_1(Gamma_1), ...)
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
    f2c(NEW br(D_1(Gamma_1) => p_1, ...)) & := NEW br(D_1(Gamma_1, alpha_1) => f2c(p_1, with: alpha_1), ...) \
    mark(f2c(f(sigma)) & := mu_1 alpha. f(f2c(sigma), alpha)) \
    mark(f2c(p) & := mu_1 alpha. f2c(p, with: alpha) quad "for all other producers" p) \
    erase(f2c(LABEL sp alpha sp br(p)) & := mu alpha. f2c(p, with: alpha)) \
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
    f2c(LET x = p_1\; sp p_2, with: c) & := && f2c(p_1, with: mark(tilde(mu)_omega)x. f2c(p_2, with: c)) \
    f2c(LET x = p_1\; sp p_2, with: c) & := && cut(f2c(p_1), mark(tilde(mu)_omega)x. f2c(p_2, with: c))\
    "where" & && p_1 : CODATA T br(...)
    #note[Maybe render the both cases more clearly.]\
    f2c(K(sigma), with: c) & := && cut(K(f2c(sigma)), c) \
    #note[In the new journal paper version, this is different.]
    f2c(p.D(sigma), with: c) & := && f2c(p, with: D(f2c(sigma), c)) \
    f2c(NEW br(D_1(Gamma_1) => p_1, ...), with: c) & := && cut(NEW br(D_1(Gamma_1, alpha_1) => f2c(p_1, with: alpha_1), ...), c) \
    f2c(p.CASE br(K_1(Gamma_1) => p_1, ...), with: c) & := && f2c(p, with: CASE br(K_1(Gamma_1) => f2c(p_1, with: c_0), ...)) \
    "where" & && c_0 equiv mark(tilde(mu)_1)x. j(Gamma)\
    "with" & && DEF j(Gamma) br(cut(x, c)) \
    "and" & && Gamma := "freeVars"(c), mark(x :^prd_1 tau) \
    f2c(IF p equiv 0 br(p_1) ELSE br(p_2), with: c) & := && IF f2c(p) equiv 0 br(f2c(p_1, with: c_0)) ELSE br(f2c(p_2, with: c_0)) \
    "where" & && c_0 equiv mark(tilde(mu)_1)x. j(Gamma)\
    "with" & && DEF j(Gamma) br(cut(x, c)) \
    "and" & && Gamma := "freeVars"(c), mark(x :^prd_1) tau \
    erase(f2c(LABEL alpha br(p), with: c) & := && cut(mu alpha. f2c(p, with: alpha), c)) \
    erase(f2c(GOTO alpha sp (p), with: c) & := && f2c(p, with: alpha)) \
  $
]

#line(length: 100%)

#figure[
  $f2c(dot) : "Arguments"_Fun -> "Arguments"_Core$
  // @typstyle off
  $
    f2c(empty) & := empty \
    f2c(sigma\, p) & := f2c(sigma), f2c(p) \
    erase(f2c(sigma\, alpha) & := f2c(sigma)\, alpha)
  $
]

#inline-note[TODO: Update with binding functions (see new paper version).]

== The Focusing Transformation
#figure[
  $focus(dot) : "Definition"_Core -> "Definition"_("Focused" Core)$
  $
    focus(DEF f(Gamma) br(s)) & := && DEF f(Gamma) br(focus(s))
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
    focus(IF p equiv 0 br(s_1) ELSE br(s_2)) & := && bind(p, lambda a. IF a equiv 0 br(focus(s_1)) ELSE br(focus(s_2))) \
    focus(f(sigma)) & := && bindargs(sigma, lambda overline(a). f(overline(a))) \
    focus(EXIT p) & := && bind(p, lambda a. EXIT a)
  $
]

#line(length: 100%)

#figure[
  $focus(dot) : "Producer"_Core -> "Producer"_("Focused" Core)$
  $
    focus(x) & := && x \
    mark(focus(mu_q alpha. s) & := && mu_q alpha. focus(s)) \
    focus(NEW br(D_1(Gamma_1) => s_1, ...)) & := && NEW br(D_1(Gamma_1) => focus(s_1), ...) \
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
    mark(focus(tilde(mu)_q x. s) & := && tilde(mu)_q x. focus(s)) \
    focus(CASE br(K_1(Gamma_1) => s_1, ...)) & := && CASE br(K_1(Gamma_1) => focus(s_1), ...) \
    focus(D(sigma)) &&& "does not occur" \
  $
]

#line(length: 100%)

#figure[
  $bind(dot, dot) : "Producer"_Core times ("Var" -> "Statement"_("Focused" Core)) -> "Statement"_("Focused" Core)$
  $
    bind(x, k) & := && k(x) \
    mark(bind(mu_q alpha. s, k) & := && cut(mu_q alpha. focus(s), tilde(mu)_1 x. k(x))) \
    mark(bind(K(sigma), k) & := && bindargs(sigma, lambda overline(a). cut(K(overline(a)), tilde(mu)_1 x. k(x)))) \
    mark(bind(NEW br(D_1(Gamma_1) => s_1, ...), k) & := && cut(NEW br(D_1(Gamma_1) => focus(s_1), ...), tilde(mu)_1 x. k(x))) \
    mark(bind(n, k) & := && cut(n, tilde(mu)_1 x. k(x))) \
    mark(bind(p_1 + p_2, k) & := && bind(p_1, lambda a_1. bind(p_2, lambda a_2. cut(a_1 + a_2, tilde(mu)_1 x. k(x)))))
  $
]

#line(length: 100%)

#figure[
  $bind(dot, dot) : "Consumer"_Core times ("Covar" -> "Statement"_("Focused" Core)) -> "Statement"_("Focused" Core)$
  $
    bind(alpha, k) & := && k(alpha) \
    mark(bind(tilde(mu)_q x. s, k) & := && cut(mu_1 alpha. k(alpha), tilde(mu)_q x. focus(s))) \
    mark(bind(D(sigma), k) & := && bindargs(sigma, lambda overline(a). cut(mu_1 alpha. k(alpha), D(overline(a))))) \
    mark(bind(CASE br(K_1(Gamma_1) => s_1, ...), k) & := && cut(mu_1 alpha. k(alpha), CASE br(K_1(Gamma_1) => focus(s_1), ...))) \
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
#todo[TODO]

== Linearity in #AxCut
#todo[TODO]

== Translation from #Core to #AxCut
#todo[TODO]

#import "/lib/lib.typ": *
#import deps.fletcher

#import syntax: *
#show: syntax.syntax-config

= The Sequent Calculus Compiler

== Overview
#figure({
  import fletcher: diagram, edge, node

  let colored-node(color) = node.with(stroke: color, fill: color.lighten(65%))

  let fun = (0, 0)
  let core = (2, 0)
  let axcut = (4, 0)
  let riscv = (6, 0)

  diagram(
    debug: false,
    node-stroke: 1pt,
    colored-node(red)(fun, Fun),
    colored-node(green)(core, Core),
    colored-node(blue)(axcut, AxCut),
    colored-node(orange)(riscv, RISC-V),
    edge(fun, core, "-|>", label: $f2c(dot)$),
    edge(core, axcut, "-|>", label: $c2a(dot)$),
    edge(axcut, riscv, "-|>", label: $a2m(dot)$),
    edge(core, core, "-|>", bend: -130deg, label: $focus(dot), shrink(dot)$),
  )
})

== The Surface Language #Fun

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
    alt(
      $LABEL alpha br(p)$,
      $GOTO alpha sp (p)$,
    ),
    $EXIT p$,

    ($c$, "Consumers"),
    $alpha$,

    ($tau$, "Types"),
    alt(
      $i64$,
      $T$,
    ),

    ($sigma$, "Arguments"),
    alt(
      $empty$,
      $sigma, sp p$,
      $sigma, sp c$,
    ),

    ($Gamma$, "Typing Contexts"),
    alt(
      $empty$,
      $Gamma, sp x : tau$,
      $Gamma, sp alpha :^cns tau$,
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
    prooftree(rule(
      name: rn($#smallcaps("Arg") _3$),
      $Theta mid Gamma tack sigma : Gamma'$,
      $Theta mid Gamma tack c :^cns tau$,
      $Theta mid Gamma tack (sigma,c) : (Gamma', sp alpha:^cns tau)$,
    )),
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
      name: rn("Label"),
      $Gamma, alpha :^cns tau tack p : tau$,
      $Gamma tack LABEL alpha br(p) : tau$,
    )),
    prooftree(rule(
      name: rn("Goto"),
      $Gamma tack p : tau$,
      $alpha :^cns tau in Gamma$,
      $Gamma tack GOTO alpha sp (p) : tau$,
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

  #line(length: 100%)

  _Consumer Typing:_ $Theta mid Gamma tack c :^cns tau$
  #rule-set(
    prooftree(rule(
      name: rn("Covar"),
      $alpha :^cns tau in Gamma$,
      $Gamma tack alpha :^cns tau$,
    )),
  )
]

== The High-Level Intermediate Language #Core

=== Syntax
#figure[
  #bnf(
    ($p$, "Producers"),
    alt(
      $var(x)$,
      $mu alpha. s$,
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
      $tilde(mu) x. s$,
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

    ($Gamma$, "Typing Contexts"),
    alt(
      $empty$,
      $Gamma, sp v :^chi tau$,
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
#figure[
  _Producer Typing:_ $Theta mid Gamma tack p :^prd tau$
  #rule-set(
    prooftree(rule(
      name: rn("Var"),
      $x :^prd tau in Gamma$,
      $Gamma tack x :^prd tau$,
    )),
    prooftree(rule(
      name: rn("Act-R"),
      $Gamma, alpha :^cns tau tack s$,
      $Gamma tack mu a. s :^prd tau$,
    )),
    prooftree(rule(
      name: rn("Ctor"),
      $DATA T br(..., K(Gamma'), ...) in Theta$,
      $Theta mid Gamma tack sigma : Gamma'$,
      $Theta mid Gamma tack K(sigma) :^prd T$,
    )),
    prooftree(rule(
      name: rn("New"),
      $CODATA T br(D_1(Gamma_1), ...) in Theta$,
      $forall i: Gamma, Gamma_i tack s_i$,
      $Theta mid Gamma tack NEW br(D_1(Gamma_1) => s_1, ...) :^prd T$,
    )),
    prooftree(rule(
      name: rn("Lit"),
      $Gamma tack n :^prd i64$,
    )),
    prooftree(rule(
      name: rn("Plus"),
      $Gamma tack p_1 :^prd i64$,
      $Gamma tack p_2 :^prd i64$,
      $Gamma tack p_1 + p_2 :^prd i64$,
    )),
  )

  #line(length: 100%)

  _Consumer Typing:_ $Theta mid Gamma tack c :^cns tau$
  #rule-set(
    prooftree(rule(
      name: rn("Covar"),
      $alpha :^cns tau in Gamma$,
      $Gamma tack alpha :^cns tau$,
    )),
    prooftree(rule(
      name: rn("Act-L"),
      $Gamma, x :^prd tau tack s$,
      $Gamma tack tilde(mu)x. s :^cns tau$,
    )),
    prooftree(rule(
      name: rn("Dtor"),
      $CODATA T br(..., D(Gamma'), ...) in Theta$,
      $Theta mid Gamma tack sigma : Gamma'$,
      $Theta mid Gamma tack D(sigma) :^cns T$,
    )),
    prooftree(rule(
      name: rn("Case"),
      $DATA T br(K_1(Gamma_1), ...) in Theta$,
      $forall i: Gamma, Gamma_i tack s_i$,
      $Theta mid Gamma tack CASE br(K_1(Gamma_1) => s_1, ...) :^cns T$,
    )),
  )

  #line(length: 100%)

  _Statement Typing:_ $Theta mid Gamma tack s$
  #rule-set(
    prooftree(rule(
      name: rn("Cut"),
      $Gamma tack p :^prd tau$,
      $Gamma tack c :^cns tau$,
      $Gamma tack cut(p, c)$,
    )),
    prooftree(rule(
      name: rn("IfZ"),
      $Gamma tack p :^prd i64$,
      $Gamma tack s_1$,
      $Gamma tack s_2$,
      $Gamma tack IF p equiv 0 br(s_1) ELSE br(s_1)$,
    )),
    prooftree(rule(
      name: rn("Call"),
      $DEF f(Gamma') br(...) in Theta$,
      $Theta mid Gamma tack sigma : Gamma'$,
      $Theta mid Gamma tack f(sigma)$,
    )),
    prooftree(rule(
      name: rn("Exit"),
      $Gamma tack p :^prd i64$,
      $Gamma tack EXIT p$,
    )),
  )
]

== Translation from #Fun to #Core
#figure[
  $f2c(dot) : "Declaration"_Fun -> "Declaration"_Core$
  $
    f2c(DEF f(Gamma) : i64 br(p)) & := DEF f(Gamma, alpha :^cns tau) br(f2c(p, with: alpha)) quad(alpha "fresh") \
    f2c(DEF "main"(Gamma) : i64 br(p)) & := DEF "main"(Gamma) br(f2c(p, with: tilde(mu)x.EXIT x)) \
    f2c(CODATA T br(D_1(Gamma_1): tau_1, ...)) & := CODATA T br(D_1(Gamma_1, alpha_1 :^cns tau_1), ...) quad(alpha_1, ... "fresh") \
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
    f2c(LABEL alpha br(p)) &:= mu alpha. f2c(p, with: alpha) \
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
    f2c(LABEL alpha br(p), with: c) & := && cut(mu alpha. f2c(p, with: alpha), c) \
    f2c(GOTO alpha sp (p), with: c) & := && f2c(p, with: alpha) \
    f2c(LET x = p_1\; sp p_2, with: c) & := && f2c(p_1, with: tilde(mu)x. f2c(p_2, with: c)) \
    f2c(LET x = p_1\; sp p_2, with: c) & := && cut(f2c(p_1), tilde(mu)x. f2c(p_2, with: c))\
    "where" & && p_1 : CODATA T br(...) \
    f2c(K(sigma), with: c) & := && cut(K(f2c(sigma)), c) \
    f2c(p.D(sigma), with: c) & := && f2c(p, with: D(f2c(sigma), c)) \
    f2c(NEW br(D_1(Gamma_1) => p_1, ...), with: c) & := && cut(NEW br(D_1(Gamma_1, alpha_1) => f2c(p_1, with: alpha_1), ...), c) \
    f2c(p.CASE br(K_1(Gamma_1) => p_1, ...), with: c) & := && f2c(p, with: CASE br(K_1(Gamma_1) => f2c(p_1, with: c_0), ...)) \
    "where" & && c_0 equiv tilde(mu)x. j(Gamma)\
    "with" & && DEF j(Gamma) br(cut(x, c)) \
    "and" & && Gamma := "freeVars"(c), x :^prd tau \
    f2c(IF p equiv 0 br(p_1) ELSE br(p_2), with: c) & := && IF f2c(p) equiv 0 br(f2c(p_1, with: c_0)) ELSE br(f2c(p_2, with: c_0)) \
    "where" & && c_0 equiv tilde(mu)x. j(Gamma)\
    "with" & && DEF j(Gamma) br(cut(x, c)) \
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
    focus(mu alpha. s) & := && mu alpha. focus(s) \
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
    focus(tilde(mu) x. s) & := && tilde(mu) x. focus(s) \
    focus(CASE br(K_1(Gamma_1) => s_1, ...)) & := && CASE br(K_1(Gamma_1) => focus(s_1), ...) \
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
    bind(NEW br(D_1(Gamma_1) => s_1, ...), k) & := && cut(NEW br(D_1(Gamma_1) => focus(s_1), ...), tilde(mu) x. k(x)) \
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
    bind(CASE br(K_1(Gamma_1) => s_1, ...), k) & := && cut(mu alpha. k(alpha), CASE br(K_1(Gamma_1) => focus(s_1), ...)) \
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

+ Inline all possible pairs of producers and consumers in cuts.

+ "Six of these combinations are precluded by typing."

+ Removing Renaming:
  #figure[
    $
      shrink(cut(mu alpha. s, beta)) & := && shrink(s[alpha mapsto beta]) \
      shrink(cut(y, tilde(mu)x. s)) & := && shrink(s[x mapsto y]) \
      shrink(cut(K_j (sigma), CASE br(K_1(Gamma_1) => s_1, ...))) & := && shrink(s_j [Gamma_j mapsto sigma]) \
      shrink(cut(NEW br(D_1(Gamma_1) => s_1, ...), D_j (sigma))) & := && shrink(s_j [Gamma_j mapsto sigma]) \
    $
  ]

+ Removing Critical Pairs:
  #figure[
    $
      shrink(cut(mu alpha. s_1, tilde(mu)x. s_2)_T) & := && cut(mu alpha. shrink(s_1), CASE br(K_1(Gamma_1) => cut(K_1(Gamma_1), tilde(mu)x. j(Gamma)), ...))\
      "where" &&& DATA T br(K_1(Gamma_1), ...) in Theta \
      "with" &&& DEF j(Gamma) br(shrink(s_2)) \
      "and" &&& Gamma := "freeVars"(shrink(s_2)) \
      shrink(cut(mu alpha. s_1, tilde(mu)x. s_2)_T) & := && cut(NEW br(D_1(Gamma_1) => cut(mu alpha. j(Gamma), D_1(Gamma_1)), ...), tilde(mu)x. shrink(s_2)) \
      "where" &&& CODATA T br(D_1(Gamma_1), ...) in Theta \
      "with" &&& DEF j(Gamma) br(shrink(s_1)) \
      "and" &&& Gamma := "freeVars"(shrink(s_1)) \
    $
  ]

+ Removing Unknown Cuts:
  #figure[
    $
      shrink(cut(x, alpha)_T) & := && cut(x, CASE br(K_1(Gamma_1) => cut(K_1(Gamma_1), alpha), ...)) \
      "where" &&& DATA T br(K_1(Gamma_1), ...) in Theta \
      shrink(cut(x, alpha)_T) & := && cut(NEW br(D_1(Gamma_1) => cut(x, D_1(Gamma_1)), ...), alpha) \
      "where" &&& CODATA T br(D_1(Gamma_1), ...) in Theta \
    $
  ]

+ Dealing with Built-In Types:

  Define: $DATA "Cont" br("Ret"(x :^prd i64))$

  #figure[
    $
      shrink(cut(mu alpha. s_1, tilde(mu) x. s_2)_i64) & := && cut(mu alpha. shrink(s_1), CASE br("Ret"(x) => shrink(s_2))) \
      shrink(cut(x, alpha)_i64) & := && cut("Ret"(x), alpha) \
      shrink(cut(n, alpha)) & := && cut(n, tilde(mu)x. cut("Ret"(x), alpha)) quad(x "fresh") \
      shrink(cut(x_1 + x_2, alpha)) & := && cut(x_1 + x_2, tilde(mu)x. cut("Ret"(x), alpha)) quad(x "fresh") \
    $
    $
      shrink(Gamma\, alpha :^cns i64) & := && shrink(Gamma), alpha :^cns "Cont" \
          shrink(Gamma\, v :^chi tau) & := && shrink(Gamma), v :^chi tau
    $
  ]

== The Lower-Level Intermediate Language #AxCut

=== Syntax
#figure[
  #bnf(
    ($v$, "(Co)Variables"),
    alt(
      $var(x)$,
      $covar(alpha)$,
    ),

    ($s$, "Statements"),
    $LET v = X(sigma); sp s$,
    $INVOKE v sp X(sigma)$,
    $SWITCH v br(X(Gamma) => s, ...)$,
    $CREATE v = Gamma br(X(Gamma) => s, ...); sp s$,
    $LIT v <- n; sp s$,
    $v <- v + v; sp s$,
    $IF v equiv 0 br(s) ELSE br(s)$,
    $f(sigma)$,
    $SUBSTITUTE[Gamma := sigma]; sp s$,
    $EXIT v$,
    ($sigma$, "Arguments"),
    alt(
      $empty$,
      $sigma, sp v$,
    ),
  )
]

=== Typing Rules
#figure[
  #rule-set(
    prooftree(rule(
      name: rn("Substitute"),
      $Gamma tack sigma : Gamma'$,
      $Gamma' tack s$,
      $Gamma tack SUBSTITUTE[Gamma' := sigma]; sp s$,
    )),
  )

  #line(length: 100%)

  #rule-set(
    prooftree(rule(
      name: rn("Lit"),
      $Gamma, v:^prd i64 tack s$,
      $Gamma tack LIT v <- n; sp s$,
    )),
    prooftree(rule(
      name: rn("Plus"),
      $v_1 :^prd i64 in Gamma$,
      $v_2 :^prd i64 in Gamma$,
      $Gamma, v :^prd i64 tack s$,
      $Gamma tack v <- v_1 + v_2; sp s$,
    )),
    prooftree(rule(
      name: rn("Exit"),
      $v :^prd i64 in Gamma$,
      $Gamma tack EXIT v$,
    )),
    prooftree(rule(
      name: rn("IfZ"),
      $v :^prd i64 in Gamma$,
      $Gamma tack s_1$,
      $Gamma tack s_2$,
      $Gamma tack IF v equiv 0 br(s_1) ELSE br(s_2)$,
    )),
  )

  #line(length: 100%)

  #rule-set(
    prooftree(rule(
      name: rn("Call"),
      $DEF f(Gamma) br(...) in Theta$,
      $Theta mid Gamma tack f(Gamma)$,
    )),
  )

  #line(length: 100%)

  $
    chi_1(DATA) := prd
    quad
    chi_1(CODATA) := cns
    quad
    chi_2(DATA) := cns
    quad
    chi_2(CODATA) := prd
  $

  #rule-set(
    prooftree(rule(
      name: $#rn("Let-")pi$,
      $pi T br(..., X(Gamma_0), ...) in Theta$,
      $Gamma, v:^(chi_1(pi)) T tack s$,
      $Theta mid Gamma, Gamma_0 tack LET v = X(Gamma_0); sp s$,
    )),
    prooftree(rule(
      name: $#rn("Create-")pi$,
      $pi T br(X_1(Gamma_1), ...) in Theta$,
      $Gamma, v:^(chi_2(pi)) T tack s$,
      $forall i: Gamma_i, Gamma_0 tack s_i$,
      $Theta mid Gamma, Gamma_0 tack CREATE v = Gamma_0 br(X_1(Gamma_1) => s_1, ...); sp s$,
    )),
    prooftree(rule(
      name: $#rn("Switch-")pi$,
      $pi T br(X_1(Gamma_1), ...) in Theta$,
      $forall i: Gamma, Gamma_i tack s_i$,
      $Theta mid Gamma, v :^(chi_1(pi)) T tack SWITCH v br(X_1(Gamma_1) => s_1, ...)$,
    )),
    prooftree(rule(
      name: $#rn("Invoke-")pi$,
      $pi T br(..., X(Gamma), ...) in Theta$,
      $Theta mid Gamma, v :^(chi_2(pi)) T tack INVOKE v sp X(Gamma)$,
    )),
  )
]

== Translation from #Core to #AxCut
#todo[TODO]

== Translation from #AxCut to #RISC-V machine code
#todo[TODO]

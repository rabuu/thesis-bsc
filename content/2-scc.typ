#import "/lib/lib.typ": *
#import deps.fletcher

#import prooftree: *
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
      $IF p equiv 0 braces(p) ELSE braces(p)$,
    ),
    alt(
      $K(sigma)$,
      $p.CASE braces(K(Gamma) => p, ...)$,
    ),
    alt(
      $p.D(sigma)$,
      $NEW braces(D(Gamma) => p, ...)$,
    ),
    alt(
      $LABEL alpha braces(p)$,
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
    $DEF f(Gamma) : tau braces(p)$,
    alt(
      $DATA T braces(K(Gamma), ...)$,
      $CODATA T braces(D(Gamma) : tau, ...)$,
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
      $Gamma tack IF p equiv 0 braces(p_1) ELSE braces(p_2) : tau$,
    )),
    prooftree(rule(
      name: rn("Label"),
      $Gamma, alpha :^cns tau tack p : tau$,
      $Gamma tack LABEL alpha braces(p) : tau$,
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
      $DATA T braces(..., K(Gamma'), ...) in Theta$,
      $Theta mid Gamma tack sigma : Gamma'$,
      $Theta mid Gamma tack K(sigma) : T$,
    )),
    prooftree(rule(
      name: rn("Case"),
      $DATA T braces(K_1(Gamma_1), ...) in Theta$,
      $Gamma tack p : T$,
      $forall i: Gamma, Gamma_i tack p_i : tau$,
      $Theta mid Gamma tack p.CASE braces(K_1(Gamma_1) => p_1, ...) : tau$,
    )),
    prooftree(rule(
      name: rn("Dtor"),
      $CODATA T braces(..., D(Gamma') : tau, ...) in Theta$,
      $Gamma tack p : T$,
      $Theta mid Gamma tack sigma : Gamma'$,
      $Theta mid Gamma tack p.D(sigma) : tau$,
    )),
    prooftree(rule(
      name: rn("New"),
      $CODATA T braces(D_1(Gamma_1) : tau_1, ...) in Theta$,
      $forall i: Gamma, Gamma_i tack p_i : tau_i$,
      $Theta mid Gamma tack NEW braces(D_1(Gamma_1) => p_1, ...) : T$,
    )),
    prooftree(rule(
      name: rn("Call"),
      $DEF f(Gamma') : tau braces(...) in Theta$,
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
      $NEW braces(D(Gamma) => s, ...)$,
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
      $CASE braces(K(Gamma) => s, ...)$,
    ),

    ($s$, "Statements"),
    alt(
      $cut(p, c)$,
      $IF p equiv 0 braces(s) ELSE braces(s)$,
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
      $DEF f(Gamma) : tau braces(p)$,
      $pi sp T braces(K(Gamma), ...)$,
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
  Producer Typing: $Theta mid Gamma tack p :^prd tau$
  #rule-set(
    prooftree(rule(
      name: rn("Act-R"),
      $Gamma, alpha :^cns tau tack s$,
      $Gamma tack mu a. s :^prd tau$,
    )),
    prooftree(rule(
      name: rn("New"),
      $CODATA T braces(D_1(Gamma_1), ...) in Theta$,
      $forall i: Gamma, Gamma_i tack s_i$,
      $Theta mid Gamma tack NEW braces(D_1(Gamma_1) => s_1, ...) :^prd T$,
    )),
  )
  The rules #rn("Var"), #rn("Ctor"), #rn("Plus") are identical to #Fun.

  #line(length: 100%)

  Consumer Typing: $Theta mid Gamma tack c :^cns tau$
  #rule-set(
    prooftree(rule(
      name: rn("Act-L"),
      $Gamma, x :^prd tau tack s$,
      $Gamma tack tilde(mu)x. s :^cns tau$,
    )),
    prooftree(rule(
      name: rn("Case"),
      $DATA T braces(K_1(Gamma_1), ...) in Theta$,
      $forall i: Gamma, Gamma_i tack s_i$,
      $Theta mid Gamma tack CASE braces(K_1(Gamma_1) => s_1, ...) :^cns T$,
    )),
    prooftree(rule(
      name: rn("Dtor"),
      $CODATA T braces(..., D(Gamma'), ...) in Theta$,
      $Theta mid Gamma tack sigma : Gamma'$,
      $Theta mid Gamma tack D(sigma) :^cns T$,
    )),
  )
  The rule #rn("Covar") is identical to #Fun.

  #line(length: 100%)

  Statement Typing: $Theta mid Gamma tack s$
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
      $Gamma tack IF p equiv 0 braces(s_1) ELSE braces(s_1)$,
    )),
    prooftree(rule(
      name: rn("Call"),
      $DEF f(Gamma') braces(...) in Theta$,
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
    f2c(DEF f(Gamma) : i64 braces(p)) & := DEF f(Gamma, alpha :^cns tau) braces(f2c(p, with: alpha)) quad(alpha "fresh") \
    f2c(DEF "main"(Gamma) : i64 braces(p)) & := DEF "main"(Gamma) braces(f2c(p, with: tilde(mu)x.EXIT x)) \
    f2c(CODATA T braces(D_1(Gamma_1): tau_1, ...)) & := CODATA T braces(D_1(Gamma_1, alpha_1 :^cns tau_1), ...) quad(alpha_1, ... "fresh") \
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
    f2c(LABEL alpha braces(p)) &:= mu alpha. f2c(p, with: alpha) \
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
#todo[TODO]

== The Shrinking Transformation
#todo[TODO]

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
    $SWITCH v braces(X(Gamma) => s, ...)$,
    $CREATE v = Gamma braces(X(Gamma) => s, ...); sp s$,
    $LIT v <- n; sp s$,
    $v <- v + v; sp s$,
    $IF v equiv 0 braces(s) ELSE braces(s)$,
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
      $Gamma tack IF v equiv 0 braces(s_1) ELSE braces(s_2)$,
    )),
  )

  #line(length: 100%)

  #rule-set(
    prooftree(rule(
      name: rn("Call"),
      $DEF f(Gamma) braces(...) in Theta$,
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
      $pi T braces(..., X(Gamma_0), ...) in Theta$,
      $Gamma, v:^(chi_1(pi)) T tack s$,
      $Theta mid Gamma, Gamma_0 tack LET v = X(Gamma_0); sp s$,
    )),
    prooftree(rule(
      name: $#rn("Create-")pi$,
      $pi T braces(X_1(Gamma_1), ...) in Theta$,
      $Gamma, v:^(chi_2(pi)) T tack s$,
      $forall i: Gamma_i, Gamma_0 tack s_i$,
      $Theta mid Gamma, Gamma_0 tack CREATE v = Gamma_0 braces(X_1(Gamma_1) => s_1, ...); sp s$,
    )),
    prooftree(rule(
      name: $#rn("Switch-")pi$,
      $pi T braces(X_1(Gamma_1), ...) in Theta$,
      $forall i: Gamma, Gamma_i tack s_i$,
      $Theta mid Gamma, v :^(chi_1(pi)) T tack SWITCH v braces(X_1(Gamma_1) => s_1, ...)$,
    )),
    prooftree(rule(
      name: $#rn("Invoke-")pi$,
      $pi T braces(..., X(Gamma), ...) in Theta$,
      $Theta mid Gamma, v :^(chi_2(pi)) T tack INVOKE v sp X(Gamma)$,
    )),
  )
]

== Translation from #Core to #AxCut
#todo[TODO]

== Translation from #AxCut to #RISC-V machine code
#todo[TODO]

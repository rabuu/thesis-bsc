#import "/lib/lib.typ": *

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
      $Gamma tack GOTO alpha sp (p) : tau'$,
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
#inline-note[Maybe a section about how Fun now loses classical expression and gets intuitionsistic.]

== Restricting #Core
#todo[TODO]

=== Typing Rules
#figure(
  kind: "Figure",
  supplement: "Figure",
)[
  #judgment-box[Producer Typing: $Theta mid Gamma tack p :^prd tau$]

  #rule-set(
    manual-grouping: true,
    (
      mark(prooftree(rule(
        name: rn("Var"),
        $x :^prd_q tack x :^prd tau$,
      ))),
      prooftree(rule(
        name: rn("Act-R"),
        $Gamma, alpha mark(:^cns_q) tau tack s$,
        $Gamma tack mark(mu_q) a. s :^prd tau$,
      )),
    ),
    (
      prooftree(rule(
        name: rn("Lit"),
        $Gamma tack n :^prd i64$,
      )),
      prooftree(rule(
        name: rn("Plus"),
        $mark(Gamma_1) tack p_1 :^prd i64$,
        $mark(Gamma_2) tack p_2 :^prd i64$,
        $mark(Gamma_1 plus.o Gamma_2) tack p_1 + p_2 :^prd i64$,
      )),
    ),
    (
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
    ),
  )

  #judgment-box[Consumer Typing: $Theta mid Gamma tack c :^cns tau$]

  #rule-set(
    manual-grouping: true,
    (
      mark(prooftree(rule(
        name: rn("Covar"),
        $alpha :^cns_q tack alpha :^cns tau$,
      ))),
      prooftree(rule(
        name: rn("Act-L"),
        $Gamma, x mark(:^prd_q) tau tack s$,
        $Gamma tack mark(tilde(mu)_q) x. s :^cns tau$,
      )),
    ),
    (
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
    ),
  )

  #judgment-box[Statement Typing: $Theta mid Gamma tack s$]

  #rule-set(
    prooftree(rule(
      name: rn("Cut"),
      $mark(Gamma_1) tack p :^prd tau$,
      $mark(Gamma_2) tack c :^cns tau$,
      $mark(Gamma_1 plus.o Gamma_2) tack cut(p, c)$,
    )),
    prooftree(rule(
      name: rn("IfZ"),
      $mark(Gamma_1) tack p :^prd i64$,
      $mark(Gamma_2) tack s_1$,
      $mark(Gamma_2) tack s_2$,
      $mark(Gamma_1 plus.o Gamma_2) tack IF p equiv 0 br(s_1) ELSE br(s_1)$,
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

#inline-note[Structural rules. Rules for arguments.]

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

== Focusing & Shrinking
#todo[TODO]

== Linearity in #AxCut

=== Syntax
#figure[
  #bnf(
    ($v$, "(Co)Variables"),
    alt(
      $var(x)$,
      $covar(alpha)$,
    ),

    ($s$, "Statements"),
    $mark(LET_q) v = X(sigma); sp s$,
    $INVOKE v sp X(sigma)$,
    $SWITCH v br(X(Gamma) => s, ...)$,
    $mark(CREATE_q) v = Gamma br(X(Gamma) => s, ...); sp s$,
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
#todo[TODO]

== Translation from #Core to #AxCut
#todo[TODO]

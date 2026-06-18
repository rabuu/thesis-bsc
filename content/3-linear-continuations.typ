#import "/lib/lib.typ": *

= Linear Continuations

== What is a Continuation?
#todo[TODO]

== Which Continuations are Linear?
#todo[TODO]

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
  )
]

=== Intuitionistic!
#inline-note[Maybe a section about how Fun now loses classical expression and gets intuitionistic.]

== Restricting #Core
#todo[TODO]

=== Syntax
#figure[
  #bnf(
    ($p$, "Producers"),
    alt(
      $var(x)$,
      $mu alpha. s$,
    ),
    alt(
      $n$,
      $p + p$,
    ),
    alt(
      $K(sigma)$,
      $NEW br(D(Gamma; alpha :^cns tau) => s, ...)$,
    ),

    ($c$, "Consumers"),
    alt(
      $covar(alpha)$,
      $tilde(mu) x. s$,
    ),
    alt(
      $D(sigma; c)$,
      $CASE br(K(Gamma) => s, ...)$,
    ),

    ($s$, "Statements"),
    alt(
      $cut(p, c)$,
    ),
    alt(
      $IF p equiv 0 br(s) ELSE br(s)$,
    ),
    alt(
      $f(sigma; c)$,
      $EXIT p$,
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

    ($sigma$, "Arguments (Producer)"),
    alt(
      $empty$,
      $sigma, sp p$,
    ),

    ($Gamma$, "Typing Contexts (Producer)"),
    alt(
      $empty$,
      $Gamma, sp x :^prd tau$,
    ),

    ($Delta$, "Typing Contexts (Consumer)"),
    alt(
      $empty$,
      $alpha :^cns tau$,
    ),

    ($pi$, "Polarity"),
    alt(
      $DATA$,
      $CODATA$,
    ),

    ($delta$, "Declarations"),
    alt(
      $DEF f(Gamma; Delta) br(s)$,
    ),
    alt(
      $DATA sp T br(K(Gamma), ...)$,
    ),
    alt(
      $CODATA sp T br(D(Gamma;Delta), ...)$,
    ),

    ($Theta$, "Programs"),
    alt(
      $empty$,
      $Theta, sp delta$,
    ),
  )
]

=== Typing Rules
#figure(
  kind: "Figure",
  supplement: "Figure",
  caption: [Typing rules for #Core.],
)[
  #def-box[Producer Typing: $Theta mid Gamma;Delta tack p :^prd tau$]

  #rule-set(
    manual-grouping: true,
    (
      prooftree(rule(
        name: rn("Var"),
        $x :^prd tau in Gamma$,
        $Gamma;Delta tack x :^prd tau$,
      )),
      prooftree(rule(
        name: rn("Act-R"),
        $Gamma; alpha :^cns tau tack s$,
        $Gamma; empty tack mu a. s :^prd tau$,
      )),
    ),
    (
      prooftree(rule(
        name: rn("Lit"),
        $Gamma;Delta tack n :^prd i64$,
      )),
      prooftree(rule(
        name: rn("Plus"),
        $Gamma;Delta_1 tack p_1 :^prd i64$,
        $Gamma;Delta_2 tack p_2 :^prd i64$,
        $Gamma;Delta_1 plus.o Delta_2 tack p_1 + p_2 :^prd i64$,
      )),
    ),
    (
      prooftree(rule(
        name: rn("Ctor"),
        $DATA T br(..., K(Gamma'), ...) in Theta$,
        $Theta mid Gamma;Delta tack sigma : Gamma'$,
        $Theta mid Gamma;Delta tack K(sigma) :^prd T$,
      )),
      prooftree(rule(
        name: rn("New"),
        $CODATA T br(D_1(Gamma_1;alpha :^cns tau), ...) in Theta$,
        $forall i: Gamma, Gamma_i;alpha :^cns tau tack s_i$,
        $Theta mid Gamma;empty tack NEW br(D_1(Gamma_1; alpha :^cns tau) => s_1, ...) :^prd T$,
      )),
    ),
  )

  #def-box[Consumer Typing: $Theta mid Gamma;Delta tack c :^cns tau$]

  #rule-set(
    manual-grouping: true,
    (
      prooftree(rule(
        name: rn("Covar"),
        $Gamma; alpha :^cns tau tack alpha :^cns tau$,
      )),
      prooftree(rule(
        name: rn("Act-L"),
        $Gamma, x :^prd tau; Delta tack s$,
        $Gamma;Delta tack tilde(mu)x. s :^cns tau$,
      )),
    ),
    (
      prooftree(rule(
        name: rn("Dtor"),
        $CODATA T br(..., D(Gamma'; alpha :^cns tau), ...) in Theta$,
        $Theta mid Gamma tack sigma : Gamma'$,
        $Theta mid Gamma; Delta tack c :^cns tau$,
        $Theta mid Gamma; Delta tack D(sigma;c) :^cns T$,
      )),
      prooftree(rule(
        name: rn("Case"),
        $DATA T br(K_1(Gamma_1), ...) in Theta$,
        $forall i: Gamma, Gamma_i; Delta tack s_i$,
        $Theta mid Gamma; Delta tack CASE br(K_1(Gamma_1) => s_1, ...) :^cns T$,
      )),
    ),
  )

  #def-box[Statement Typing: $Theta mid Gamma; Delta tack s$]

  #rule-set(
    prooftree(rule(
      name: rn("Cut"),
      $Gamma; Delta_1 tack p :^prd tau$,
      $Gamma; Delta_2 tack c :^cns tau$,
      $Gamma; Delta_1 plus.o Delta_2 tack cut(p, c)$,
    )),
    prooftree(rule(
      name: rn("IfZ"),
      $Gamma; Delta_1 tack p :^prd i64$,
      $Gamma; Delta_2 tack s_1$,
      $Gamma; Delta_2 tack s_2$,
      $Gamma; Delta_1 plus.o Delta_2 tack IF p equiv 0 br(s_1) ELSE br(s_1)$,
    )),
    prooftree(rule(
      name: rn("Call"),
      $DEF f(Gamma'; alpha :^cns tau) br(...) in Theta$,
      $Theta mid Gamma tack sigma : Gamma'$,
      $Theta mid Gamma; Delta tack c :^cns tau$,
      $Theta mid Gamma; Delta tack f(sigma; c)$,
    )),
    prooftree(rule(
      name: rn("Exit"),
      $Gamma; Delta tack p :^prd i64$,
      $Gamma; Delta tack EXIT p$,
    )),
  )
]

#inline-note[Structural rules. Rules for arguments.]

=== Linearity & Intuitionistic
#inline-note[This resembles Gentzen's LJ :O]

== Translation from #Fun to #Core
#todo[TODO]

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

    ($q$, "Quantities"),
    alt(
      $omega$,
      $1$,
    ),

    ($s$, "Statements"),
    $mark(LET_q) v = X(sigma); sp s$,
    $mark(CREATE_q) v = Gamma br(X(Gamma) => s, ...); sp s$,
    $mark(SWITCH_q) v br(X(Gamma) => s, ...)$,
    $INVOKE v sp X(sigma)$,
    $LIT v <- n; sp s$,
    $v <- v + v; sp s$,
    $IF v equiv 0 br(s) ELSE br(s)$,
    $f(sigma)$,
    $EXIT v$,
    $SUBSTITUTE[Gamma := sigma]; sp s$,

    ($sigma$, "Arguments"),
    alt(
      $empty$,
      $sigma, sp v$,
    ),
  )
]

=== Typing Rules
#figure[
  #def-box[Statement Typing: $Theta mid Gamma tack s$]
  #rule-set(
    manual-grouping: true,
    (
      prooftree(rule(
        name: $#rn("Let-")pi$,
        $pi T br(..., X(Gamma_0), ...) in Theta$,
        $Gamma, mark(v :^(chi_1(pi))_q) T tack s$,
        $Theta mid Gamma, Gamma_0 tack mark(LET_q) sp v = X(Gamma_0); sp s$,
      )),
      prooftree(rule(
        name: $#rn("Create-")pi$,
        $pi T br(X_1(Gamma_1), ...) in Theta$,
        $Gamma, mark(v :^(chi_2(pi))_q) T tack s$,
        $forall i: Gamma_i, Gamma_0 tack s_i$,
        $Theta mid Gamma, Gamma_0 tack mark(CREATE_q) sp v = Gamma_0 br(X_1(Gamma_1) => s_1, ...); sp s$,
      )),
      prooftree(rule(
        name: $#rn("Switch-")pi$,
        $pi T br(X_1(Gamma_1), ...) in Theta$,
        $forall i: Gamma, Gamma_i tack s_i$,
        $Theta mid Gamma, mark(v :^(chi_1(pi))_q) T tack mark(SWITCH_q) sp v br(X_1(Gamma_1) => s_1, ...)$,
      )),
      prooftree(rule(
        name: $#rn("Invoke-")pi$,
        $pi T br(..., X(Gamma), ...) in Theta$,
        $Theta mid Gamma, mark(v :^(chi_2(pi))_q) T tack INVOKE v sp X(Gamma)$,
      )),
    ),
    (
      prooftree(rule(
        name: rn("Substitute"),
        $Gamma tack sigma : Gamma'$,
        $Gamma' tack s$,
        inline-note[linear bindings cannot be shared or erased],
        $Gamma tack SUBSTITUTE[Gamma' := sigma]; sp s$,
      )),
    ),
    (
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
    ),
    (
      prooftree(rule(
        name: rn("IfZ"),
        $v :^prd i64 in Gamma$,
        $Gamma tack s_1$,
        $Gamma tack s_2$,
        $Gamma tack IF v equiv 0 br(s_1) ELSE br(s_2)$,
      )),
      prooftree(rule(
        name: rn("Call"),
        $DEF f(Gamma) br(...) in Theta$,
        $Theta mid Gamma tack f(Gamma)$,
      )),
      prooftree(rule(
        name: rn("Exit"),
        $v :^prd i64 in Gamma$,
        $Gamma tack EXIT v$,
      )),
    ),
  )
]

== Translation from #Core to #AxCut
#figure[
  #set math.lr(size: 1em)

  #def-box[$c2a(dot, ctx: dot.o) : "Statement"_("Shrunk" Core) times "Context"_AxCut -> "Statement"_AxCut$]
  $
    c2a(cut(K(Gamma_0), tilde(mu)x. s), ctx: Gamma) & := && SUBSTITUTE[Gamma' := Gamma', Gamma_0^f := Gamma_0]; \
    &&& mark(LET_omega) sp x = K(Gamma_0^f); sp c2a(s, ctx: Gamma'\, x) \
    "where" &&& Gamma' = "freeVars"(s) subset Gamma \
    c2a(cut(mu alpha. s, D(Gamma_0)), ctx: Gamma) & := && SUBSTITUTE[Gamma' := Gamma', Gamma_0^f := Gamma_0]; \
    &&& mark(LET_1) sp alpha = D(Gamma_0^f); sp c2a(s, ctx: Gamma'\, alpha) \
    "where" &&& Gamma' = "freeVars"(s) subset Gamma \
    c2a(cut(x, CASE br(K_1(Gamma_1) => s_1, ...)), ctx: Gamma) & := && SUBSTITUTE[Gamma' := Gamma', x^f := x]; \
    &&& mark(SWITCH_omega) sp x br(K_1(Gamma_1) => c2a(s_1, ctx: Gamma'\,Gamma_1), ...) \
    "where" &&& Gamma' = union.big_i "freeVars"(s_i) subset Gamma \
    c2a(cut(NEW br(D_1(Gamma_1) => s_1, ...), alpha), ctx: Gamma) & := && SUBSTITUTE[Gamma' := Gamma', alpha^f := alpha]; \
    &&& mark(SWITCH_1) sp alpha br(D_1(Gamma_1) => c2a(s_1, ctx: Gamma'\,Gamma_1), ...) \
    "where" &&& Gamma' = union.big_i "freeVars"(s_i) subset Gamma \
    c2a(cut(mu alpha. s, CASE br(K_1(Gamma_1) => s_1, ...)), ctx: Gamma) & := && SUBSTITUTE[Gamma'^f := Gamma', Gamma_0 := Gamma_0]; \
    &&& mark(CREATE_1) sp alpha = Gamma_0 br(K_1(Gamma_1) => c2a(s_1, ctx: Gamma_1\, Gamma_0), ...); \
    &&& c2a(s[Gamma' mapsto Gamma'^f], ctx: Gamma'^f\, alpha) \
    "where" &&& Gamma_0 = union.big_i "freeVars"(s_i) subset Gamma quad Gamma' = "freeVars"(s) subset Gamma \
    c2a(cut(NEW br(D_1(Gamma_1) => s_1, ...), tilde(mu)x. s), ctx: Gamma) & := && SUBSTITUTE[Gamma'^f := Gamma', Gamma_0 := Gamma_0]; \
    &&& mark(CREATE_omega) sp x = Gamma_0 br(K_1(Gamma_1) => c2a(s_1, ctx: Gamma_1\, Gamma_0), ...); \
    &&& c2a(s[Gamma' mapsto Gamma'^f], ctx: Gamma'^f\, x) \
    "where" &&& Gamma_0 = union.big_i "freeVars"(s_i) subset Gamma quad Gamma' = "freeVars"(s) subset Gamma \
  $
]

#inline-note[The (maybe) new #Core syntax is not used here yet. Maybe also include other cases.]

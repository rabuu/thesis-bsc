#import "/lib/lib.typ": *

#import prooftree: *
#import syntax: *
#show: syntax.syntax-config

= Background

== The Surface Language #Fun

=== Syntax
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

=== Typing Rules

_Argument Typing:_ $Theta mid Gamma tack sigma : Gamma'$
#rule-set(
  prooftree(rule(
    name: rn("Arg1"),
    $Theta mid Gamma tack empty : empty$,
  )),
  prooftree(rule(
    name: rn("Arg2"),
    $Theta mid Gamma tack sigma : Gamma'$,
    $Theta mid Gamma tack p : tau$,
    $Theta mid Gamma tack (sigma,p) : (Gamma', sp x:tau)$,
  )),
  prooftree(rule(
    name: rn("Arg2"),
    $Theta mid Gamma tack sigma : Gamma'$,
    $Theta mid Gamma tack c :^cns tau$,
    $Theta mid Gamma tack (sigma,c) : (Gamma', sp alpha:^cns tau)$,
  )),
)

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

_Consumer Typing:_ $Theta mid Gamma tack c :^cns tau$
#rule-set(
  prooftree(rule(
    name: rn("Covar"),
    $alpha :^cns tau in Gamma$,
    $Gamma tack alpha :^cns tau$,
  )),
)

== The High-Level Intermediate Language #Core

=== Syntax
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

== The Lower-Level Intermediate Language #AxCut

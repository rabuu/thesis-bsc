#import "/lib/lib.typ": *

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

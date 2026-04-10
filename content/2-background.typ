#import "/lib/lib.typ": *

= Background

== The Surface Language #Fun

=== Syntax
#import syntax.fun: *
#show sym.colon: math.scripts

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

== The Lower-Level Intermediate Language #AxCut

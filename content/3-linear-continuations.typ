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
    $EXIT p$,
    erase(alt(
      $LABEL alpha braces(p)$,
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
      $Gamma tack IF p equiv 0 braces(p_1) ELSE braces(p_2) : tau$,
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

  #rule-set(
    erase(prooftree(rule(
      name: rn("Label"),
      $Gamma, alpha :^cns tau tack p : tau$,
      $Gamma tack LABEL alpha braces(p) : tau$,
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

== Translation from #Fun to #Core
#figure[
  $f2c(dot) : "Declaration"_Fun -> "Declaration"_Core$
  $
    f2c(DEF f(Gamma) : i64 braces(p)) & := DEF f(Gamma, alpha mark(:_1^cns) tau) braces(f2c(p, with: alpha)) quad(alpha "fresh") \
    f2c(DEF "main"(Gamma) : i64 braces(p)) & := DEF "main"(Gamma) braces(f2c(p, with: tilde(mu)x.EXIT x)) \
    f2c(CODATA T braces(D_1(Gamma_1): tau_1, ...)) & := CODATA T braces(D_1(Gamma_1, alpha_1 mark(:_1^cns) tau_1), ...) quad(alpha_1, ... "fresh") \
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
    mark(f2c(f(sigma)) & := mu_1 alpha. f(f2c(sigma), alpha)) \
    f2c(p) & := #note[Should this be linear?] mu alpha. f2c(p, with: alpha) quad "for all other producers" p \
  $
  $
    erase(f2c(LABEL sp alpha sp braces(p)) & := mu alpha. f2c(p, with: alpha)) \
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
  $
    erase(f2c(LABEL alpha braces(p), with: c) & := && cut(mu alpha. f2c(p, with: alpha), c)) \
    erase(f2c(GOTO alpha sp (p), with: c) & := && f2c(p, with: alpha)) \
  $
]

#line(length: 100%)

#figure[
  $f2c(dot) : "Arguments"_Fun -> "Arguments"_Core$
  $
        f2c(empty) & := empty \
    f2c(sigma\, p) & := f2c(sigma), f2c(p) \
  $
  $
    erase(f2c(sigma\, alpha) & := f2c(sigma)\, alpha)
  $
]


== The Focusing Transformation

== The Shrinking Transformation

== Linearity in #AxCut

== Translation from #Core to #AxCut

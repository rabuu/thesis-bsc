#import "/lib/lib.typ": *

= Supplementary Formalization <app:form>

== Typing Rules for #Fun <app:form:fun:typing>
To keep the presentation concise, well-formedness rules for programs and declarations are omitted.
We assume that all types and names that are used in the program are well-defined and unique.

There are three judgment forms for producers, consumers, and argument lists, respectively.
The judgment $Theta mid Gamma tack p : tau$ means that under the global context $Theta$, which keeps track of top-level declarations,
and the local context $Gamma$, which keeps track of currently active (co)variable bindings, the term $p$ has the type $tau$.
Similarly, $Theta mid Gamma tack c :^cns tau$ denotes that $c$ is a well-typed consumer of $tau$.
The judgment $Theta mid Gamma tack sigma : Gamma'$ means that the arguments list $sigma$ matches the parameter list $Gamma'$.
In many rules, the global context $Theta$ is not referenced.
If that is the case, it is omitted to improve readability.

#figure(
  block(width: 100%)[
    #def-box[Producer Typing: $Theta mid Gamma tack p : tau$]

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
        $Gamma tack GOTO alpha sp (p) : tau'$,
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

    #def-box[Consumer Typing: $Theta mid Gamma tack c :^cns tau$]

    #rule-set(
      prooftree(rule(
        name: rn("Covar"),
        $alpha :^cns tau in Gamma$,
        $Gamma tack alpha :^cns tau$,
      )),
    )

    #def-box[Argument Typing: $Theta mid Gamma tack sigma : Gamma'$]

    #rule-set(
      column-gutter: 1.3em,
      prooftree(rule(
        name: $rn("Arg"_empty)$,
        $Gamma tack empty : empty$,
      )),
      prooftree(rule(
        name: $rn("Arg"_prd)$,
        $Gamma tack sigma : Gamma'$,
        $Gamma tack p : tau$,
        $Gamma tack (sigma,p) : (Gamma', sp x:tau)$,
      )),
      prooftree(rule(
        name: $rn("Arg"_cns)$,
        $Gamma tack sigma : Gamma'$,
        $Gamma tack c :^cns tau$,
        $Gamma tack (sigma,c) : (Gamma', sp alpha:^cns tau)$,
      )),
    )
  ],
)

== Lifting Non-(Co)Values <app:form:bindval>

#figure(
  bnf(
    row-gutter: 1.2em,
    ($phi$, "Value"),
    alt(
      $n$,
      $K(overline(psi))$,
      $NEW#hide[`E`] { ... }$,
      $p quad "where" p :^prd CODATA T sp { ... }$,
    ),

    ($phi.alt$, "Covalue"),
    alt(
      $#hide[$n quad | quad$]D(overline(psi))$,
      $CASE { ... }$,
      $c quad " unless" c :^cns CODATA T sp { ... }$,
    ),

    ($psi$, "(Co)Value"),
    alt($phi$, $phi.alt$),
  ),
)

#figure(
  block(width: 100%)[
    #def-box(
      $bindval(dot, dot) : "Argument"_Core -> ("(Co)Value"_Core -> "Statement"_Core) -> "Statement"_Core$,
    )
    $
      bindval(e, k) & := && cut(e, tilde(mu)x. k(x)) && quad quad #text(font: settings.font-serif, weight: "bold", "if") e eq.not psi \
      bindval(psi, k) & := && k(psi)
    $

    #def-box(
      $bindvals(dot, dot) : "Arguments"_Core -> ("(Co)Values"_Core -> "Statement"_Core) -> "Statement"_Core$,
    )
    $
      bindvals(empty, k) & := && k(empty) \
      bindvals(e :: sigma, k) & := && bindval(e, lambda a. bindvals(sigma, lambda overline(a). k(a :: overline(a))))
    $
  ],
)

== The Focusing Transformation
#figure(
  block(width: 100%)[
    #def-box[$focus(dot) : "Definition"_Core -> "Definition"_("Focused" Core)$]
    $
      focus(DEF f(Gamma) br(s)) & := && DEF f(Gamma) br(focus(s))
    $

    #def-box[$focus(dot) : "Statement"_Core -> "Statement"_("Focused" Core)$]
    $
      focus(cut(p_1 + p_2, c)) & := && bind(p_1, lambda a_1. bind(p_2, lambda a_2. cut(a_1 + a_2, focus(c)))) \
      focus(cut(K(sigma), c)) & := && bindargs(sigma, lambda overline(a). cut(K(overline(a)), focus(c))) \
      focus(cut(p, D(sigma))) & := && bindargs(sigma, lambda overline(a). cut(focus(p), D(overline(a)))) \
      focus(cut(p, c)) & := && cut(focus(p), focus(c)) \
      focus(IF p equiv 0 br(s_1) ELSE br(s_2)) & := && bind(p, lambda a. IF a equiv 0 br(focus(s_1)) ELSE br(focus(s_2))) \
      focus(f(sigma)) & := && bindargs(sigma, lambda overline(a). f(overline(a))) \
      focus(EXIT p) & := && bind(p, lambda a. EXIT a)
    $

    #def-box[$focus(dot) : "Producer"_Core -> "Producer"_("Focused" Core)$]
    $
      focus(x) & := && x \
      focus(mu alpha. s) & := && mu alpha. focus(s) \
      focus(NEW br(D_1(Gamma_1) => s_1, ...)) & := && NEW br(D_1(Gamma_1) => focus(s_1), ...) \
      focus(K(sigma)) &&& "does not occur" \
      focus(n) & := && n \
      focus(p_1 + p_2) &&& "does not occur"
    $

    #def-box[$focus(dot) : "Consumer"_Core -> "Consumer"_("Focused" Core)$]
    $
      focus(alpha) & := && alpha \
      focus(tilde(mu) x. s) & := && tilde(mu) x. focus(s) \
      focus(CASE br(K_1(Gamma_1) => s_1, ...)) & := && CASE br(K_1(Gamma_1) => focus(s_1), ...) \
      focus(D(sigma)) &&& "does not occur" \
    $
  ],
)

#figure(
  block(width: 100%)[
    #def-box[$bind(dot, dot) : "Producer"_Core times ("Var" -> "Statement"_("Focused" Core)) -> "Statement"_("Focused" Core)$]
    $
      bind(x, k) & := && k(x) \
      bind(mu alpha. s, k) & := && cut(mu alpha. focus(s), tilde(mu) x. k(x)) \
      bind(K(sigma), k) & := && bindargs(sigma, lambda overline(a). cut(K(overline(a)), tilde(mu) x. k(x))) \
      bind(NEW br(D_1(Gamma_1) => s_1, ...), k) & := && cut(NEW br(D_1(Gamma_1) => focus(s_1), ...), tilde(mu) x. k(x)) \
      bind(n, k) & := && cut(n, tilde(mu) x. k(x)) \
      bind(p_1 + p_2, k) & := && bind(p_1, lambda a_1. bind(p_2, lambda a_2. cut(a_1 + a_2, tilde(mu) x. k(x))))
    $

    #def-box[$bind(dot, dot) : "Consumer"_Core times ("Covar" -> "Statement"_("Focused" Core)) -> "Statement"_("Focused" Core)$]
    $
      bind(alpha, k) & := && k(alpha) \
      bind(tilde(mu) x. s, k) & := && cut(mu alpha. k(alpha), tilde(mu) x. focus(s)) \
      bind(D(sigma), k) & := && bindargs(sigma, lambda overline(a). cut(mu alpha. k(alpha), D(overline(a)))) \
      bind(CASE br(K_1(Gamma_1) => s_1, ...), k) & := && cut(mu alpha. k(alpha), CASE br(K_1(Gamma_1) => focus(s_1), ...)) \
    $

    #def-box[$bindargs(dot, dot) : "Args"_Core times ("Context" -> "Statement"_("Focused" Core)) -> "Statement"_("Focused" Core)$]
    $
      bindargs(empty, k) & := && k(empty) \
      bindargs(e :: sigma, k) & := && bind(e, lambda a. bindargs(sigma, lambda overline(a). k(a :: overline(a))))
    $
  ],
)


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

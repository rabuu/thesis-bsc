#import "/lib/lib.typ": *

= Linear Continuations <ch:lin>

== What is a Continuation?
#todo[TODO]

== Which Continuations are Linear?
#todo[TODO]

== Restricting the Surface Language #Fun
As we have seen, correctly identifying which continuations are used linearly is much harder for programs using non-local control flow.
Therefore, we restrict the optimization that this thesis explores to a certain subset of #Fun programs,
i.e. programs that do not make use of the $LABEL$ and $GOTO$ constructs.

This restrictions leaves us with a less interesting but much more predictable language where control flow is completely implicit.
And because of this implicitness we can be sure that every continuation is perfectly linear.

=== Syntax
The syntax of this restricted version of #Fun is, in comparison to @def:scc:fun, much simpler.
By removing $LABEL$ and $GOTO$ from the language, we also lose the need for explicit covariables, and hence consumers in general.

#definition(title: [Restricted #Fun])[
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

      ($sigma$, "Arguments"),
      alt(
        $empty$,
        $sigma, sp p$,
      ),

      ($Gamma$, "Typing Contexts"),
      alt(
        $empty$,
        $Gamma, sp x : tau$,
      ),
    )
  ]
]

=== Intuitionistic!
#inline-note[Maybe a section about how Fun now loses classical expression and gets intuitionistic.]

=== Typing?
#inline-note[This boring but I should add some note.]

== Restricting #Core
The goal is now to retain the information about linear continuations that we gained by restricting #Fun,
to finally use it to optimize code generation.
But in #Core there is nothing like $LABEL$ and $GOTO$ from #Fun that we can simply forbid.
Instead, all continuations are explicit now, and we must structurally ensure that they are used linearly.

The key idea here is that, coming from #Fun, every continuation and consumer must be linear anyway,
since in #Fun there is just no way to construct something that would result in a nonlinear usage of consumers.

In theory, it would suffice to keep #Core and the translation to it as is, remembering that every continuation must be linear.
But to make the correctness of the following optimization obvious,
we identify the subset of #Core that can result from the restricted version of #Fun.

=== Syntax
We will show in @sec:lin:f2c that restricted #Fun can be translated to the following restricted fragment of #Core.
Note that it is a strict subset of @def:scc:core.

#definition(title: [Restricted #Core])[
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
        $NEW br(D(Gamma, alpha :^cns tau) => s, ...)$,
      ),

      ($c$, "Consumers"),
      alt(
        $covar(alpha)$,
        $tilde(mu) x. s$,
      ),
      alt(
        $D(sigma, c)$,
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
        $f(sigma, c)$,
        $EXIT p$,
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

      ($delta$, "Declarations"),
      alt(
        $DEF f(Gamma, Delta) br(s)$,
      ),
      alt(
        $DATA sp T br(K(Gamma), ...)$,
      ),
      alt(
        $CODATA sp T br(D(Gamma, Delta), ...)$,
      ),
    )
  ]
]

In #Core programs that are translated from the restricted fragment of #Fun,
all covariables and consumer arguments must stem from the translation process.
In argument and parameter lists, they are exactly the added arguments that correspond to the implicit continuation in #Fun.

Here, this is made explicit by splitting arguments, parameters, and typing contexts into parts for producers and consumers, respectively.
In this restricted version of #Core, every top-level definition --- except the special entry point `main` which is omitted here ---
and every destructor has exactly one consumer argument at the end.
And constructors cannot have any consumer field.

=== Typing Rules
#figure(
  kind: "Figure",
  supplement: "Figure",
  caption: [Typing rules for #Core.],
  block(width: 100%)[
    #def-box[Producer Typing: $Theta mid Gamma, Delta tack p :^prd tau$]

    #rule-set(
      manual-grouping: true,
      (
        prooftree(rule(
          name: rn("Var"),
          $x :^prd tau in Gamma$,
          $Gamma, Delta tack x :^prd tau$,
        )),
        prooftree(rule(
          name: rn("Act-R"),
          $Gamma, alpha :^cns tau tack s$,
          $Gamma tack mu a. s :^prd tau$,
        )),
      ),
      (
        prooftree(rule(
          name: rn("Lit"),
          $Gamma, Delta tack n :^prd i64$,
        )),
        prooftree(rule(
          name: rn("Plus"),
          $Gamma, Delta_1 tack p_1 :^prd i64$,
          $Gamma, Delta_2 tack p_2 :^prd i64$,
          $Gamma, Delta_1 plus.o Delta_2 tack p_1 + p_2 :^prd i64$,
        )),
      ),
      (
        prooftree(rule(
          name: rn("Ctor"),
          $DATA T br(..., K(Gamma'), ...) in Theta$,
          $Theta mid Gamma, Delta tack sigma : Gamma'$,
          $Theta mid Gamma, Delta tack K(sigma) :^prd T$,
        )),
        prooftree(rule(
          name: rn("New"),
          $CODATA T br(D_1(Gamma_1, alpha_1 :^cns tau), ...) in Theta$,
          $forall i: Gamma, Gamma_i, alpha_i :^cns tau tack s_i$,
          $Theta mid Gamma tack NEW br(D_1(Gamma_1, alpha_1 :^cns tau) => s_1, ...) :^prd T$,
        )),
      ),
    )

    #def-box[Consumer Typing: $Theta mid Gamma, Delta tack c :^cns tau$]

    #rule-set(
      manual-grouping: true,
      (
        prooftree(rule(
          name: rn("Covar"),
          $Gamma, alpha :^cns tau tack alpha :^cns tau$,
        )),
        prooftree(rule(
          name: rn("Act-L"),
          $Gamma, x :^prd tau, Delta tack s$,
          $Gamma, Delta tack tilde(mu)x. s :^cns tau$,
        )),
      ),
      (
        prooftree(rule(
          name: rn("Dtor"),
          $CODATA T br(..., D(Gamma', alpha :^cns tau), ...) in Theta$,
          $Theta mid Gamma, Delta_1 tack sigma : Gamma'$,
          $Theta mid Gamma, Delta_2 tack c :^cns tau$,
          $Theta mid Gamma, Delta_1 plus.o Delta_2 tack D(sigma, c) :^cns T$,
        )),
        prooftree(rule(
          name: rn("Case"),
          $DATA T br(K_1(Gamma_1), ...) in Theta$,
          $forall i: Gamma, Gamma_i, Delta tack s_i$,
          $Theta mid Gamma, Delta tack CASE br(K_1(Gamma_1) => s_1, ...) :^cns T$,
        )),
      ),
    )

    #def-box[Statement Typing: $Theta mid Gamma, Delta tack s$]

    #rule-set(
      prooftree(rule(
        name: rn("Cut"),
        $Gamma, Delta_1 tack p :^prd tau$,
        $Gamma, Delta_2 tack c :^cns tau$,
        $Gamma, Delta_1 plus.o Delta_2 tack cut(p, c)$,
      )),
      prooftree(rule(
        name: rn("IfZ"),
        $Gamma, Delta_1 tack p :^prd i64$,
        $Gamma, Delta_2 tack s_1$,
        $Gamma, Delta_2 tack s_2$,
        $Gamma, Delta_1 plus.o Delta_2 tack IF p equiv 0 br(s_1) ELSE br(s_1)$,
      )),
      prooftree(rule(
        name: rn("Call"),
        $DEF f(Gamma', alpha :^cns tau) br(...) in Theta$,
        $Theta mid Gamma, Delta_1 tack sigma : Gamma'$,
        $Theta mid Gamma, Delta_2 tack c :^cns tau$,
        $Theta mid Gamma, Delta_1 plus.o Delta_2 tack f(sigma, c)$,
      )),
      prooftree(rule(
        name: rn("Exit"),
        $Gamma, Delta tack p :^prd i64$,
        $Gamma, Delta tack EXIT p$,
      )),
    )
  ],
)

#inline-note[Structural rules. Rules for arguments.]

=== Linearity & Intuitionistic
#inline-note[This resembles Gentzen's LJ :O]

== Translation from #Fun to #Core <sec:lin:f2c>
#todo[TODO]

== Focusing & Shrinking
#todo[TODO]

== Linearity in #AxCut

=== Syntax
#definition(title: [#AxCut with Linearity Annotations])[
  #figure[
    #bnf(
      ($q$, "Quantities"),
      alt(
        $omega$,
        $1$,
      ),

      ($s$, "Statements"),
      $...$,
      $highlight(LET_q) sp v = X(sigma); sp s$,
      $highlight(CREATE_q) sp v = Gamma br(X(Gamma) => s, ...); sp s$,
      $highlight(SWITCH_q) sp v br(X(Gamma) => s, ...)$,
      $INVOKE v sp X(sigma)$,
    )
  ]
]

=== Typing Rules
#figure[
  #def-box[Statement Typing: $Theta mid Gamma tack s$]
  #rule-set(
    manual-grouping: true,
    (
      prooftree(rule(
        name: $#rn("Let") _1"-"pi$,
        $pi T br(..., X(Gamma_0), ...) in Theta$,
        $Gamma, mark(v :^(chi_1(pi))_1) T tack s$,
        $Theta mid Gamma, Gamma_0 tack mark(LET_1) sp v = X(Gamma_0); sp s$,
      )),
      prooftree(rule(
        name: $#rn("Let") _omega"-"pi$,
        $pi T br(..., X(Gamma_0), ...) in Theta$,
        $Gamma, mark(v :^(chi_1(pi))_omega) T tack s$,
        inline-note[$omega(Gamma_0) = Gamma_0$],
        $Theta mid Gamma, Gamma_0 tack mark(LET_omega) sp v = X(Gamma_0); sp s$,
      )),
      prooftree(rule(
        name: $#rn("Create") _1"-"pi$,
        $pi T br(X_1(Gamma_1), ...) in Theta$,
        $Gamma, mark(v :^(chi_2(pi))_1) T tack s$,
        $forall i: Gamma_i, Gamma_0 tack s_i$,
        $Theta mid Gamma, Gamma_0 tack mark(CREATE_1) sp v = Gamma_0 br(X_1(Gamma_1) => s_1, ...); sp s$,
      )),
      prooftree(rule(
        name: $#rn("Create") _omega"-"pi$,
        $pi T br(X_1(Gamma_1), ...) in Theta$,
        $Gamma, mark(v :^(chi_2(pi))_omega) T tack s$,
        $forall i: Gamma_i, Gamma_0 tack s_i$,
        inline-note[$omega(Gamma_0)=Gamma_0$],
        $Theta mid Gamma, Gamma_0 tack mark(CREATE_omega) sp v = Gamma_0 br(X_1(Gamma_1) => s_1, ...); sp s$,
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
        inline-note[Linearity Condition: $forall v in "lin"(Gamma). exists_1 v' in sigma. v = v'$],
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

#import "/lib/lib.typ": *

= Linear Continuations <ch:lin>
A central feature of the SCC is how it explicitly represents control flow,
leveraging the symmetric properties of data and computation contexts inherited from the sequent calculus.
Consumers as a first-class construct naturally allow for very powerful and flexible handling of control flow.

But not all programs make use of this.
In many functional programs control flow is simple.
The motivation behind this thesis is that we do not want to sacrifice performance and memory usage for power and flexibility that is not even used.
The goal of this chapter is to identify what it means for control flow to be simple and make this information available to the code generation stage.

== Control Flow and Continuations

=== ...in #Fun
Control flow in #Fun is mostly implicit as a result of its call and return semantics.
Invoking a top-level definition or destructor transfers control from the caller to the callee
which is then handed back with a return value.

#example[
  This program demonstrates local control flow in #Fun programs.
  $
    & DEF f(): i64 sp { quad g(#imm(1)) + #imm(2) quad } \
    & DEF g(x: i64): i64 sp { quad x + x quad }
  $
  The function $f$ invokes $g$ with some argument.
  The function $g$ must return some value --- unless it terminates the program --- and has no influence on what happens after it returns.
  Only the body of $f$ controls how the computation continues.
] <ex:lin:fun:local>

But there is an exception: control operators, i.e. $LABEL$ and $GOTO$, can circumvent the usual control flow
by providing explicit control of where some computation continues.
In #Fun, $LABEL$ is the only way to get an explicit handle to the otherwise implicit continuation.
Labels can be freely passed around as covariables which are allowed to be duplicated or dropped.

#example[
  This #Fun program uses control operators causing non-local control flow.
  $
    & DEF f(): i64 { quad LABEL alpha sp { sp g(#imm(1), sp alpha) + #imm(2) sp } quad } \
    & DEF g(x: i64, sp alpha :^cns i64) sp { \
      & quad IF x equiv #imm(0) sp { quad GOTO alpha sp (x) quad } \
      & quad ELSE { quad x + x quad } \
      & } \
  $
  Here, $f$ gives its entire body the label $alpha$ and provides it to $g$ as an additional argument.
  By giving $g$ access to this label, the function can arbitrarily decide whether it returns a value, handing control back to the call side,
  or invoking the $alpha$. At the call side in $f$, it cannot be known if the computation will resume after the call to $g$.
] <ex:lin:fun:nonlocal>

Control flow like in @ex:lin:fun:local that is completely decided by #Fun's implicit semantics of calls and return values is referred to as _local_
because computation is known to continue exactly where it left off.
When control effects like in @ex:lin:fun:nonlocal break this property, it is called _non-local_ control flow.

=== ...in #Core
In #Core, all control flow is made explicit with consumers that are a first-class representation for computation contexts.
This makes programs much more verbose and arguably harder to read.
But it also simplifies the reasoning about control flow and continuations.

The translation function from #Fun to #Core keeps track of the current continuation, represented by such a consumer.
When translating top-level definitions, destructors, and the corresponding calls, the continuation that is implicit in #Fun is added as explicit consumer argument.
Returning a value in #Fun becomes invoking the continuation with that value in #Core.

#example[
  This is the translation of @ex:lin:fun:local to #Core.
  $
    & DEF f(kappa :^cns i64) sp { quad cut((mu alpha. g(#imm(1), sp alpha)) + #imm(2), kappa) quad } \
    & DEF g(x :^prd i64, sp kappa :^cns i64) sp { quad cut(x + x, kappa) quad } \
  $
  The definitions $f$ and $g$ do not return a value anymore.
  Instead, they use the additional continuation argument $kappa$.
  A cut with $kappa$ exactly corresponds to returning a value in @ex:lin:fun:local.
  The call to $g$ in $f$ needs to specify where the continuations should resume after $g$ which it does by capturing the current continuation using the $mu$ abstraction.
] <ex:lin:core:local>

When there is only local control flow, like in @ex:lin:core:local,
the covariable representing the continuation is invoked exactly once at runtime.
Because invoking the continuation corresponds to returning a value and a function in #Fun must return exactly once, unless control effects are involved.

#definition(title: [Linear Continuation])[
  A continuation is _linear_ if it is invoked exactly once in every possible execution.
]

The observation motivating this chapter is that in a program with only local control flow every continuation must be linear.

In a program that makes use of control operators resulting in non-local control flow,
continuations are not generally linear.

#example[
  This is the translation of @ex:lin:fun:nonlocal to #Core.
  $
    & DEF f(kappa :^cns i64) sp { \
    & quad cl mu alpha. \
    & quad quad cut((mu beta. g(#imm(1), sp alpha, sp beta)) + #imm(2), alpha) \
    & quad | kappa cr \
    & } \
    & DEF g(x :^prd i64, sp alpha :^cns i64, sp kappa :^cns i64) sp { \
    & quad IF x equiv #imm(0) sp { quad cut(#imm(0), alpha) quad } \
    & quad ELSE { quad cut(x + x, kappa) quad } \
    & } \
  $
  The example shows how non-local control flow corresponds to nonlinear continuations.
  In $f$, the first $mu$ abstraction gives a name to the current continuation --- which is $kappa$, so $alpha$ is just another name for $kappa$.
  And $alpha$ is not used linearly: it is given to $g$ as explicit argument and it is used as consumer in the cut.
  Also in $g$, neither $alpha$ nor $kappa$ is linear because depending on $x$ one of them is dropped.
]

To summarize: programs in #Fun with only local control flow correspond to #Core programs where every continuation is linear and #Fun programs that make use of control operators to achieve non-local control flow result in #Core programs where continuations may be nonlinear.
The source of nonlinearity is the ability to capture a continuation explicitly using $LABEL$ and duplicate or drop it like an ordinary variable.

=== ...in #AxCut
#AxCut makes linearity even more explicit by concentrating all sources of nonlinearity into explicit $SUBSTITUTE$ statements.
The only way to duplicate or drop a (co)variable is through the usage of $SUBSTITUTE$.

The translation from #Core to #AxCut preserves the linearity of continuations.
That means, a linear continuation in a #Core program is translated into a linear continuation in #AxCut.

One thing to keep in mind is that the usage of producers and consumers is syntactically unified.
Continuations and can be introduced by $LET$ and $CREATE$.
Both of which can also introduce producers.

#example[
  Consider the following #Fun program that makes use of data and codata types.
  #set math.lr(size: 1em)
  #let (Unit, unit) = (`Unit`, `U`)
  #let (Fun, ap) = (`Fun`, `ap`)
  $
    & DATA Unit sp { quad unit quad } \
    & CODATA Fun sp { quad ap(u : Unit): Unit quad } \
    & DEF f(): Unit sp { \
    & quad highlight(LET sp u, color: #green) = unit; \
    & quad highlight(LET sp h, color: #blue) = NEW { quad ap(u) => u quad }; \
    & quad highlight(h.ap(g().ap(u)), color: #orange) \
    & } \
    & DEF g(): Fun { sp ... sp }
  $

  In the green and blue highlighted parts, some data is bound to a variable.
  The parts of the program that concern control flow are highlighted in orange.

  The following #AxCut translation illustrates how $LET$ and $CREATE$ are used for both continuations and data.

  $
    & DATA Unit sp { quad unit quad } \
    & CODATA Fun { quad ap(x :^prd Unit, kappa :^cns Unit) quad } \
    & DEF f(kappa_f :^cns Unit) sp { \
      & quad highlight(LET sp u, color: #green) = unit; \
      & quad highlight(CREATE sp h, color: #blue) = () sp { sp ap(u, sp kappa_j) => \
        & quad quad SUBSTITUTE [kappa_h := kappa_h]; \
        & quad quad INVOKE kappa_h sp U \
        & quad }; \
      & quad SUBSTITUTE [u := u, sp kappa_f := kappa_f, sp h := h]; \
      & quad highlight(CREATE sp alpha, color: #orange) = (kappa_f, sp h) sp { sp unit => \
        & quad quad LET x = U; \
        & quad quad SUBSTITUTE [x := x, sp kappa_f := kappa_f, sp h := h]; \
        & quad quad INVOKE h ap(x, sp kappa_f) \
        & quad }; \
      & quad highlight(LET sp beta, color: #orange) = ap(u, sp alpha); \
      & quad g(beta) \
      & } \
    & DEF g(kappa_g :^cns Fun) sp { sp ... sp } \
  $
  In #AxCut, a the producer of a data type is $LET$-bound to a variable.
  A codata type, on the other hand, is translated into a closure using $CREATE$.
  And dually, a continuation for a data type, like $alpha$, is introduced by $CREATE$,
  while a continuation for a codata type, like $beta$ is a $LET$-binding.
] <ex:lin:axcut:4intros>

We must be careful to distinguish which $CREATE$, $LET$, $SWITCH$, and $INVOKE$ corresponds to a linear continuation and which does not,
so we can use this information to optimize code generation.

=== ...in Machine Code
#todo[TODO]

== Restricting #Fun
As we have seen, #Fun programs with non-local control flow using control operators lead to nonlinear continuations.
As soon as any control operator is involved, only a complex analysis of the whole program can track which continuations exactly are used linearly.
This thesis focuses only on programs that use no control operators at all.

The optimization can only be applied to a certain subset of #Fun programs,
i.e. programs that do not make use of the $LABEL$ and $GOTO$ constructs.
This restrictions leaves us with a less interesting but much more predictable language where control flow is simple and completely implicit.
Because of this implicitness we can be sure that every continuation is perfectly linear.

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
] <def:lin:fun>

The typing rules from @fig:scc:fun:typing also apply to this fragment of #Fun.
Of course, the rules #rn("Label"), #rn("Goto"), #rn("Covar"), and $#rn("Arg") _3$ are not needed anymore.

=== Control Operators and Intuitionistic Logic
The addition of the control operators $LABEL$ and $GOTO$ in #Fun corresponds to classical logic,
similarly to `call/cc` in Scheme @Timothy1990formulae.
This enables programs corresponding to classical propositions, like the law of the excluded middle or double negation elimination,
which cannot be derived without control operators.

Restricting #Fun, therefore, also means that we lose the ability to write those classical programs.
The fragment from @def:lin:fun corresponds to intuitionistic logic which will get even more obvious in #Core.

#note[Idk about this section. It is poorly phrased and not important to the thesis.]

== Restricting #Core
After restricting #Fun, the goal is now to retain the information about linear continuations that we gained.
In #Core, there is nothing like $LABEL$ and $GOTO$ from #Fun that we can simply remove from the language.
Instead, all continuations are explicit now, and we must structurally ensure that they are used linearly.

The key idea here is that, coming from #Fun, every continuation and consumer must be linear anyway,
since in #Fun there is just no way to construct something that would result in a nonlinear usage of consumers.

In theory, it would suffice to keep #Core and the translation to it as is, remembering that every continuation must be linear.
But to make the correctness of the following optimization obvious,
we identify the fragment of #Core that can result from the restricted version of #Fun.
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
In argument and parameter lists, they are exactly the added consumer arguments that correspond to the implicit continuation in #Fun.

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

#note[Structural rules. Rules for arguments.]

=== Linearity & Intuitionistic
#note[This resembles Gentzen's LJ :O]

=== Focusing & Shrinking
#todo[TODO]

== Linearity in #AxCut

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
        note[$omega(Gamma_0) = Gamma_0$],
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
        note[$omega(Gamma_0)=Gamma_0$],
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
        note[Linearity Condition: $forall v in "lin"(Gamma). exists_1 v' in sigma. v = v'$],
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

#note[The (maybe) new #Core syntax is not used here yet. Maybe also include other cases.]

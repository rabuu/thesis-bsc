#import "/lib/lib.typ": *
#import deps: fletcher

= Linear Continuations <ch:lin>
A central feature of the SCC is how it explicitly represents control flow,
leveraging the symmetric properties of data and computation contexts inherited from the sequent calculus.
Consumers as a first-class construct naturally allow for very powerful and flexible handling of control flow.

But not all programs make use of this.
In many functional programs control flow is simple.
The motivation behind this thesis is that we do not want to sacrifice performance and memory usage for power and flexibility that is not even used.
The goal of this chapter is to identify what it means for control flow to be simple and make this information available to the code generation stage.

== Control Flow and Continuations <sec:lin:flow>
We begin with an informal analysis of how control flow is represented throughout the different compiler stages.
This provides intuition for why the optimization is correct and motivates the approach presented in the remainder of this chapter.

=== ...in #Fun
Control flow in #Fun is mostly implicit due to its direct-style call-and-return semantics.
Invoking a top-level definition or destructor transfers control from the caller to the callee,
which eventually returns control to the caller along with a return value.

#example[
  This program demonstrates local control flow in #Fun programs.

  #figure(pseudo(
    $DEF f(): i64 sp { quad g(#imm(1)) + #imm(2) quad }$,
    $DEF g(x: i64): i64 sp { quad x + x quad }$,
  ))

  The function $f$ invokes $g$ with some argument.
  The function $g$ must return some value --- unless it terminates the program --- and has no influence on what happens after it returns.
  Only the body of $f$ controls how the computation continues.
] <ex:lin:fun:local>

But there is an important exception: control operators, i.e. $LABEL$ and $GOTO$, can circumvent the usual control flow
by providing explicit control of where some computation continues.
In #Fun, $LABEL$ is the only way to get an explicit handle to the otherwise implicit continuation.
Labels can be freely passed around as covariables which are allowed to be duplicated or dropped.

#example[
  This #Fun program uses control operators causing non-local control flow.

  #figure(pseudo(
    $DEF f(): i64 { quad LABEL alpha sp { sp g(#imm(1), sp alpha) + #imm(2) sp } quad }$,
    $DEF g(x: i64, sp alpha :^cns i64): i64 sp {$,
    (
      $IF x equiv #imm(0) sp { quad GOTO alpha sp (x) quad }$,
      $ELSE { quad x + x quad }$,
    ),
    $}$,
  ))

  Here, $f$ annotates its entire body with the label $alpha$ and which it provides to $g$ as an additional argument.
  By giving $g$ access to this label, the function can arbitrarily decide whether it returns a value, handing control back to the call side,
  or invokes the continuation $alpha$. At the call side in $f$, it cannot be known if the computation will resume after the call to $g$.
] <ex:lin:fun:nonlocal>

Control flow like in @ex:lin:fun:local that is completely decided by #Fun's implicit semantics of calls and return values is referred to as _local_
because computation is known to continue exactly where it left off.
When control effects like in @ex:lin:fun:nonlocal break this property, it is called _non-local_ control flow.

=== ...in #Core
In #Core, all control flow is made explicit with consumers that are a first-class representation for computation contexts.
This makes programs much more verbose and arguably harder to read.
But it also simplifies the reasoning about control flow and continuations.

The translation function from #Fun to #Core keeps track of the current continuation.
When translating top-level definitions, destructors, and the corresponding calls, the continuation that is implicit in #Fun is added as explicit consumer argument.
Returning a value in #Fun becomes invoking the continuation with that value in #Core.

#example[
  This is the translation of @ex:lin:fun:local to #Core.

  #figure(pseudo(
    $DEF f(kappa :^cns i64) sp { quad cut((mu alpha. g(#imm(1), sp alpha)) + #imm(2), kappa) quad }$,
    $DEF g(x :^prd i64, sp kappa :^cns i64) sp { quad cut(x + x, kappa) quad }$,
  ))

  The definitions $f$ and $g$ do not return a value anymore.
  Instead, they use the additional continuation argument $kappa$.
  A cut with $kappa$ exactly corresponds to returning a value in @ex:lin:fun:local.
  The call to $g$ in $f$ needs to specify where the computation should continue after $g$ which it does by capturing the current continuation using the $mu$ abstraction.
] <ex:lin:core:local>

When there is only local control flow, like in @ex:lin:core:local,
the covariable representing the continuation is invoked exactly once at runtime.
This is because invoking the continuation corresponds to returning a value and a function in #Fun must return exactly once --- unless control effects are involved.

#definition(title: [Linear Continuation])[
  A continuation is _linear_ if it is invoked exactly once in every possible branch of execution.
]

The observation motivating this chapter is that in a program with only local control flow every continuation must be linear.
Conversely, in a program that makes use of control operators resulting in non-local control flow,
continuations are not generally linear.

#example[
  This is the translation of @ex:lin:fun:nonlocal to #Core.
  It shows how non-local control flow corresponds to nonlinear continuations.

  #figure(pseudo(
    $DEF f(kappa :^cns i64) sp {$,
    (
      $cl mu alpha.$,
      (
        $cut((mu beta. g(#imm(1), sp alpha, sp beta)) + #imm(2), alpha)$,
      ),
      $| kappa cr$,
    ),
    $}$,
    $DEF g(x :^prd i64, sp alpha :^cns i64, sp kappa :^cns i64) sp {$,
    (
      $IF x equiv #imm(0) sp { quad cut(x, alpha) quad }$,
      $ELSE { quad cut(x + x, kappa) quad }$,
    ),
    $}$,
  ))

  In $f$, the first $mu$ abstraction gives a name to the current continuation --- which is $kappa$, so $alpha$ is just another name for $kappa$.
  And $alpha$ is not used linearly: it is given to $g$ as explicit argument and it is used as consumer in the cut.
  Also in $g$, neither $alpha$ nor $kappa$ is linear because depending on $x$ one of them is dropped.
]

To summarize: programs in #Fun with only local control flow correspond to #Core programs where every continuation is linear. However, #Fun programs that make use of control operators to achieve non-local control flow result in #Core programs where continuations may be nonlinear.
The source of nonlinearity is the ability to capture a continuation explicitly using $LABEL$ and duplicate or drop it like an ordinary variable.

=== ...in #AxCut
#AxCut makes linearity even more explicit by concentrating all causes of nonlinearity into explicit $SUBSTITUTE$ statements.
The only way to duplicate or drop a (co)variable is through the usage of $SUBSTITUTE$.

The translation from #Core to #AxCut preserves the linearity of continuations.
That means, a linear continuation in a #Core program is translated into a linear continuation in #AxCut.

One thing to keep in mind is that the usage of producers and consumers is syntactically unified.
Continuations can be introduced by $LET$ and $CREATE$.
Both of which can also introduce producers.

#example[
  Consider the following #Fun program that makes use of data and codata types.
  #let (Unit, unit) = (`Unit`, `U`)
  #let (Fun, ap) = (`Fun`, `ap`)

  #figure(pseudo(
    $DATA Unit sp { quad unit quad }$,
    $CODATA Fun sp { quad ap(u : Unit): Unit quad }$,
    $DEF f(): Unit sp {$,
    (
      $highlight(LET sp u, color: #green) = unit;$,
      $highlight(LET sp h, color: #blue) = NEW { quad ap(u) => u quad };$,
      $highlight(h.ap(g().ap(u)), color: #orange)$,
    ),
    $}$,
    $DEF g(): Fun { sp ... sp }$,
  ))

  In the green and blue highlighted parts, some data is bound to a variable.
  The parts of the program that concern control flow are highlighted in orange.

  The following #AxCut translation illustrates how $LET$ and $CREATE$ are used for both continuations and data.

  #figure(pseudo(
    $DATA Unit sp { quad unit quad }$,
    $CODATA Fun { quad ap(x :^prd Unit, kappa :^cns Unit) quad }$,
    $DEF f(kappa_f :^cns Unit) sp {$,
    (
      $highlight(LET sp u, color: #green) = unit;$,
      $highlight(CREATE sp h, color: #blue) = () sp { sp ap(u, sp kappa_h) =>$,
      (
        $SUBSTITUTE [kappa_h := kappa_h];$,
        $INVOKE kappa_h sp U$,
      ),
      $};$,
      $SUBSTITUTE [u := u, sp kappa_f := kappa_f, sp h := h];$,
      $highlight(CREATE sp alpha, color: #orange) = (kappa_f, sp h) sp { sp unit =>$,
      (
        $LET x = U;$,
        $SUBSTITUTE [x := x, sp kappa_f := kappa_f, sp h := h];$,
        $INVOKE h ap(x, sp kappa_f)$,
      ),
      $};$,
      $highlight(LET sp beta, color: #orange) = ap(u, sp alpha);$,
      $g(beta)$,
    ),
    $}$,
    $DEF g(kappa_g :^cns Fun) sp { sp ... sp }$,
  ))

  In #AxCut, the producer of a data type is $LET$-bound to a variable.
  A codata producer, on the other hand, is translated into a closure using $CREATE$.
  And dually, a continuation for a data type, like $alpha$, is introduced by $CREATE$
  and a continuation for a codata type, like $beta$, with $LET$.
] <ex:lin:axcut:4intros>

We must be careful to distinguish which $CREATE$, $LET$, $SWITCH$, and $INVOKE$ corresponds to a linear continuation and which does not,
so we can use this information to optimize code generation.

#sidenote[codegen sec?]

== The Scope of the Optimization
This thesis presents how to exploit the linearity of continuations in the SCC to improve the generated machine code.
As discussed, a source program that makes use of control operators inherently requires the expressive power of nonlinear continuations.
Consequently, the optimization targets only programs whose control flow is entirely local.
#sidenote[Why not mix and match?]

The following sections describe the modifications to the compiler stages and translations required to achieve these optimized results.
The lower-level stages of the compiler are extended to support special treatment of linearity --- for data and continuations in general.
The higher-level stages, namely #Fun and #Core, are instead restricted to enable these lower-level optimizations for linear continuations in particular.

#figure({
  import fletcher: diagram, edge, node, shapes

  let colored-node(color) = node.with(
    stroke: color,
    shape: shapes.rect,
    fill: color.lighten(65%),
  )

  let fun = (0, 0)
  let core = (1.5, 0)
  let axcut = (3, 0)
  let riscv = (4.5, 0)

  show ref: set text(size: settings.font-size-normal - 4pt)

  diagram(
    debug: false,
    node-stroke: 1pt,
    label-sep: 0.2em,
    colored-node(red)(fun, [Restricted \ #Fun \ @sec:lin:fun]),
    colored-node(green)(core, [Restricted \ #Core \ @sec:lin:core]),
    colored-node(blue)(axcut, [Extended \ #AxCut \ @sec:lin:axcut]),
    colored-node(orange)(riscv, [Optimized \ #RISC-V \ @ch:codegen]),
    edge(fun, core, "-|>", label: $f2c(dot)$, label-side: left),
    edge(
      core,
      axcut,
      "-|>",
      label: [
        #set align(center)
        #set par(leading: 5pt)
        #text(size: settings.font-size-normal - 2pt, "modified") \
        $c2a(dot)$
      ],
      label-side: left,
    ),
    edge(
      core,
      axcut,
      "-|>",
      label: [@sec:lin:c2a],
      label-side: right,
      stroke: none,
    ),
    edge(
      axcut,
      riscv,
      "-|>",
      label: [
        #set align(center)
        #set par(leading: 5pt)
        #text(size: settings.font-size-normal - 2pt, "modified") \
        $a2m(dot)$
      ],
      label-side: left,
    ),
    edge(
      axcut,
      riscv,
      "-|>",
      label: [@ch:codegen],
      label-side: right,
      stroke: none,
    ),
    edge(
      core,
      core,
      "-|>",
      bend: -120deg,
      label: $focus(dot), shrink(dot)$,
    ),
  )
})

The pipeline as described in @ch:scc remains largely intact.
The remainder of this chapter discusses the class of programs for which the optimization presented in @ch:codegen is applicable and why it is correct.

== Restricting #Fun <sec:lin:fun>
The property that is required for the optimization to work is that every continuation is linear.
In #Fun, most continuations are implicit, so the goal is to find the subset of #Fun programs that result in #Core and #AxCut programs with only linear continuations.
As shown in @sec:lin:flow, #Fun programs with non-local control flow, resulting from the control operators $LABEL$ and $GOTO$,
are translated to #Core programs with nonlinear continuations.
In this chapter we show that restricting the surface language to programs without the usage of $LABEL$ and $GOTO$ ensures that all continuations in the lower-level compiler stages must be linear.
This restriction leaves us with a less interesting but much more predictable language where control flow is completely implicit and local.

The syntax of the restricted version of #Fun is, in comparison to @def:scc:fun, much simpler.
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

The typing rules from @app:form:fun:typing also apply to this fragment of #Fun.
Of course, the rules concerning $LABEL$, $GOTO$ and covariables are not needed.

#note[
  Maybe a small section about how restricted #Fun corresponds to intuitionistic logic.
  See @Timothy1990formulae.
]

== Restricting #Core <sec:lin:core>
After restricting #Fun, the goal is now to retain the information about linear continuations that we gained.
To do that, one could image extending #Core to somehow annotate every continuation (or even every (co)variable) with whether it is linear or not
and then translate restricted #Fun to annotate the linearity of the continuations.
This approach would lead to an extended version of #Core with additional compile-time information about continuations.
Although this would be attractive, especially as a compilation target for more than just #Fun, it also requires a much more complex, linear type system.

Instead, in this thesis we chose to also restrict #Core to a fragment where every continuation must be linear.
In #Core, there is nothing like $LABEL$ and $GOTO$ from #Fun that we can simply remove from the language.
Instead, all continuations are explicit now, and we must structurally ensure their linearity.

The key idea here is that, coming from restricted #Fun, every continuation and consumer must be linear anyway,
since in #Fun there is just no way to construct something that would result in a nonlinear usage of consumers.
So, we identify the image of the translation from restricted #Fun.
It is a strict subset of @def:scc:core.

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

      ($delta$, "Declarations"),
      alt(
        $DEF f(Gamma, alpha :^cns tau) br(s)$,
      ),
      alt(
        $DATA sp T br(K(Gamma), ...)$,
      ),
      alt(
        $CODATA sp T br(D(Gamma, alpha :^cns tau), ...)$,
      ),
    )
  ]
]

In #Core programs that are translated from the restricted fragment of #Fun,
all covariables and consumer arguments must stem from the translation process.
In argument and parameter lists, they are exactly the added consumer arguments that correspond to the implicit continuation in #Fun.

Here, this is made explicit by restricting arguments $sigma$ and typing contexts $Gamma$ to only include producers.
This makes it very explicit where continuations can appear:
every top-level definition and every destructor has exactly one consumer argument at the end which is the continuation;
constructors cannot have any consumer field.

Restricted #Core is exactly the image of $f2c(dot)$ (see @fig:scc:f2c) for restricted #Fun.

=== Typing Rules
The type system for restricted #Core is modified to ensure that every continuation is used exactly once.
It works similar to linear type systems @Wadler1990linear, a concept originally derived from linear logic @Girard1987.
The idea is that linearity is a structural property and can be tracked by restricting the structural rules for the context.
The difference to full linear type systems is that, in restricted #Core, only continuations are linear, so the structural rules are only restricted for consumer bindings.

Concretely, the structural rules like in @def:scc:core:structural are restricted to only apply to producers.
Each continuation must be used, therefore continuations are not allowed to be dropped from the context.
And each continuation must be used exactly once, therefore continuations are not allowed to be duplicated in the context.
The former corresponds to restricting the #rn("Weakening") rule, the latter corresponds to the #rn("Contraction") rule.
In restricted #Core, there cannot be more than one continuation in the context, so #rn("Exchange") does not apply to consumer bindings.

#definition(title: [Structural Rules])[
  For statement typing, the structural rules are:
  #figure(rule-set(
    column-gutter: 2em,
    manual-grouping: true,
    (
      prooftree(rule(
        name: rn("Weakening"),
        $Gamma, alpha :^cns tau' tack s$,
        $Gamma, x :^prd tau, alpha :^cns tau' tack s$,
      )),
      prooftree(rule(
        name: rn("Contraction"),
        $Gamma, x :^prd tau, x :^prd tau, alpha :^cns tau' tack s$,
        $Gamma, x :^prd tau, alpha :^cns tau' tack s$,
      )),
    ),
    prooftree(rule(
      name: rn("Exchange"),
      $Gamma_1, v_1 :^prd tau_1, v_2 :^prd tau_2, Gamma_2, alpha :^cns tau' tack s$,
      $Gamma_1, v_2 :^prd tau_2, v_1 :^prd tau_1, Gamma_2, alpha :^cns tau' tack s$,
    )),
  ))

  Analogous, the three rules exist for consumer, producer, and argument typing.
  For producer and argument typing, the additional consumer binding is omitted.
]

The rest of the rules stays similar to the ones from @fig:scc:core:typing.
But they are adjusted to track the continuation.
In restricted #Core, there is always exactly one consumer, _the_ continuation, in the context when typing a statement.
And this consumer must be invoked in the body of the statement. In every cut statement, the continuation must appear in the consumer part because a producer can only introduce new continuations --- using the $tilde(mu)$ abstraction or in a copattern match --- but never consume it.
This is made explicit in the judgment forms.
In #box[$Theta mid Gamma tack p :^prd tau$] there can only be producers in the context,
in #box[$Theta mid Gamma, alpha :^cns tau tack c :^cns tau'$] and #box[$Theta mid Gamma, alpha :^cns tau tack s$], on the other hand, there must be a single continuation in the context.

This distinction makes it obvious where exactly the continuation is used.
Producers cannot directly invoke continuations, and if a producers contains a statement, it first must introduce a new continuation.
Statements and consumers always use their continuation exactly once.

#note[This needs more work.]

#figure(
  kind: "Figure",
  supplement: "Figure",
  caption: [Typing rules for restricted #Core.],
  block(width: 100%)[
    #def-box[Declaration Typing: $Theta tack delta$]
    #rule-set(
      prooftree(rule(
        name: rn("Def"),
        $Theta mid Gamma, alpha :^cns tau tack s$,
        $Theta tack DEF f(Gamma, alpha :^cns tau) br(s)$,
      )),
    )

    #def-box[Producer Typing: $Theta mid Gamma tack p :^prd tau$]

    #rule-set(
      manual-grouping: true,
      (
        prooftree(rule(
          name: rn("Var"),
          $x :^prd tau tack x :^prd tau$,
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
          $Gamma tack n :^prd i64$,
        )),
        prooftree(rule(
          name: rn("Plus"),
          $Gamma tack p_1 :^prd i64$,
          $Gamma tack p_2 :^prd i64$,
          $Gamma tack p_1 + p_2 :^prd i64$,
        )),
      ),
      (
        prooftree(rule(
          name: rn("Ctor"),
          $DATA T br(..., K(Gamma'), ...) in Theta$,
          $Gamma tack sigma : Gamma'$,
          $Theta mid Gamma tack K(sigma) :^prd T$,
        )),
        prooftree(rule(
          name: rn("New"),
          $CODATA T br(D_1(Gamma_1, alpha_1 :^cns tau_1), ...) in Theta$,
          $forall i: Gamma, Gamma_i, alpha_i :^cns tau_i tack s_i$,
          $Theta mid Gamma tack NEW br(D_1(Gamma_1, alpha_1 :^cns tau_1) => s_1, ...) :^prd T$,
        )),
      ),
    )

    #def-box[Consumer Typing: $Theta mid Gamma, alpha :^cns tau tack c :^cns tau'$]

    #rule-set(
      manual-grouping: true,
      (
        prooftree(rule(
          name: rn("Covar"),
          $alpha :^cns tau tack alpha :^cns tau$,
        )),
        prooftree(rule(
          name: rn("Act-L"),
          $Gamma, x :^prd tau', alpha :^cns tau tack s$,
          $Gamma, alpha :^cns tau tack tilde(mu)x. s :^cns tau'$,
        )),
      ),
      (
        prooftree(rule(
          name: rn("Dtor"),
          $CODATA T br(..., D(Gamma', alpha' :^cns tau'), ...) in Theta$,
          $Gamma tack sigma : Gamma'$,
          $Gamma, alpha :^cns tau tack c :^cns tau'$,
          $Theta mid Gamma, alpha :^cns tau tack D(sigma, c) :^cns T$,
        )),
        prooftree(rule(
          name: rn("Case"),
          $DATA T br(K_1(Gamma_1), ...) in Theta$,
          $forall i: Gamma, Gamma_i, alpha :^cns tau tack s_i$,
          $Theta mid Gamma, alpha :^cns tau tack CASE br(K_1(Gamma_1) => s_1, ...) :^cns T$,
        )),
      ),
    )

    #def-box[Statement Typing: $Theta mid Gamma, alpha :^cns tau tack s$]

    #rule-set(
      prooftree(rule(
        name: rn("Cut"),
        $Gamma tack p :^prd tau'$,
        $Gamma, alpha :^cns tau tack c :^cns tau'$,
        $Gamma, alpha :^cns tau tack cut(p, c)$,
      )),
      prooftree(rule(
        name: rn("IfZ"),
        $Gamma, tack p :^prd i64$,
        $Gamma, alpha :^cns tau tack s_1$,
        $Gamma, alpha :^cns tau tack s_2$,
        $Gamma, alpha :^cns tau tack IF p equiv 0 br(s_1) ELSE br(s_1)$,
      )),
      prooftree(rule(
        name: rn("Call"),
        $DEF f(Gamma', alpha' :^cns tau') br(...) in Theta$,
        $Gamma tack sigma : Gamma'$,
        $Gamma, alpha :^cns tau tack c :^cns tau'$,
        $Theta mid Gamma, alpha :^cns tau tack f(sigma, c)$,
      )),
      prooftree(rule(
        name: rn("Exit"),
        $Gamma tack p :^prd i64$,
        $Gamma, alpha :^cns tau tack EXIT p$,
      )),
    )
  ],
)

=== Focusing and Shrinking
The transformations on #Core, focusing (@app:form:focusing) and shrinking (@app:form:shrinking), preserve typability and therefore the linearity of continuations.

#note[Why?]

== Linearity in #AxCut <sec:lin:axcut>

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

      ($Gamma$, "Typing Contexts"),
      alt(
        $empty$,
        $Gamma, sp v :^chi_highlight(q) tau$,
      ),
    )
  ]
]

#note[Is it okay that the linearity annotations appear in parameter lists?]

=== Typing Rules

#definition(title: [Context Filtering])[
  To filter a typing context for linear and nonlinear bindings, we define the following two operations $Gamma^omega$ and $Gamma^1$ on some typing context $Gamma$:

  $
    (Gamma, v :^chi_omega tau)^omega & := Gamma^omega, v :^chi_omega tau #h(4em)
    & (Gamma, v :^chi_1 tau)^omega & := Gamma^omega \
    (Gamma, v :^chi_omega tau)^1 & := Gamma^1 #h(4em)
    & (Gamma, v :^chi_1 tau)^1 & := Gamma^1, v :^chi_1 tau \
  $
]

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

== Translation from #Core to #AxCut <sec:lin:c2a>
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

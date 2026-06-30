#import "/lib/lib.typ": *
#import deps: fletcher

= Linear Continuations <ch:lin>
A central feature of the SCC is its explicit representation of control flow.
This follows the sequent-calculus view in which data and computation contexts are treated symmetrically.
Consumers become first-class objects that naturally allow for a very expressive handling of control flow.

However, many programs do not require this full expressive power.
In typical functional programs, control flow is often simple: calls return to their call site and computation continues locally.
In such cases, we should not sacrifice performance and memory usage for power and expressiveness that is never used.

The goal of this chapter is therefore to make this notion of "simple control flow" precise and to propagate the resulting information to code generation.

== Control Flow and Continuations <sec:lin:flow>
We begin with an informal analysis of how control flow is represented throughout the different compiler stages.
This builds intuition for the optimization and motivates the formal restrictions introduced later in this chapter.

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

  The function $f$ invokes $g$ with an argument.
  Function $g$ must return some value --- unless it terminates the program --- and cannot influence what happend after the return.
  How the computation continues is determined entirely by the body of $f$.
] <ex:lin:fun:local>

There is one important exception: control operators, i.e. $LABEL$ and $GOTO$, can circumvent the usual call-return local control flow
by providing explicit control of where a computation continues.
In #Fun, $LABEL$ is the only way to get an explicit handle to the otherwise implicit current continuation.
This continuation is bound to a covariable and can be passed around, duplicated, and dropped, so control flow can become non-local.

#example[
  This #Fun program uses control operators and therefore exhibits non-local control flow.

  #figure(pseudo(
    $DEF f(): i64 { quad LABEL alpha sp { sp g(#imm(1), sp alpha) + #imm(2) sp } quad }$,
    $DEF g(x: i64, sp alpha :^cns i64): i64 sp {$,
    (
      $IF x equiv #imm(0) sp { quad GOTO alpha sp (x) quad }$,
      $ELSE { quad x + x quad }$,
    ),
    $}$,
  ))

  Function $f$ labels its body with the covariable $alpha$ and passes this label to $g$.
  Therefore, $g$ can either return normally or jump to $alpha$.
  At the call site in $f$, it is no longer guaranteed that execution resumes after the call to $g$.
] <ex:lin:fun:nonlocal>

We call control flow _local_ when the computation flow is uniquely determined by direct-style call-return semantics, as in @ex:lin:fun:local.
When control operators break this property, as in @ex:lin:fun:nonlocal, we call it _non-local_ control flow.

=== ...in #Core
In #Core, control flow is no longer implicit: it is represented explicitly through consumers.
This makes terms more verbose, but also simplifies reasoning about control flow and continuations.

The translation from #Fun to #Core tracks the current continuation.
Whenever #Fun has an implicit return continuation --- that is in top-level definitions and destructors ---,
#Core introduces an explicit consumer argument.
Returning a value in #Fun becomes invoking this consumer in #Core.

#example[
  This is the translation of @ex:lin:fun:local to #Core.

  #figure(pseudo(
    $DEF f(kappa :^cns i64) sp { quad cut((mu alpha. g(#imm(1), sp alpha)) + #imm(2), kappa) quad }$,
    $DEF g(x :^prd i64, sp kappa :^cns i64) sp { quad cut(x + x, kappa) quad }$,
  ))

  The definitions $f$ and $g$ no longer return values directly.
  Instead, both receive an additional explicit continuation argument $kappa$.
  A cut with $kappa$ corresponds exactly to returning a value in @ex:lin:fun:local.
  In $f$, the call to $g$ explicitly specifies where computation should continue by capturing the current continuation via the $mu$ operator.
] <ex:lin:core:local>

In a program with purely local control flow, as in @ex:lin:core:local,
this continuation is invoked exactly once at runtime.
Intuitively, this is because invoking the continuation corresponds to returning a value and a function in #Fun must return exactly once, if no control effects are involved.

#definition(title: [Linear Continuation])[
  A continuation is _linear_ if it is invoked exactly once in every possible branch of execution.
]

This is the key observation of this chapter:
if a #Fun program has only local control flow, then the corresponding continuations in #Core are linear.
Conversely, control operators can introduce nonlinear continuation usage.

#example[
  This is the translation of @ex:lin:fun:nonlocal to #Core.
  It illustrates how non-local control flow corresponds to nonlinear continuations.

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

  In $f$, the first $mu$ abstraction names the current continuation.
  Here, that continuation is $kappa$, so $alpha$ is another name for $kappa$.
  This continuation is not linear: it is passed to $g$ and used in a cut.
  In $g$, neither $alpha$ nor $kappa$ is linear, since one of them is dropped depending on $x$.
]

To summarize: #Fun programs with local control flow map to #Core programs with only linear continuations.
#Fun programs that use control operators for non-local control flow result in #Core programs where continuations may be nonlinear.
The source of nonlinearity is the ability to capture a continuation explicitly using $LABEL$ and duplicate or drop it like an ordinary variable.

=== ...in #AxCut
In #AxCut, linearity in general becomes even more transparent because duplication and dropping of (co)variables are concentrated in explicit $SUBSTITUTE$ statements.
These are the only potential source of nonlinearity.

The translation from #Core to #AxCut preserves the linearity of continuations:
a linear continuation in #Core is translated to a linear continuation in #AxCut.

#AxCut unifies the handling of producers and consumers symmetrically and operationally.
Both producer variables and continuations are introduced via $LET$ or $CREATE$, depending on the combination of its chirality and polarity.

#example[
  Consider the following #Fun program that uses data and codata.
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

  The green and blue fragments, bind data to variables.
  The orange fragment concerns control flow and continuation passing.

  The corresponding #AxCut translation shows how $LET$ and $CREATE$ are used for both continuations and data.

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

  In #AxCut, a producer variable for data (e.g. $u$) is introduced by $LET$.
  A producer variable for codata (e.g. $h$) is introduced by $CREATE$.
  Dually, a continuation for data (e.g. $alpha$) is introduced by $CREATE$,
  while a continuation for codata (e.g. $beta$) is introduced by $LET$.
] <ex:lin:axcut:4intros>

For code generation, this means we must distinguish linear from nonlinear uses of $CREATE$, $LET$, $SWITCH$, and $INVOKE$.
The rest of this chapter formalizes exactly this distinction.

== The Scope of the Optimization <sec:lin:scope>
This thesis presents how to exploit the linearity of continuations in the SCC to improve the generated machine code.
As discussed above, programs that rely on control operators inherently require the expressive power of nonlinear continuations.
Consequently, the optimization targets only programs with entirely local control flow.

This is a deliberate design choice.
In principle, one could attempt a mixed strategy with both linear and nonlinear continuations in one program.
However, this would require significantly more bookkeeping and analysis infrastructure across all compiler stages.
For the purposes of this thesis, we instead prioritize a clear and robust pipeline for the fully local case.

Moreover, the low-level optimization is conceptually not limited to continuations.
The relevant memory-management mechanisms are identical for producers and consumers,
which, in theory, makes the approach applicable to linear data in general.
In this thesis, however, we apply it only to linear continuations, because they provide a simple but impactful entry point.
It is sufficient to restrict control operators to statically prove that continuations are linear.

The following illustration shows how we modify the SCC pipeline in the rest of this thesis.
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

The lower-level stages (#AxCut and code generation) are _extended_ with linearity-aware mechanisms for both data and continuations in general.
The higher-level stages (#Fun and #Core) are instead _restricted_ so that continuations are guaranteed to be linear.

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
To do that, one could imagine extending #Core to somehow annotate every continuation (or even every (co)variable) with whether it is linear or not
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
        $Gamma tack p :^prd i64$,
        $Gamma, alpha :^cns tau tack s_1$,
        $Gamma, alpha :^cns tau tack s_2$,
        $Gamma, alpha :^cns tau tack IF p equiv 0 br(s_1) ELSE br(s_2)$,
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
The restricted fragments of #Fun and #Core are known to only cause local control flow and linear continuations, respectively.
The next step is to make this information available in #AxCut.
Of course, we could restrict the language to the exact image of the translation from restricted #Core where it would be obvious that all continuations are still linear.
But in this thesis, we choose to extend #AxCut with explicit linearity annotations.
This makes the language suitable as a target for even more optimizations regarding linearity, not only the linearity of continuations.

#AxCut unifies the handling of variables for producers and covariables for consumers. All (co)variables are treated the same.
There are two ways to introduce and consume a (co)variable: either is introduced with $LET$ and consumed by $SWITCH$, or it is introduced by $CREATE$ and consumed by $INVOKE$.
In both cases, the (co)variable references some data. For a $LET$ (co)variable, that is its tag and the constructor or destructor fields; for a $CREATE$ (co)variable, that is the closure with its code and environment.
We extend #AxCut now by annotating for each variable whether it must be used linearly or not.

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
      $LET_q sp v = X(sigma); sp s$,
      $CREATE_q sp v = Gamma br(X(Gamma) => s, ...); sp s$,
      $SWITCH_q sp v br(X(Gamma) => s, ...)$,
      $INVOKE v sp X(sigma)$,

      ($Gamma$, "Typing Contexts"),
      alt(
        $empty$,
        $Gamma, sp v :^chi_q tau$,
      ),
    )
  ]
]

At each binding side, i.e. $LET$ and $CREATE$, we add an annotation where $omega$ means that the use of the (co)variable is unrestricted and $1$ means it must be used linearly.
We also add this information in typing contexts so that the quantity of a binding is known everywhere.

An annotation is also added for $SWITCH$, the consuming part of a $LET$ (co)variable.
This annotation is not strictly necessary and could be inferred from the context, but it eases the presentation of the code generation step.
Since the code generation for $INVOKE$ works the same regardless of the quantity of the (co)variable, there is no need for another annotation.

=== Type System
The original typing rules for #AxCut (@fig:scc:axcut:typing) must be modified to ensure that, in a well-typed #AxCut program, every linear (co)variable is actually used exactly once.
The updated rules are shown in @fig:lin:axcut:typing.

To formulate the typing rules for the extended variant of #AxCut we need some notation to distinguish linear from nonlinear bindings in the typing context.

#definition(title: [Context Filtering])[
  To filter a typing context for linear and nonlinear bindings, we define the following two operations $Gamma^omega$ and $Gamma^1$ on some typing context $Gamma$:

  $
    (Gamma, v :^chi_omega tau)^omega & := Gamma^omega, v :^chi_omega tau #h(4em)
    & (Gamma, v :^chi_1 tau)^omega & := Gamma^omega \
    (Gamma, v :^chi_omega tau)^1 & := Gamma^1 #h(4em)
    & (Gamma, v :^chi_1 tau)^1 & := Gamma^1, v :^chi_1 tau \
  $

  $Gamma^omega$ and $Gamma^1$ contain exactly the unrestricted and linear bindings from $Gamma$, respectively.
]

The $SUBSTITUTE$ statement is the only place where a (co)variable can be duplicated or dropped.
So we add a condition in the #rn("Substitute") rule that every linear (co)variable in the current context must be mentioned in the $SUBSTITUTE$ statement, exactly once.

Furthermore, linear (co)variables must not be consumed by nonlinear (co)variables.
That means, the fields of a nonlinear $LET$ (co)variable must consist of other nonlinear (co)variables.
And similarly, a linear (co)variable is not allowed as part of the closure environment of a nonlinear $CREATE$ (co)variable.
Otherwise, the inner linear (co)variable could be used in a nonlinear way by duplicating or dropping the containing nonlinear (co)variable.

#figure(
  kind: "Figure",
  supplement: "Figure",
  caption: [Typing rules for extended #AxCut.],
  block(width: 100%)[
    #def-box[Statement Typing: $Theta mid Gamma tack s$]
    #rule-set(
      manual-grouping: true,
      (
        prooftree(rule(
          name: $#rn("Let") _1"-"pi$,
          $pi T br(..., X(Gamma_0), ...) in Theta$,
          $Gamma, v :^(chi_1(pi))_1 T tack s$,
          $Theta mid Gamma, Gamma_0 tack LET_1 sp v = X(Gamma_0); sp s$,
        )),
        prooftree(rule(
          name: $#rn("Let") _omega"-"pi$,
          $pi T br(..., X(Gamma_0), ...) in Theta$,
          $Gamma, v :^(chi_1(pi))_omega T tack s$,
          $Gamma_0 = Gamma_0^omega$,
          $Theta mid Gamma, Gamma_0 tack LET_omega sp v = X(Gamma_0); sp s$,
        )),
        prooftree(rule(
          name: $#rn("Create") _1"-"pi$,
          $pi T br(X_1(Gamma_1), ...) in Theta$,
          $Gamma, v :^(chi_2(pi))_1 T tack s$,
          $forall i: Gamma_i, Gamma_0 tack s_i$,
          $Theta mid Gamma, Gamma_0 tack CREATE_1 sp v = Gamma_0 br(X_1(Gamma_1) => s_1, ...); sp s$,
        )),
        prooftree(rule(
          name: $#rn("Create") _omega"-"pi$,
          $pi T br(X_1(Gamma_1), ...) in Theta$,
          $Gamma, v :^(chi_2(pi))_omega T tack s$,
          $forall i: Gamma_i, Gamma_0 tack s_i$,
          $Gamma_0 = Gamma_0^omega$,
          $Theta mid Gamma, Gamma_0 tack CREATE_omega sp v = Gamma_0 br(X_1(Gamma_1) => s_1, ...); sp s$,
        )),
        prooftree(rule(
          name: $#rn("Switch-")pi$,
          $pi T br(X_1(Gamma_1), ...) in Theta$,
          $forall i: Gamma, Gamma_i tack s_i$,
          $Theta mid Gamma, v :^(chi_1(pi))_q T tack SWITCH_q sp v br(X_1(Gamma_1) => s_1, ...)$,
        )),
        prooftree(rule(
          name: $#rn("Invoke-")pi$,
          $pi T br(..., X(Gamma), ...) in Theta$,
          $Theta mid Gamma, v :^(chi_2(pi))_q T tack INVOKE v sp X(Gamma)$,
        )),
      ),
      (
        prooftree(rule(
          name: rn("Substitute"),
          $Gamma tack sigma : Gamma'$,
          $Gamma' tack s$,
          $forall v in Gamma^1. sp exists_1 v' in sigma. sp v = v'$,
          $Gamma tack SUBSTITUTE[Gamma' := sigma]; sp s$,
        )),
      ),
    )

    #def-box[Argument Typing: $Theta mid Gamma tack sigma : Gamma'$]
    #rule-set(
      prooftree(rule(
        name: $rn("Arg"_empty)$,
        $Gamma tack empty : empty$,
      )),
      prooftree(rule(
        name: $rn("Arg")$,
        $Gamma tack sigma : Gamma'$,
        $v :^chi_q tau in Gamma$,
        $Gamma tack (sigma, v) : (Gamma', sp v :^chi_q tau)$,
      )),
    )
  ],
) <fig:lin:axcut:typing>

== Translation from #Core to #AxCut <sec:lin:c2a>
With the support for linear (co)variables in #AxCut, we can now retain the information we have about continuations in the restricted #Core fragment.
Since every continuation in restricted #Core is linear, we can annotate this when translating to #AxCut.

#figure(
  kind: "Figure",
  supplement: "Figure",
  caption: [Translation from restricted #Core into extended #AxCut.],
)[
  #set math.lr(size: 1em)
  $
    c2a(cut(K(Gamma_0), tilde(mu)x. s), ctx: Gamma) & := && SUBSTITUTE[Gamma' := Gamma', Gamma_0^f := Gamma_0]; \
    &&& LET_omega sp x = K(Gamma_0^f); sp c2a(s, ctx: Gamma'\, x) \
    "where" &&& Gamma' = "freeVars"(s) subset Gamma \
    c2a(cut(mu alpha. s, D(Gamma_0, alpha_0 : tau)), ctx: Gamma) & := && SUBSTITUTE[Gamma' := Gamma', Gamma_0^f := Gamma_0, alpha_0^f := alpha_0]; \
    &&& LET_1 sp alpha = D(Gamma_0^f, alpha :^cns_1 tau); sp c2a(s, ctx: Gamma'\, alpha) \
    "where" &&& Gamma' = "freeVars"(s) subset Gamma \
    c2a(cut(mu alpha. s, CASE br(K_1(Gamma_1) => s_1, ...)), ctx: Gamma) & := && SUBSTITUTE[Gamma'^f := Gamma', Gamma_0 := Gamma_0]; \
    &&& CREATE_1 sp alpha = Gamma_0 br(K_1(Gamma_1) => c2a(s_1, ctx: Gamma_1\, Gamma_0), ...); \
    &&& c2a(s[Gamma' mapsto Gamma'^f], ctx: Gamma'^f\, alpha) \
    "where" &&& Gamma_0 = union.big_i "freeVars"(s_i) subset Gamma quad Gamma' = "freeVars"(s) subset Gamma \
    c2a(cut(NEW br(D_1(Gamma_1, alpha_1 :^cns tau_1) => s_1, ...), tilde(mu)x. s), ctx: Gamma) & := && SUBSTITUTE[Gamma'^f := Gamma', Gamma_0 := Gamma_0]; \
    &&& CREATE_omega sp x = Gamma_0 br(D_1(Gamma_1, alpha_1 :^cns_1 tau_1) => c2a(s_1, ctx: Gamma_1\, alpha_1\, Gamma_0), ...); \
    &&& c2a(s[Gamma' mapsto Gamma'^f], ctx: Gamma'^f\, x) \
    "where" &&& Gamma_0 = union.big_i "freeVars"(s_i) subset Gamma quad Gamma' = "freeVars"(s) subset Gamma \
    c2a(cut(x, CASE br(K_1(Gamma_1) => s_1, ...)), ctx: Gamma) & := && SUBSTITUTE[Gamma' := Gamma', x^f := x]; \
    &&& SWITCH_omega sp x br(K_1(Gamma_1) => c2a(s_1, ctx: Gamma'\,Gamma_1), ...) \
    "where" &&& Gamma' = union.big_i "freeVars"(s_i) subset Gamma \
    c2a(cut(NEW br(D_1(Gamma_1, alpha_1 :^cns tau_1) => s_1, ...), alpha), ctx: Gamma) & := && SUBSTITUTE[Gamma' := Gamma', alpha^f := alpha]; \
    &&& SWITCH_1 sp alpha br(D_1(Gamma_1, alpha_1 :^cns_1 tau_1) => c2a(s_1, ctx: Gamma'\,Gamma_1\,alpha_1), ...) \
    "where" &&& Gamma' = union.big_i "freeVars"(s_i) subset Gamma \
  $

  #note[too wide :(]
]

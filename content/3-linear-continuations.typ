#import "/lib/lib.typ": *
#import deps: fletcher

= Linear Continuations <ch:lin>
A central feature of the SCC is its explicit representation of control flow,
based on the structure of the sequent calculus, in which consumers are treated dually to producers.
Consumers become first-class objects, which allows the SCC to naturally and uniformly express even complex control flow.

This expressiveness, however, is not free: first-class consumers require a runtime representation and memory management strategy general enough to support this full range of control flow.
Yet many programs do not need this.
In typical functional programs, control flow is often simple: calls return to their call site and computation continues locally.
In such cases, we should not sacrifice performance and memory usage for expressiveness that is never used.

If the compiler can statically identify programs that only require simple control flow, we can generate more efficient code for them.
The goal of this chapter is therefore to make this notion of "simple control flow" precise and to propagate the resulting information to code generation.

== Control Flow and Continuations <sec:lin:flow>
We begin with an informal analysis of how control flow is represented throughout the different compiler stages.
This builds intuition for the optimization and motivates the formal restrictions introduced later in this chapter.

=== Local Control Flow and Linear Continuations
Control flow in #Fun is mostly implicit due to its direct-style call-and-return semantics.
Invoking a top-level definition or destructor transfers control from the caller to the callee,
which eventually returns control to the caller along with a return value.
When control flow is determined only by this kind of call-and-return semantics,
it is referred to as _local_.

#example[
  This program demonstrates local control flow in #Fun programs.

  #figure(pseudo(
    $DEF f(): i64 sp { quad g(#imm(1)) + #imm(2) quad }$,
    $DEF g(x: i64): i64 sp { quad x + x quad }$,
  ))

  The function $f$ invokes $g$.
  Function $g$ must return a value.
  After that, the computation is guaranteed to continue where it left off.
] <ex:lin:fun:local>

In #Core, this is made explicit with consumers.
The translation from #Fun to #Core tracks the current continuation,
and for every implicit return continuation in #Fun, it introduces an explicit consumer argument.
Returning a value in #Fun becomes invoking this consumer in #Core.

#example[
  This is the translation of @ex:lin:fun:local to #Core.

  #figure(pseudo(
    $DEF f(kappa :^cns i64) sp { quad cut((mu alpha. g(#imm(1), sp alpha)) + #imm(2), kappa) quad }$,
    $DEF g(x :^prd i64, sp kappa :^cns i64) sp { quad cut(x + x, kappa) quad }$,
  ))

  The functions $f$ and $g$ no longer return values directly.
  Instead, both receive an additional explicit continuation argument $kappa$.
  A cut with $kappa$ corresponds exactly to returning a value in @ex:lin:fun:local.
  In $f$, the call to $g$ explicitly specifies where computation continues by capturing the current continuation via the $mu$ operator.
] <ex:lin:core:local>

In a program with purely local control flow, as in @ex:lin:core:local,
each continuation is invoked exactly once at runtime.
Intuitively, this is because invoking the continuation corresponds to returning a value and a function in #Fun must return exactly once, if no control effects are involved.

#definition(title: [Linear Continuation])[
  A continuation is _linear_ if it is invoked exactly once in every possible branch of execution.
]

This is the key observation of this chapter:
if a #Fun program has only local control flow, then the corresponding continuations in #Core and consequently #AxCut are linear.

=== Non-Local Control Flow and Nonlinear Continuations
In #Fun, the control operators $LABEL$ and $GOTO$ can circumvent the usual local control flow
by providing explicit control of where a computation continues.
$LABEL$ is the only way to get a handle to the otherwise implicit current continuation.
This continuation is bound to a covariable and can be passed around and even duplicated or dropped.
Then, $GOTO$ can bypass the usual call-and-return restrictions by transferring control to an arbitrary continuation.
This kind of control flow is called _non-local_.

#example[
  This #Fun program uses control operators and therefore exhibits non-local control flow.

  #figure(pseudo(
    $DEF f(): i64 { quad LABEL alpha sp { quad g(#imm(1), sp alpha) + #imm(2) sp } quad }$,
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

Again, #Core makes this explicit with consumers representing continuations.
Non-local control flow leads to nonlinear continuations.

#example[
  This is the translation of @ex:lin:fun:nonlocal to #Core.

  #figure(pseudo(
    $DEF f(kappa :^cns i64) sp {$,
    (
      $cl mu highlight(alpha).$,
      (
        $cut((mu beta. g(#imm(1), sp highlight(alpha), sp beta)) + #imm(2), highlight(alpha))$,
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

  In $f$, the covariable $alpha$ is a name for the function continuation, corresponding to the explicit continuation introduced by $LABEL$ in #Fun.
  The covariable $beta$ abstracts the current continuation where $g$ is called; it is introduced by the translation.
  The continuation $alpha$ is not linear: it is passed to $g$ and used in a cut.

  In $g$, one of the two available continuations is invoked depending on $x$;
  since the other continuation is dropped, neither $alpha$ nor $kappa$ is linear.
] <ex:lin:core:nonlocal>

To summarize: #Fun programs with local control flow map to #Core programs with only linear continuations.
#Fun programs that use control operators for non-local control flow result in #Core programs where continuations may be nonlinear.
The source of nonlinearity is the ability to capture a continuation explicitly using $LABEL$ and duplicate or drop it like an ordinary variable.

== The Scope of the Optimization <sec:lin:scope>
This thesis shows how to exploit the linearity of continuations in the SCC to improve the generated machine code.
As discussed above, programs that rely on control operators inherently require the expressive power of nonlinear continuations.
Consequently, the optimization can only target the local control flow in the program.

In this thesis, we restrict ourselves to programs without _any_ non-local control flow.
Distinguishing which parts of a program are affected by non-local control flow from those that are not
would require significantly more bookkeeping and analysis infrastructure, which is beyond the scope of this thesis.

Moreover, the low-level optimization is conceptually not limited to continuations.
The relevant memory-management mechanisms are identical for producers and consumers,
which makes the approach applicable to linear data in general.
In this thesis, however, we apply it only to linear continuations because they provide a simple but impactful entry point:
it is sufficient to restrict control operators to statically prove that continuations are linear.

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
The optimization requires that every continuation is linear.
Since continuations in #Fun are mostly implicit, we first identify the fragment of #Fun whose translations have only linear continuations.

From @sec:lin:flow we know that non-local control flow in #Fun stems from $LABEL$ and $GOTO$, translating to nonlinear continuations in #Core.
Hence, we restrict #Fun by removing these control operators.
This leaves a less expressive language, but one with predictable, purely local control flow.

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

Syntactically, this restricted #Fun fragment is much simpler than @def:scc:fun:
without $LABEL$ and $GOTO$, explicit covariables (and thus consumers in general) are no longer needed at the surface level.

The typing rules from @app:form:fun:typing carry over to this fragment.
Only the rules involving $LABEL$, $GOTO$ and covariables are removed.

== Restricting #Core <sec:lin:core>
After restricting #Fun, we must retain the gained information about local control flow in the next stage: #Core.

One possible approach would be to extend #Core with explicit linearity annotations on continuations, or even all (co)variables.
That approach is more general, which could be appealing, but it would require a considerably more complex linear type system.

In this thesis, we choose instead to restrict #Core to a fragment where continuation linearity is guaranteed by construction.
Unlike in #Fun, this cannot be done by simply removing some control operators.
In #Core, continuations are explicit everywhere, so linearity must be enforced structurally.

The guiding idea is simple:
because restricted #Fun cannot express non-local control effects, every consumer introduced by its translation must already be linear.
So we restrict #Core exactly to the image of the translation (@fig:scc:f2c) from restricted #Fun.
This image is a strict subset of @def:scc:core.

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
all consumer arguments arise from the translation itself.
In particular, consumer arguments in parameter and argument lists are exactly those introduced to represent the implicit #Fun continuation.

This is reflected by restricting $sigma$ and $Gamma$ to producers only.
As a result, continuation positions become explicit:
each top-level definition and destructor has exactly one consumer argument at the end --- the continuation ---
while constructors have no consumer fields.

=== Type System
We now adapt typing for restricted #Core so that continuations are used exactly once.

The approach is inspired by linear type systems @Wadler1990linear, rooted in linear logic @Girard1987.
Linearity is enforced as a structural property by restricting how the typing context can be used.
Unlike fully linear systems, only consumer bindings are linear here; producer bindings remain unrestricted.

This is achieved by keeping the structural properties of the producer context $Gamma$:
the order and multiplicity of bound variables are irrelevant, and #rn("Var") only checks for the presence of a variable.
In contrast, continuations must be used exactly once:
they cannot be dropped and must be threaded through consumers and statements until they are type-checked by #rn("Covar").

The typing rules are presented in @fig:lin:core:typing.
They are based on @fig:scc:core:typing, but with judgments that explicitly track the unique continuation.
Producers are typed in a producer-only context, while consumers and statements are typed with exactly one additional continuation binding in scope.
Formally:
- $Theta mid Gamma tack p :^prd tau$ types a producer,
- $Theta mid Gamma, alpha :^cns tau tack c :^cns tau'$ types a consumer,
- and $Theta mid Gamma, alpha :^cns tau tack s$ types a statement.
Here, the comma separating the producer context from the continuation is part of the judgment syntax.

This formulation makes continuation usage explicit.
Producers cannot directly invoke continuations.
If a producer contains a statement, it must first introduce a continuation (via $mu$ or copattern matching),
and consumers and statements must use their continuation exactly once.

Intuitively, there is only a single continuation that is tracked through every execution branch until it eventually appears in a function or destructor call, or on the right side of a cut.

#figure(
  kind: "Figure",
  supplement: "Figure",
  caption: [Typing rules for restricted #Core.],
  block(width: 100%)[
    #def-box[Well-Formed Declarations: $Theta tack delta$]
    #rule-set(
      prooftree(rule(
        name: rn("Def"),
        $Theta mid Gamma, alpha :^cns tau tack s$,
        $Theta tack DEF f(Gamma, alpha :^cns tau) br(s)$,
      )),
      $...$,
    )

    #def-box[Producer Typing: $Theta mid Gamma tack p :^prd tau$]

    #rule-set(
      manual-grouping: true,
      (
        prooftree(rule(
          name: rn("Var"),
          $x :^prd tau in Gamma$,
          $Gamma tack x :^prd tau$,
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
          $Gamma, alpha :^cns tau tack alpha :^cns tau$,
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
    )
  ],
) <fig:lin:core:typing>

=== Focusing and Shrinking
The #Core transformations focusing (@app:form:focusing) and shrinking (@app:form:shrinking) preserve typability.
Since continuation linearity is enforced by typing in restricted #Core, both transformations also preserve continuation linearity.

Intuitively, neither transformation introduces new control effects or continuations.
They only reorganize already well-typed terms while preserving the single-continuation property of the typing rules.

== Extending #AxCut with Linearity Annotations <sec:lin:axcut>
At this point, restricted #Fun guarantees local control flow, and restricted #Core guarantees linear continuations.
The next step is to carry this information into #AxCut.

A possible approach is again to restrict #AxCut to the exact image of the translation from restricted #Core.
In this thesis, however, we choose a more general design:
we extend #AxCut with explicit linearity annotations for both producers and consumers.
This makes the intermediate representation suitable for extending the optimization to producers.

#AxCut unifies the treatment of producers and consumers.
A (co)variable is either introduced by $LET$ and consumed by $SWITCH$, or introduced by $CREATE$ and consumed by $INVOKE$.
In both cases, it contains a reference to runtime data:
for $LET$, tagged fields (of constructors and destructors);
for $CREATE$, a closure object with environment and methods.
If it is statically known that this data is used linearly, the memory management can be specialized.

Therefore, we now annotate each binding with whether it is linear or unrestricted.

#definition(title: [Extended #AxCut])[
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

At binding sites ($LET$, $CREATE$), quantity $omega$ means unrestricted usage and $1$ means linear usage.
The same quantity is tracked in typing contexts.

We also annotate $SWITCH$.
This is not strictly necessary, as it could be inferred from the context, but it makes subsequent code-generation translations more direct.
No additional annotation is needed for $INVOKE$, since code generation for it is independent of quantity.

#example[
  Consider the following #Fun program.

  #let (Unit, unit) = (`Unit`, `U`)
  #let Fn = `Fun`

  #figure(pseudo(
    $DATA Unit sp { quad unit quad }$,
    $CODATA Fn sp { quad apply(u : Unit): Unit quad }$,
    $DEF f(): Unit sp {$,
    (
      $highlight(LET sp x, color: #green) = unit;$,
      $highlight(LET sp h, color: #blue) = NEW { quad apply(u) => U quad };$,
      $highlight(h.apply(g().apply(x)), color: #orange)$,
    ),
    $}$,
    $DEF g(): Fn { sp ... sp }$,
  ))

  The first two lines of $f$ bind producers to variables.
  The third line concerns control flow and continuation passing.

  Since the #Fun program does not use control operators, the continuations are known to be linear.
  However, the compiler has no information about the linearity of producers.
  Therefore, the translation to #AxCut annotates continuations with $1$ and producers with $omega$.
  The corresponding modifications for the translation function are presented in @sec:lin:c2a.

  #figure(pseudo(
    $DATA Unit sp { quad unit quad }$,
    $CODATA Fn { quad apply(x :^prd_omega Unit, kappa :^cns_1 Unit) quad }$,
    $DEF f(kappa_f :^cns_1 Unit) sp {$,
    (
      $highlight(LET_omega sp x, color: #green) = unit;$,
      $highlight(CREATE_omega sp h, color: #blue) = () sp { sp apply(u, kappa_h) =>$,
      (
        $SUBSTITUTE [kappa_h := kappa_h];$,
        $INVOKE kappa_h sp U$,
      ),
      $};$,
      $SUBSTITUTE [x := x, sp kappa_f := kappa_f, sp h := h];$,
      $highlight(CREATE_1 sp alpha, color: #orange) = (kappa_f, sp h) sp { sp unit =>$,
      (
        $LET_omega sp u = U;$,
        $SUBSTITUTE [u := u, sp kappa_f := kappa_f, sp h := h];$,
        $INVOKE h apply(u, kappa_f)$,
      ),
      $};$,
      $highlight(LET_1 sp beta, color: #orange) = apply(x, alpha);$,
      $g(beta)$,
    ),
    $}$,
    $DEF g(kappa_g :^cns_1 Fn) sp { sp ... sp }$,
  ))
] <ex:lin:axcut:4intros>

=== Type System
The typing rules from @fig:scc:axcut:typing are adapted so that every linear binding is used exactly once in a well-typed program.
The updated rules are shown in @fig:lin:axcut:typing.

To formulate these rules, we first introduce a notation to separate linear and unrestricted parts of a typing context.

#definition(title: [Context Filtering])[
  To filter a typing context $Gamma$ into unrestricted and linear bindings, define $Gamma^omega$ and $Gamma^1$ by:

  $
    (Gamma, v :^chi_omega tau)^omega & := Gamma^omega, v :^chi_omega tau #h(4em)
    & (Gamma, v :^chi_1 tau)^omega & := Gamma^omega \
    (Gamma, v :^chi_omega tau)^1 & := Gamma^1 #h(4em)
    & (Gamma, v :^chi_1 tau)^1 & := Gamma^1, v :^chi_1 tau \
  $

  Thus, $Gamma^omega$ contains exactly the unrestricted bindings of $Gamma$, and $Gamma^1$ contains exactly the linear bindings.
]

The key enforcement point for linearity is $SUBSTITUTE$, since that is where duplication and dropping can occur.
Therefore, rule #rn("Substitute") requires each linear variable in the current context to appear exactly once in the substitution list.

Additionally, linear bindings must not be hidden inside unrestricted containers.
Concretely: fields of nonlinear $LET$ bindings must be unrestricted, and environment bindings of nonlinear $CREATE$ closures must be unrestricted.
Otherwise, a linear inner (co)variable could be duplicated or dropped indirectly through the unrestricted outer container.

The additional premises for linear continuations are highlighted.

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
          highlight($Gamma_0 = Gamma_0^omega$),
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
          highlight($Gamma_0 = Gamma_0^omega$),
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
          highlight($forall v in Gamma^1. sp exists_1 v' in sigma. sp v = v'$),
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

== Extending the Translation from #Core to #AxCut <sec:lin:c2a>
With linearity-aware #AxCut in place, the translation can preserve and expose the continuation information from restricted #Core.
Since all continuations in restricted #Core are linear, the translation marks them with quantity $1$.
All producers, however, are marked with $omega$ because we have no static information about them.

#figure(
  kind: "Figure",
  supplement: "Figure",
  caption: [Translation from restricted #Core into extended #AxCut.],
  block(width: 100%)[
    #set math.lr(size: 1em)

    #def-box[$c2a(dot, ctx: dot.o) : "Statement"_("Shrunk" Core) times "Context"_AxCut -> "Statement"_AxCut$]
    $
      & c2a(cut(K(Gamma_0), tilde(mu)x. s), ctx: Gamma) := \
      & #h(4em) SUBSTITUTE[Gamma' := Gamma', Gamma_0^f := Gamma_0]; \
      & #h(4em) LET_omega sp x = K(Gamma_0^f); sp c2a(s, ctx: Gamma'\, sp x) \
      & #h(4em) "where" quad Gamma' = "freeVars"(s) subset Gamma \
      & c2a(cut(mu alpha. s, D(Gamma_0, alpha_0 : tau)), ctx: Gamma) := \
      & #h(4em) SUBSTITUTE[Gamma' := Gamma', Gamma_0^f := Gamma_0, alpha_0^f := alpha_0]; \
      & #h(4em) LET_1 sp alpha = D(Gamma_0^f, alpha :^cns_1 tau); sp c2a(s, ctx: Gamma'\, alpha) \
      & #h(4em) "where" quad Gamma' = "freeVars"(s) subset Gamma \
      & c2a(cut(mu alpha. s, CASE br(K_1(Gamma_1) => s_1, ...)), ctx: Gamma) := \
      & #h(4em) SUBSTITUTE[Gamma'^f := Gamma', Gamma_0 := Gamma_0]; \
      & #h(4em) CREATE_1 sp alpha = Gamma_0 br(K_1(Gamma_1) => c2a(s_1, ctx: Gamma_1\, Gamma_0), ...); \
      & #h(4em) c2a(s[Gamma' mapsto Gamma'^f], ctx: Gamma'^f\, alpha) \
      & #h(4em) "where" quad Gamma_0 = union_i "freeVars"(s_i) subset Gamma quad "and" quad Gamma' = "freeVars"(s) subset Gamma \
      & c2a(cut(NEW br(D_1(Gamma_1, alpha_1 :^cns tau_1) => s_1, ...), tilde(mu)x. s), ctx: Gamma) := \
      & #h(4em) SUBSTITUTE[Gamma'^f := Gamma', Gamma_0 := Gamma_0]; \
      & #h(4em) CREATE_omega sp x = Gamma_0 br(D_1(Gamma_1, alpha_1 :^cns_1 tau_1) => c2a(s_1, ctx: Gamma_1\, alpha_1\, Gamma_0), ...); \
      & #h(4em) c2a(s[Gamma' mapsto Gamma'^f], ctx: Gamma'^f\, x) \
      & #h(4em) "where" quad Gamma_0 = union_i "freeVars"(s_i) subset Gamma quad "and" quad Gamma' = "freeVars"(s) subset Gamma \
      & c2a(cut(x, CASE br(K_1(Gamma_1) => s_1, ...)), ctx: Gamma) := \
      & #h(4em) SUBSTITUTE[Gamma' := Gamma', x^f := x]; \
      & #h(4em) SWITCH_omega sp x br(K_1(Gamma_1) => c2a(s_1, ctx: Gamma'\,Gamma_1), ...) \
      & #h(4em) "where" quad Gamma' = union_i "freeVars"(s_i) subset Gamma \
      & c2a(cut(NEW br(D_1(Gamma_1, alpha_1 :^cns tau_1) => s_1, ...), alpha), ctx: Gamma) := \
      & #h(4em) SUBSTITUTE[Gamma' := Gamma', alpha^f := alpha]; \
      & #h(4em) SWITCH_1 sp alpha br(D_1(Gamma_1, alpha_1 :^cns_1 tau_1) => c2a(s_1, ctx: Gamma'\,Gamma_1\,alpha_1), ...) \
      & #h(4em) "where" quad Gamma' = union_i "freeVars"(s_i) subset Gamma \
    $
  ],
)

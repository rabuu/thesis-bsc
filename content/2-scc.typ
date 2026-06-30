#import "/lib/lib.typ": *
#import deps: cetz, fletcher

= The Sequent Calculus Compiler <ch:scc>
This chapter provides a summary of the entire Sequent Calculus Compiler (SCC) pipeline as described by Müller et al. @Mueller2026,
and serves as the foundation for the subsequent chapters that will modify and extend it.
The presentation follows the original paper closely, adapted here to establish the notation and terminology used throughout this thesis.

The SCC compiles a functional programming language, called #Fun, to native machine code.
The concrete target architecture is not very relevant here and can easily be adapted.
In the implementation @Mueller2026scc, multiple backend architectures are supported but for the sake of simplicity we only consider #RISC-V in this thesis.

The compiler is a pipeline of translations between the four representation stages that become progressively lower-level.
The intermediate languages #Core and #AxCut are directly based on the classical sequent calculus and thus form the heart of the SCC.

Here is an illustration of the complete SCC compilation pipeline,
where each box represents a compiler stage and the arrows represent the translations between them:

#figure({
  import fletcher: diagram, edge, node

  let colored-node(color) = node.with(stroke: color, fill: color.lighten(65%))

  let fun = (0, 0)
  let core = (2, 0)
  let axcut = (4, 0)
  let riscv = (6, 0)

  show ref: set text(size: settings.font-size-normal - 4pt)

  diagram(
    debug: false,
    node-stroke: 1pt,
    label-sep: 0.2em,
    colored-node(red)(fun, [#Fun \ @sec:scc:fun]),
    colored-node(green)(core, [#Core \ @sec:scc:core]),
    colored-node(blue)(axcut, [#AxCut \ @sec:scc:axcut]),
    colored-node(orange)(riscv, [#RISC-V \ @sec:scc:codegen:riscv]),
    edge(fun, core, "-|>", label: $f2c(dot)$, label-side: left),
    edge(
      fun,
      core,
      "-|>",
      label: [@sec:scc:f2c],
      label-side: right,
      stroke: none,
    ),
    edge(core, axcut, "-|>", label: $c2a(dot)$, label-side: left),
    edge(
      core,
      axcut,
      "-|>",
      label: [@sec:scc:c2a],
      label-side: right,
      stroke: none,
    ),
    edge(axcut, riscv, "-|>", label: $a2m(dot)$, label-side: left),
    edge(
      axcut,
      riscv,
      "-|>",
      label: [@sec:scc:codegen],
      label-side: right,
      stroke: none,
    ),
    edge(
      core,
      core,
      "-|>",
      bend: -125deg,
      label: [
        #set align(center)
        #set par(leading: 5pt)

        $focus(dot), shrink(dot)$ \
        @sec:scc:transformations
      ],
    ),
  )
})

The following sections will explain every stage and translation step-by-step.

== The Surface Language #Fun <sec:scc:fun>
Every compiler pipeline starts with a surface language: the language of its source programs, typically written by a human.
In the case of the SCC, this language is called #Fun @Binder2024grokking.
It is an expression-oriented, functional programming language, extended with some advanced features to showcase the power of the compiler pipeline.
#Fun is not intended as a production-ready programming language, but rather as vehicle for demonstrating what the SCC can handle and how it functions.

=== Syntax
This thesis covers a multiple languages, each with their own syntax.
To help readability, syntax elements that are common to more than one language share the same notation.
Here, we establish a nomenclature that is valid for the rest of this thesis.

#definition(title: "Naming Conventions")[
  - $x,y,...$ are _variable names_,
  - $alpha, beta, ...$ are _covariable names_,
  - $T$ is some user-defined _type name_,
  - $K,D,X$ are _tags_ used for constructors and destructors,
  - and $f$ is a _label_ used for top-level definitions.
] <naming>

With these conventions in place, we can define the syntax of the surface language.

#definition(title: [Syntax of #Fun])[
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
      alt(
        $LABEL alpha br(p)$,
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
      $DEF f(Gamma) : tau br(p)$,
      alt(
        $DATA T br(K(Gamma), ...)$,
        $CODATA T br(D(Gamma) : tau, ...)$,
      ),

      ($Theta$, "Programs"),
      alt(
        $empty$,
        $Theta, sp delta$,
      ),
    )
  ]
] <def:scc:fun>

At its core, #Fun is an ordinary functional language, supporting standard features such as top-level (first-order) functions, variables, (non-recursive) let-bindings, simple integer arithmetic --- in this thesis, only addition is presented as an example ---, and conditional expressions.

Besides built-in machine integers ($i64$), there are user-definable algebraic data and codata types.
Algebraic data types are a familiar concept from many popular statically-typed programming languages --- like Haskell's `data` or Rust's `enum` types.
They are defined by their constructors $K(sigma)$, which produce elements of the data type, and are consumed by pattern matching ($CASE$).
Dually, the less common algebraic codata types @Hagino1989 @Downen2019codata are defined by their destructors $D(sigma)$, which consume elements of the codata type, and are produced by copattern matching ($NEW$) @Abel2013copattern;
they are closely related to interfaces and objects in object-oriented programming.
Together, data and codata provide a general framework for user-defined types, subsuming other desirable features of popular programming languages like lists, streams, and even higher-order function types.

A very interesting feature, especially with regard to the contents of this thesis, are the control operators $LABEL$ and $GOTO$.
They work in a similar fashion to `let/cc` @Reynolds1972letcc, known from the Scheme family of programming languages.
$LABEL$ captures the current computation context --- the so-called _continuation_ --- and binds it to a covariable.
With $GOTO$ such a computation context can be invoked, resulting in non-local control flow.
Another way of breaking the usual control flow of programs is the $EXIT$ expression
that terminates the program with a given exit code.

The naming of terms and covariables as _producers_ and _consumers_, respectively, are chosen to mimic the terminology used for the languages that get introduced later.

#note[TODO: example]

=== Type System
All typing rules for #Fun are shown in @app:form:fun:typing.

Most of the rules are standard.
Interesting are the control operators.
#sidenote[Some explanation of the judgments.]

#figure(rule-set(
  manual-grouping: true,
  (
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
  ),
  prooftree(rule(
    name: rn("Exit"),
    $Gamma tack p : i64$,
    $Gamma tack EXIT p : tau$,
  )),
))
In #rn("Label"), a covariable $alpha$ is added to the context when typing the body of the expression.
If there is a covariable in the current context, #rn("Goto") can be used to invoke it.
Here, the argument must be of the same type as the consumer covariable.
The expression as a whole, however, is allowed to have any type $tau'$ because the computation will not continue at this point, which makes the type irrelevant.
Similarly, the type of an $EXIT$ expression is also arbitrary, since it terminates the program anyway.

== The High-Level Intermediate Language #Core <sec:scc:core>
The next stage in the compilation pipeline is the intermediate representation #Core.
It is an extension of the $lambda mu tilde(mu)$-calculus @Curien2000, a term assignment system for Gentzen's classical sequent calculus LK @Gentzen1935a,
equipped with integer arithmetic, top-level function definitions, and algebraic data and codata types.

While remaining at a relatively high level of abstraction, #Core makes the order and structure of computation very explicit by reifying control flow in the language.
This is similar to continuation-passing style (CPS) @Appel1991cps --- widely used in compilers for functional languages ---
which introduces functions that explicitly represent the current computation context.
In #Core, this is instead achieved by making computation contexts a first-class construct, called _consumers_, in direct symmetry with _producers_, which represent the data that consumers act on.

=== Syntax
Many constructs of #Fun can be found in #Core as well, but adapted for its symmetric structure.
The naming conventions from @naming hold here, too.

#definition(title: [Syntax of #Core])[
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
        $NEW br(D(Gamma) => s, ...)$,
      ),

      ($c$, "Consumers"),
      alt(
        $covar(alpha)$,
        $tilde(mu) x. s$,
      ),
      alt(
        $D(sigma)$,
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
        $f(sigma)$,
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
        $DEF f(Gamma) br(s)$,
        $pi sp T br(X(Gamma), ...)$,
      ),

      ($Theta$, "Programs"),
      alt(
        $empty$,
        $Theta, sp delta$,
      ),
    )
  ]
] <def:scc:core>

There are three separate syntactic categories for terms in #Core: producers, consumers and statements.
Producers and consumers introduce and eliminate static data.
The language becomes dynamic through statements that drive computation forward.
New is the _cut_ statement $cut(p, c)$ where a matching pair of a producer and a consumer interact.

Special about the sequent-calculus-based representation is the almost perfect symmetry of producers and consumers.
Only the built-in integers and arithmetic on them do not have consumer counterparts.
But for algebraic (co)data types, the symmetry is very obvious.
In contrast to #Fun, pattern matches and destructor invocations in #Core are separated from the value they act on and appear as independent consumers.
Hence, there are constructors and copattern matches as producers for data and codata types, respectively,
and corresponding pattern matches and destructors as consumers.

Central to the $lambda mu tilde(mu)$-calculus, and thus #Core, are the abstraction operators $mu$ and $tilde(mu)$.
The producer $mu alpha. s$ captures the current consumer and binds it to the covariable $alpha$ for the scope of its body $s$.
Dually, the consumer $tilde(mu) x. s$ captures the current producer and binds it to the variable $x$ in $s$.
#sidenote[Example?]

In #Core, we have to keep track of both variable and covariable bindings in the typing environments, which also serve as parameter lists.
This is similar to #Fun where we have to distinguish between normal terms and covariabel labels.
Consumers in #Core are even more important and common.
Therefore, each binding is explicitly annotated with its _chirality_, i.e. whether it is a producer ($prd$) or consumer ($cns$).

Another notable aspect of #Core is that top-level definitions and codata destructors do not specify a return type.
Instead, the interaction between caller and callee is generalized by allowing arbitrary consumer arguments that act as _continuations_.
The equivalent of returning from a function or destructor is passing a value to a continuation.
Neatly, since destructors no longer have a return type, the definition of data and codata types become perfectly symmetric.

=== Type System
@fig:scc:core:typing shows the typing rules for #Core.
To keep the presentation concise, well-formedness rules for programs and declarations are omitted.
We assume that all types and names that are used in the program are well-defined and unique.

For every syntactic category, there is a typing judgment form:
The judgments #box($Theta mid Gamma tack p :^prd tau$) and #box($Theta mid Gamma tack c :^cns tau$) type producers and consumers, respectively,
and #box($Theta mid Gamma tack s$) denotes that $s$ is a well-typed statement.
Statements, representing computation, do not have return types themselves.
$Theta$ is the global program context that holds information about all top-level declarations and is often omitted in rules that do not mention it.
The local context $Gamma$ contains the currently active (co)variable bindings.

We make the structural properties of the typing context explicit by giving additional inference rules
that define how bindings in the local context can be manipulated.

#definition(title: [Structural Rules])[
  For statement typing, there are the following structural rules:
  #figure(rule-set(
    manual-grouping: true,
    (
      prooftree(rule(
        name: rn("Weakening"),
        $Gamma tack s$,
        $Gamma, v :^chi tau tack s$,
      )),
      prooftree(rule(
        name: rn("Contraction"),
        $Gamma, v :^chi tau, v :^chi tau tack s$,
        $Gamma, v :^chi tau tack s$,
      )),
    ),
    prooftree(rule(
      name: rn("Exchange"),
      $Gamma_1, v_1 :^chi tau_1, v_2 :^chi tau_2, Gamma_2 tack s$,
      $Gamma_1, v_2 :^chi tau_2, v_1 :^chi tau_1, Gamma_2 tack s$,
    )),
  ))

  The same rules also exist analogously for producer, consumer, and argument typing.
] <def:scc:core:structural>

The rules make it possible to drop, duplicate, and reorder bindings in the context.
Since we can freely use all of the rules, it would also be possible to represent the context as a set
and then, in the rules #rn("Var") and #rn("Covar"), look up whether the (co)variable exists in the context.
For this thesis, the presentation is so explicit because in @ch:lin we will adapt the typing system of #Core for linear continuations which involves modifying the structural properties of the context.

#figure(
  kind: "Figure",
  supplement: "Figure",
  caption: [Typing rules for #Core.],
  block(width: 100%)[
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
          $Theta mid Gamma tack sigma : Gamma'$,
          $Theta mid Gamma tack K(sigma) :^prd T$,
        )),
        prooftree(rule(
          name: rn("New"),
          $CODATA T br(D_1(Gamma_1), ...) in Theta$,
          $forall i: Gamma, Gamma_i tack s_i$,
          $Theta mid Gamma tack NEW br(D_1(Gamma_1) => s_1, ...) :^prd T$,
        )),
      ),
    )

    #def-box[Consumer Typing: $Theta mid Gamma tack c :^cns tau$]

    #rule-set(
      manual-grouping: true,
      (
        prooftree(rule(
          name: rn("Covar"),
          $alpha :^cns tau tack alpha :^cns tau$,
        )),
        prooftree(rule(
          name: rn("Act-L"),
          $Gamma, x :^prd tau tack s$,
          $Gamma tack tilde(mu)x. s :^cns tau$,
        )),
      ),
      (
        prooftree(rule(
          name: rn("Dtor"),
          $CODATA T br(..., D(Gamma'), ...) in Theta$,
          $Theta mid Gamma tack sigma : Gamma'$,
          $Theta mid Gamma tack D(sigma) :^cns T$,
        )),
        prooftree(rule(
          name: rn("Case"),
          $DATA T br(K_1(Gamma_1), ...) in Theta$,
          $forall i: Gamma, Gamma_i tack s_i$,
          $Theta mid Gamma tack CASE br(K_1(Gamma_1) => s_1, ...) :^cns T$,
        )),
      ),
    )

    #def-box[Statement Typing: $Theta mid Gamma tack s$]

    #rule-set(
      prooftree(rule(
        name: rn("Cut"),
        $Gamma tack p :^prd tau$,
        $Gamma tack c :^cns tau$,
        $Gamma tack cut(p, c)$,
      )),
      prooftree(rule(
        name: rn("IfZ"),
        $Gamma tack p :^prd i64$,
        $Gamma tack s_1$,
        $Gamma tack s_2$,
        $Gamma tack IF p equiv 0 br(s_1) ELSE br(s_1)$,
      )),
      prooftree(rule(
        name: rn("Call"),
        $DEF f(Gamma') br(...) in Theta$,
        $Theta mid Gamma tack sigma : Gamma'$,
        $Theta mid Gamma tack f(sigma)$,
      )),
      prooftree(rule(
        name: rn("Exit"),
        $Gamma tack p :^prd i64$,
        $Gamma tack EXIT p$,
      )),
    )

    #def-box[Argument Typing: $Theta mid Gamma tack sigma : Gamma'$]

    #rule-set(
      column-gutter: 1.2em,
      prooftree(rule(
        name: $rn("Arg"_empty)$,
        $Gamma tack empty : empty$,
      )),
      prooftree(rule(
        name: $rn("Arg"_prd)$,
        $Gamma tack sigma : Gamma'$,
        $Gamma tack p :^prd tau$,
        $Gamma tack (sigma, p) : (Gamma', sp x :^prd tau)$,
      )),
      prooftree(rule(
        name: $rn("Arg"_cns)$,
        $Gamma tack sigma : Gamma'$,
        $Gamma tack c :^cns tau$,
        $Gamma tack (sigma, c) : (Gamma', sp alpha :^cns tau)$,
      )),
    )
  ],
) <fig:scc:core:typing>

Most of the rules exist similarly in #Fun (@app:form:fun:typing).
We present all of them here to highlight the symmetry of #Core. #sidenote[And maybe for the contrast to later.]
Except for #rn("Lit") and #rn("Plus"), which are identical to the corresponding rules in #Fun,
all the rules for producers and consumers come in pairs of two: one for the producer, and one for the corresponding consumer.

Concerning (co)data types, the only differences to the rules of #Fun are that (co)pattern matches now have statements as branch bodies
and destructors no longer have a special return type.

New are the two activation rules.
The right activation rule #rn("Act-R") types a producer $mu alpha. s$ which abstracts over a consumer in the body statement.
And, dually, the left activation rule #rn("Act-L") types a consumer $tilde(mu) x. s$ which abstracts over a producer in its body.
In both cases, the type of the abstracted (co)variable must match the type of the abstraction, but with switched chirality.

The statement judgments differ from their corresponding #Fun rules in that they do not yield any return type.
In #rn("IfZ") only the condition producer must have a specific type, namely $i64$, while the branches are now statements themselves.
Calls to top-level definitions do not have a return type, so they become statements, too.
In contrast to #Fun, where the $EXIT$ expression has an arbitrary type, in #Core it is a statement because it represents a computation.
The new #rn("Cut") rule ensures that a producer and a consumer that meet in a cut have the same type.
This guarantees that they can meaningfully interact.

#note[Too much mention of #Fun rules that I moved to the appendix.]

== Translation from #Fun to #Core <sec:scc:f2c>
Now that we formally introduced the surface language #Fun and the first intermediate representation #Core,
this section presents the translation function $f2c(dot)$ that transforms the former into the latter.

This translation bridges the gap between the direct-style #Fun and the two-sided world of the sequent calculus.
It resembles a CPS transformation @Danvy2003cps and works by passing the current continuation as argument of the translation to the correct position.
The transformation is designed to avoid administrative redexes.

At one point, i.e. translating a destructor invocation, the translation makes use of a function $bindvals(dot, dot)$
to lift non-(co)values out of argument position for the destructor.
The reason behind this is not relevant to this thesis.
For the sake of completeness, the definition of (co)values and the lifting function can be found in @app:form:bindval.

#figure(
  kind: "Figure",
  supplement: "Figure",
  caption: [Translation from #Fun to #Core.],
  block(width: 100%)[
    #set math.lr(size: 1em)

    #def-box[$f2c(dot) : "Declaration"_Fun -> "Declaration"_Core$]
    $
      f2c(DEF f(Gamma) : i64 br(p)) & := DEF f(Gamma, alpha :^cns tau) br(f2c(p, with: alpha)) quad(alpha "fresh") \
      f2c(CODATA T br(D_1(Gamma_1): tau_1, ...)) & := CODATA T br(D_1(Gamma_1, alpha_1 :^cns tau_1), ...) quad(alpha_1, ... "fresh") \
      f2c(DATA T br(K_1(Gamma_1), ...)) & := DATA T br(K_1(Gamma_1), ...)
    $

    #def-box[$f2c(dot) : "Producer"_Fun -> "Producer"_Core$]
    #stack(dir: ltr, spacing: 2em)[
      $
               f2c(x) & := x \
        f2c(K(sigma)) & := K(f2c(sigma)) \
      $
    ][
      $
                f2c(n) & := n \
        f2c(p_1 + p_2) & := f2c(p_1) + f2c(p_2) \
      $
    ]
    $
      f2c(NEW br(D_1(Gamma_1) => p_1, ...)) & := NEW br(D_1(Gamma_1, alpha_1) => f2c(p_1, with: alpha_1), ...) \
      f2c(LABEL alpha br(p)) & := mu alpha. f2c(p, with: alpha) \
      f2c(p) &:= mu alpha. f2c(p, with: alpha) quad "for all other producers" p \
    $

    #def-box[$f2c(dot, with: dot.o) : "Producer"_Fun times "Consumer"_Core -> "Statement"_Core$]
    #stack(dir: ltr, spacing: 2em)[
      $
                        f2c(x, with: c) & := cut(x, c) \
                        f2c(n, with: c) & := cut(n, c) \
                 f2c(K(sigma), with: c) & := cut(K(f2c(sigma)), c) \
                 f2c(f(sigma), with: c) & := f(f2c(sigma), c) \
        f2c(LABEL alpha br(p), with: c) & := cut(mu alpha. f2c(p, with: alpha), c) \
      $
    ][
      $
        #hide[$f2c(x, with: c) := cut(x, c)$] \
        f2c(p_1 + p_2, with: c) & := cut(f2c(p_1) + f2c(p_2), c) \
        f2c(p.D(sigma), with: c) & := bindvals(f2c(sigma), lambda overline(a). f2c(p, with: D(overline(a), c))) \
        f2c(EXIT p, with: c) & := EXIT f2c(p) \
        f2c(GOTO alpha sp (p), with: c) & := f2c(p, with: alpha) \
      $
    ]
    $
      f2c(LET x = p_1\; sp p_2, with: c) & := && cases(
        cut(f2c(p_1), tilde(mu)x. f2c(p_2, with: c)) quad & "if" p_1: CODATA T br(...),
        f2c(p_1, with: tilde(mu)x. f2c(p_2, with: c)) quad & "otherwise",
      ) \
      f2c(NEW br(D_1(Gamma_1) => p_1, ...), with: c) & := && cut(NEW br(D_1(Gamma_1, alpha_1) => f2c(p_1, with: alpha_1), ...), c) \
      f2c(p.CASE br(K_1(Gamma_1) => p_1, ...), with: c) & := && f2c(p, with: c_0) quad "where" c_0 equiv CASE br(K_1(Gamma_1) => f2c(p_1, with: tilde(mu)x. j(Gamma)), ...) \
      "with" quad DEF j(Gamma) br(cut(x, c)) quad &&& "and" quad Gamma := "freeVars"(c), sp x :^prd tau quad ("where" c :^cns tau) \
      f2c(IF p equiv 0 br(p_1) ELSE br(p_2), with: c) & := && IF f2c(p) equiv 0 br(f2c(p_1, with: tilde(mu)x. j(Gamma))) ELSE br(f2c(p_2, with: tilde(mu)x. j(Gamma))) \
      "with" quad DEF j(Gamma) br(cut(x, c)) quad &&& "and" quad Gamma := "freeVars"(c), sp x :^prd tau quad ("where" c :^cns tau) \
    $

    #def-box[$f2c(dot) : "Arguments"_Fun -> "Arguments"_Core$]
    $
      f2c(empty) := empty quad quad
      f2c(sigma\, p) := f2c(sigma), f2c(p) quad quad
      f2c(sigma\, alpha) := f2c(sigma), alpha
    $
  ],
) <fig:scc:f2c>

#note[
  Explain the translation. I am not sure yet how much of is relevant enough to explain.

  - Mention `main`
]

== Transformations on #Core <sec:scc:transformations>

=== Focusing
#definition(title: [Focused #Core])[
  #figure[
    #bnf(
      ($p$, "Producers"),
      alt(
        $var(x)$,
        $mu alpha. s$,
      ),
      alt(
        $n$,
        $highlight(x) + highlight(x)$,
      ),
      alt(
        $K(sigma)$,
        $NEW br(D(Gamma) => s, ...)$,
      ),

      ($c$, "Consumers"),
      alt(
        $covar(alpha)$,
        $tilde(mu) x. s$,
      ),
      alt(
        $D(sigma)$,
        $CASE br(K(Gamma) => s, ...)$,
      ),

      ($s$, "Statements"),
      alt(
        $cut(p, c)$,
      ),
      alt(
        $IF sp highlight(x) equiv 0 br(s) ELSE br(s)$,
      ),
      alt(
        $f(sigma)$,
        $EXIT sp highlight(x)$,
      ),

      ($sigma$, "Arguments"),
      alt(
        $empty$,
        $sigma, sp highlight(x)$,
        $sigma, sp highlight(alpha)$,
      ),
    )
  ]
] <def:scc:focused>

=== Shrinking

#definition(title: [Shrunk #Core])[
  #figure[
    #bnf(
      ($s$, "Statements"),
      alt(
        $cut(K(sigma), alpha)$,
        $cut(K(sigma), tilde(mu) x. s)$,
        $cut(x, D(sigma))$,
        $cut(mu alpha. s, D(sigma))$,
      ),
      alt(
        $cut(x, CASE br(K(Gamma) => s, ...))$,
        $cut(mu alpha. s, CASE br(K(Gamma) => s, ...))$,
      ),
      alt(
        $cut(NEW br(D(Gamma) => s, ...), alpha)$,
        $cut(NEW br(D(Gamma) => s, ...), tilde(mu)x. s)$,
      ),
      alt(
        $cut(n, tilde(mu)x. s)$,
        $cut(x + x, tilde(mu)x. s)$,
      ),
      alt(
        $IF x equiv 0 br(s) ELSE br(s)$,
        $f(sigma)$,
        $EXIT x$,
      ),

      ($sigma$, "Arguments"),
      alt(
        $empty$,
        $sigma, sp x$,
        $sigma, sp alpha$,
      ),
    )
  ]
] <def:scc:shrunk>


== The Lower-Level Intermediate Language #AxCut <sec:scc:axcut>

=== Syntax
#definition(title: [Syntax of #AxCut])[
  #figure[
    #bnf(
      ($v$, "(Co)Variables"),
      alt(
        $var(x)$,
        $covar(alpha)$,
      ),

      ($s$, "Statements"),
      $LET v = X(sigma); sp s$,
      $CREATE v = Gamma br(X(Gamma) => s, ...); sp s$,
      $SWITCH v br(X(Gamma) => s, ...)$,
      $INVOKE v sp X(sigma)$,
      $LIT v <- n; sp s$,
      $v <- v + v; sp s$,
      $IF v equiv 0 br(s) ELSE br(s)$,
      $f(sigma)$,
      $EXIT v$,
      $SUBSTITUTE[Gamma := sigma]; sp s$,

      ($sigma$, "Arguments"),
      alt(
        $empty$,
        $sigma, sp v$,
      ),

      ($Gamma$, "Typing Contexts"),
      alt(
        $empty$,
        $Gamma, sp v :^chi tau$,
      ),
    )
  ]
] <def:scc:axcut>

=== Type System
#definition[
  $
    chi_1(DATA) := prd
    quad
    chi_1(CODATA) := cns
    quad
    chi_2(DATA) := cns
    quad
    chi_2(CODATA) := prd
  $
]

#figure(
  kind: "Figure",
  supplement: "Figure",
  caption: [Typing rules for #AxCut.],
  block(width: 100%)[
    #def-box[Statement Typing: $Theta mid Gamma tack s$]
    #rule-set(
      manual-grouping: true,
      (
        prooftree(rule(
          name: $#rn("Let-")pi$,
          $pi T br(..., X(Gamma_0), ...) in Theta$,
          $Gamma, v:^(chi_1(pi)) T tack s$,
          $Theta mid Gamma, Gamma_0 tack LET v = X(Gamma_0); sp s$,
        )),
        prooftree(rule(
          name: $#rn("Create-")pi$,
          $pi T br(X_1(Gamma_1), ...) in Theta$,
          $Gamma, v:^(chi_2(pi)) T tack s$,
          $forall i: Gamma_i, Gamma_0 tack s_i$,
          $Theta mid Gamma, Gamma_0 tack CREATE v = Gamma_0 br(X_1(Gamma_1) => s_1, ...); sp s$,
        )),
        prooftree(rule(
          name: $#rn("Switch-")pi$,
          $pi T br(X_1(Gamma_1), ...) in Theta$,
          $forall i: Gamma, Gamma_i tack s_i$,
          $Theta mid Gamma, v :^(chi_1(pi)) T tack SWITCH v br(X_1(Gamma_1) => s_1, ...)$,
        )),
        prooftree(rule(
          name: $#rn("Invoke-")pi$,
          $pi T br(..., X(Gamma), ...) in Theta$,
          $Theta mid Gamma, v :^(chi_2(pi)) T tack INVOKE v sp X(Gamma)$,
        )),
      ),
      (
        prooftree(rule(
          name: rn("Substitute"),
          $Gamma tack sigma : Gamma'$,
          $Gamma' tack s$,
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

    #def-box[Argument Typing: $Theta mid Gamma tack sigma : Gamma'$]
    #rule-set(
      prooftree(rule(
        name: $rn("Arg"_empty)$,
        $Gamma tack empty : empty$,
      )),
      prooftree(rule(
        name: $rn("Arg")$,
        $Gamma tack sigma : Gamma'$,
        $v :^chi tau in Gamma$,
        $Gamma tack (sigma, v) : (Gamma', sp v :^chi tau)$,
      )),
    )
  ],
) <fig:scc:axcut:typing>

== Translation from #Core to #AxCut <sec:scc:c2a>
#note[Improve formatting.]
#big-figure[
  #set math.lr(size: 1em)

  #def-box[$c2a(dot) : "Definition"_("Shrunk" Core) -> "Definition"_AxCut$]
  $
    c2a(DEF f(Gamma) br(s)) & := && DEF f(Gamma) br(c2a(s, ctx: Gamma))
  $

  #def-box[$c2a(dot, ctx: dot.o) : "Statement"_("Shrunk" Core) times "Context"_AxCut -> "Statement"_AxCut$]
  $
    c2a(cut(K(Gamma_0), tilde(mu)x. s), ctx: Gamma) & := && SUBSTITUTE[Gamma' := Gamma', Gamma_0^f := Gamma_0]; \
    &&& LET x = K(Gamma_0^f); sp c2a(s, ctx: Gamma'\, x) \
    "where" &&& Gamma' = "freeVars"(s) subset Gamma \
    c2a(cut(mu alpha. s, D(Gamma_0)), ctx: Gamma) & := && SUBSTITUTE[Gamma' := Gamma', Gamma_0^f := Gamma_0]; \
    &&& LET alpha = D(Gamma_0^f); sp c2a(s, ctx: Gamma'\, alpha) \
    "where" &&& Gamma' = "freeVars"(s) subset Gamma \
    c2a(cut(K(Gamma_0), alpha), ctx: Gamma) & := && SUBSTITUTE[Gamma_0^f := Gamma_0, alpha := alpha]; sp INVOKE alpha sp K(Gamma_0^f) \
    c2a(cut(x, D(Gamma_0)), ctx: Gamma) & := && SUBSTITUTE[Gamma_0^f := Gamma_0, x := x]; sp INVOKE x sp D(Gamma_0^f) \
    c2a(cut(x, CASE br(K_1(Gamma_1) => s_1, ...)), ctx: Gamma) & := && SUBSTITUTE[Gamma' := Gamma', x^f := x]; \
    &&& SWITCH x br(K_1(Gamma_1) => c2a(s_1, ctx: Gamma'\,Gamma_1), ...) \
    "where" &&& Gamma' = union.big_i "freeVars"(s_i) subset Gamma \
    c2a(cut(NEW br(D_1(Gamma_1) => s_1, ...), alpha), ctx: Gamma) & := && SUBSTITUTE[Gamma' := Gamma', alpha^f := alpha]; \
    &&& SWITCH alpha br(D_1(Gamma_1) => c2a(s_1, ctx: Gamma'\,Gamma_1), ...) \
    "where" &&& Gamma' = union.big_i "freeVars"(s_i) subset Gamma \
    c2a(cut(mu alpha. s, CASE br(K_1(Gamma_1) => s_1, ...)), ctx: Gamma) & := && SUBSTITUTE[Gamma'^f := Gamma', Gamma_0 := Gamma_0]; \
    &&& CREATE alpha = Gamma_0 br(K_1(Gamma_1) => c2a(s_1, ctx: Gamma_1\, Gamma_0), ...); \
    &&& c2a(s[Gamma' mapsto Gamma'^f], ctx: Gamma'^f\, alpha) \
    "where" &&& Gamma_0 = union.big_i "freeVars"(s_i) subset Gamma quad Gamma' = "freeVars"(s) subset Gamma \
    c2a(cut(NEW br(D_1(Gamma_1) => s_1, ...), tilde(mu)x. s), ctx: Gamma) & := && SUBSTITUTE[Gamma'^f := Gamma', Gamma_0 := Gamma_0]; \
    &&& CREATE x = Gamma_0 br(D_1(Gamma_1) => c2a(s_1, ctx: Gamma_1\, Gamma_0), ...); \
    &&& c2a(s[Gamma' mapsto Gamma'^f], ctx: Gamma'^f\, x) \
    "where" &&& Gamma_0 = union.big_i "freeVars"(s_i) subset Gamma quad Gamma' = "freeVars"(s) subset Gamma \
    c2a(cut(n, tilde(mu)x. s), ctx: Gamma) & := && SUBSTITUTE[Gamma' := Gamma']; sp LIT x <- n; sp c2a(s, ctx: Gamma'\, x) \
    "where" &&& Gamma' = "freeVars"(s) subset Gamma \
    c2a(cut(x_1 + x_2, tilde(mu)x. s), ctx: Gamma) & := && SUBSTITUTE[Gamma' := Gamma']; sp x <- x_1 + x_2; sp c2a(s, ctx: Gamma'\, x) \
    "where" &&& Gamma' = ({x_1, x_2} union "freeVars"(s)) subset Gamma \
    c2a(IF x equiv 0 br(s_1) ELSE br(s_2), ctx: Gamma) & := && IF x equiv 0 br(c2a(s_1, ctx: Gamma)) ELSE br(c2a(s_2, ctx: Gamma)) \
    c2a(f(Gamma_0), ctx: Gamma) & := && SUBSTITUTE[Gamma_0^f := Gamma_0]; sp f(Gamma_0^f) \
    c2a(EXIT x, ctx: Gamma) & := && EXIT x
  $
]

== Code Generation <sec:scc:codegen>
The final step of the SCC is code generation, translating #AxCut into native machine code.
For the purposes of this thesis, #RISC-V @Waterman2014riscv was chosen as the target architecture due to its simplicity.
The translation works nearly identically for other architectures since it only relies on ubiquitous assembly concepts and does not apply any techniques or optimizations that depend on a particular instruction set.

=== The Target Language #RISC-V <sec:scc:codegen:riscv>
This is the subset of #RISC-V used as target of the code generation:

#definition(title: [Syntax of #RISC-V])[
  #figure[
    #bnf(
      ($I$, "Instructions"),
      alt(
        $l:$,
        $ADD r sp r sp r$,
        $ADDI r sp r sp i$,
        $MV r sp r$,
      ),
      alt(
        $LI r sp i$,
        $LA r sp l$,
        $LW r sp i sp r$,
        $SW r sp i sp r$,
      ),
      alt(
        $JUMP o$,
        $JR r sp o$,
        $BEQ r sp r sp o$,
        $ECALL$,
      ),

      ($r$, "Registers"),
      alt(
        $#reg(0)$,
        $#reg(1)$,
        $...$,
        $#reg(31)$,
      ),

      ($l$, "Labels"),
      alt(
        $#lab(0)$,
        $#lab(1)$,
        $...$,
      ),

      ($i$, "Immediates"),
      alt(
        $#imm(0)$,
        $#imm(1)$,
        $...$,
      ),

      ($o$, "Offsets"),
      alt(
        $l$,
        $i$,
      ),
    )
  ]
] <def:scc:riscv>

In #RISC-V, there are 32 registers, each containing one word.
The register #reg(0) always contains the value 0, all other registers can be used freely.
A program consists of a list of instructions.
Labels can be attached to instructions and then be referenced by other instructions.

With $ADD$ and $ADDI$, the two values of the second and third operand are added:
For $ADD$, that is the contents of two registers, for $ADDI$ the contents of a register and an immediate value.
The sum is put into the register specified by the first operand.
$MV$ copies the contents of the second register into the first.
The $LI$ and $LA$ instructions directly load values into a register.
For $LI$, that is an immediate integer value, and for $LA$ an instruction address, given by a label.

$LW$ and $SW$ are responsible for memory access.
Both of them compute a memory address by adding an offset, given by the immediate operand, to the value in the third operand's register.
Then, $LW$ loads the memory word at this address into its first operand's register, and $SW$ writes the contents of the first register to the memory address.

There are three instructions for jumping.
The destination of the unconditional jump $JUMP$ is specified directly, whereas the indirect jump $JR$ computes it by adding an immediate offset to the address in its register operand.
The conditional branching instruction $BEQ$ compares the values of its two register operands: if they are equal, it jumps to the given destination, otherwise the execution just continues.
#sidenote[Add $BNE$]

Lastly, $ECALL$ is used to make a system call.
Before invoking it, the required arguments must be placed in certain registers, specified by the operating system.

=== The Model
#note[
  - $Gamma$ is registers
  - A variable living in $Gamma$ takes up two registers
  - $REG_1$, $REG_2$
  - Memory blocks and their layout
  - Constant-time lazy reference counting @Lam2024
]

#figure(
  kind: "Figure",
  supplement: "Figure",
  caption: [The layout of heap memory blocks.],
)[
  #grid(
    columns: 2,
    column-gutter: 4em,
    row-gutter: 1em,
    align: (right + horizon, center + horizon),
    [in free list],
    cetz.canvas({
      import diagram: *
      memblock(
        data: ([`next`],),
      )
    }),

    [in use],
    cetz.canvas({
      import diagram: *
      memblock(
        data: ([`rc`],),
        fill: (reserved,) * 2 + (free-to-use,) * 6,
      )
    }),
  )
] <fig:scc:codegen:layout>

=== Translation from #AxCut to #RISC-V
The next subsections define the translation function $a2m(dot)$ that generates RISC-V assembly code from #AxCut.
Each #AxCut construct is explained separately.

#note[
  TODO:
  - Objects are Virtual Tables, Closures are Memory Blocks, Destructor Invocations are Indirect Jumps
  - Highlight: $LET$ and $CREATE$ acquire memory, $SWITCH$ and $INVOKE$ release memory
  - Share increases refcount, erase decreases refcount
]

==== Programs, Top-Level Definitions, and Calls
An #AxCut program is a list of type declarations and top-level definitions.
Since type declarations have no computational relevance, only the definitions are translated to machine code.
This is as easy as attaching the definition label to the first instruction of the translated body statement.
$ a2m(DEF f(Gamma) br(s)) & := && f: a2m(s) $
A call to top-level definition can now be translated as an unconditional jump to the definition's label.
$ a2m(f(Gamma)) := JUMP f $
The parameters $Gamma$ are just the current state of the registers and thus handled by #AxCut's $SUBSTITUTE$ statement.

==== Substitutions
The current context in #AxCut corresponds to the register values in the machine.
It is the job of the $SUBSTITUTE$ statements to prepare the registers for the subsequent statements which means reordering the contents of the registers.
If this involves dropping or duplicating variables that point to heap-allocated data, it must also modify the reference count of that data.

The reordering is achieved by a parallel moves algorithm @Rideau2008parallelmoves written as $MOVE$ that is not further explained here.

#note[$SHARE$ and $ERASE$]

$
  a2m(SUBSTITUTE[Gamma' := sigma]\; sp s) & := && SHARE [Gamma' := sigma] \
                                          &    && ERASE [Gamma' := sigma] \
                                          &    && MOVE [Gamma' := sigma] \
                                          &    && a2m(s)
$

==== Machine Integers, Conditionals, and Termination
The use of extern constructs translates to hardware instructions and system calls.
For integer literals and arithmetic expressions, this is a simple application of the primitive machine instructions.
$
  a2m(LIT v <- n\; sp s) & := && LI (REG_2 sp v) sp n \
  & && a2m(s) \
  a2m(v <- v_1 + v_2\; sp s) & := && ADD (REG_2 sp v) sp (REG_2 sp v_1) sp (REG_2 sp v_2) \
  & && a2m(s) \
$

An $IF$ statement in #AxCut translates to a conditional branch.
For that, we introduce a fresh label $l$.
$
  a2m(IF v equiv 0 br(s_1) ELSE br(s_2)) & := && BEQ (REG_2 sp v) #reg(0) l \
                                         &    && #hide[$l:$] a2m(s_2) \
                                         &    && l: a2m(s_1) \
$

And lastly, the $EXIT$ statement results in a system call to terminate the program.
The exact requirements for a system call depend on the operating system.
This is an exemplary translation for the Linux Kernel which requires the system call number #imm(93) in #reg(17) and the argument in #reg(10).
$
  a2m(EXIT v) & := && LI #reg(17) #imm(93) \
              &    && MV #reg(10) (REG_2 sp v) \
              &    && ECALL \
$

==== Let-Bindings and Pattern Matches
A $LET$-binding in #AxCut binds a constructor or destructor to a variable.
In the machine code, the fields of the constructor (or destructor) are stored in newly allocated memory using $STORE$ which is explained later in @sec:scc:codegen:mem.
The registers that were occupied by those fields are free use to again.
Instead, a new variable is created in the registers. It consists of a pointer to the stored memory block and the index of the constructor (or destructor) tag.
$
  a2m(LET v = X(Gamma_0)\; s) & := && STORE (REG_1 sp v) sp Gamma_0 \
                              &    && LI (REG_2 sp v) sp (INDEX X) \
                              &    && a2m(s)
$
The index of the constructor (or destructor) is an offset value for the jump table that is explained next.
It is calculated by multiplying the position of the constructor (or destructor) in its type declaration by four.

$LET$-bound variables in #AxCut are consumed by pattern matches using the $SWITCH$ statement.
The translation function turns a $SWITCH$ statement into an indirect jump into a so-called jump table.

Jump tables are defined as follows. Here the labels $l_i$ are fresh.
$
  JTABLE { X_1(Gamma_1) => s_1, ... } sp Gamma & := && JUMP l_1 \
  &&& JUMP l_2 \
  &&& ... \
  &&& JTABLEB { X_1(Gamma_1) => s_1, ... } sp Gamma sp (l_1, l_2, ...) \
  JTABLEB { X_1(Gamma_1) => s_1, ...} sp Gamma sp (l_1, l_2, ...) & := && l_1: LOAD (REG_1 sp x) sp Gamma_1 \
  &&& #hide[$l_1:$] a2m(s_1) \
  &&& JTABLEB { X_2(Gamma_2) => s_2, ... } sp Gamma sp (l_2, l_3, ...)
$

With this definition of jump tables, the translation of $SWITCH$ statements is easy.
$
  a2m(SWITCH v sp b) & := && JR (REG_2 sp v) sp l \
                     &    && l: JTABLE b sp Gamma
$
The variable which the pattern match acts on has two components:
the pointer to the fields of the constructor or destructor that were stored in memory and the tag index.
Firstly, the tag index is used to get to the correct $JUMP$ instruction, and then the jump table itself is generated.
In every branch the fields are loaded back into the registers. This is done using a the variable that stand after $Gamma$, above called $x$, which is exactly the variable $v$ which holds the memory pointer.

#note[This needs more work. Examples would be good.]

==== Objects and Invocations
The $CREATE$ instruction is similar to the $LET$ instruction in that it also creates a new variable.
But in contrast to binding a constructor or destructor to a variable, it creates a closure object.

#note[Unfinished!]

$
  VTABLE { X_1(Gamma_1) => s_1, ... } sp Gamma_0 & := && JUMP l_1 \
  &&& JUMP l_2 \
  &&& ... \
  &&& VTABLEB { X_1(Gamma_1) => s_1, ...} sp Gamma_0 (l_1, l_2, ...) \
  VTABLEB { X_1(Gamma_1) => s_1, ...} sp Gamma sp (l_1, l_2, ...) & := && l_1: LOAD (REG_1 sp x) sp Gamma_0 \
  &&& #hide[$l_1:$] a2m(s_1) \
  &&& VTABLEB { X_2(Gamma_2) => s_2, ... } sp Gamma sp (l_2, l_3, ...)
$

#note[Note the $Gamma_0$ in the $LOAD$.]

$
  a2m(CREATE v = Gamma_0 sp b\; s) & := && STORE (REG_1 sp v) sp Gamma_0 \
                                   &    && LA (REG_2 sp v) sp l \
                                   &    && a2m(s) \
                                   &    && l: VTABLE b sp Gamma_0 \
         a2m(INVOKE v sp X(Gamma)) & := && JR (REG_2 sp v) sp (INDEX X) \
$

=== Memory Management <sec:scc:codegen:mem>
#figure[
  $
    LOAD r sp Gamma & := && RELEASE r \
    & && LOADV r sp Gamma \
    LOADV r sp (Gamma, v:^chi tau) & := && LW (REG_2 sp v) sp (OFFSET_2 sp v) sp r \
    & && LW (REG_1 sp v) sp (OFFSET_1 sp v) sp r \
    & && LOADV r sp Gamma \
    STORE r sp Gamma & := && STOREV r sp Gamma \
    & && ACQUIRE r \
    STOREV (Gamma, v:^chi tau) & := && SW (REG_2 sp v) sp (OFFSET_2 sp v) sp HEAP \
    & && SW (REG_1 sp v) sp (OFFSET_1 sp v) sp HEAP \
    & && STOREV r sp Gamma \
    RELEASE r & := && LW TEMP #imm(0) sp r \
    &&& BEQ TEMP #reg(0) l_1 \
    &&& #hide[$l_1:$] ADDI TEMP TEMP #imm(-1) \
    &&& #hide[$l_1:$] SW TEMP #imm(0) sp r \
    &&& #hide[$l_1:$] SHAREFIELDS r \
    &&& #hide[$l_1:$] JUMP l_2 \
    &&& l_1: SW HEAP #imm(0) sp r \
    &&& #hide[$l_1:$] MV HEAP r \
    &&& l_2: \
    ACQUIRE r & := && MV r HEAP \
    &&& LW HEAP #imm(0) HEAP \
    &&& BEQ HEAP #reg(0) l_1 \
    &&& #hide[$l_1:$] SW #reg(0) #imm(0) sp r \
    &&& #hide[$l_1:$] JUMP l_2 \
    &&& l_1: MV HEAP TODO \
    &&& #hide[$l_1:$] LW TODO #imm(0) TODO \
    &&& #hide[$l_1:$] BEQ TODO #reg(0) l_3 \
    &&& #hide[$l_1:$] #hide[$l_3:$] SW #reg(0) #imm(0) HEAP \
    &&& #hide[$l_1:$] #hide[$l_3:$] ERASEFIELDS HEAP \
    &&& #hide[$l_1:$] #hide[$l_3:$] JUMP l_2 \
    &&& #hide[$l_1:$] l_3: ADDI TODO HEAP #imm(32) \
    &&& l_2: \
  $
]

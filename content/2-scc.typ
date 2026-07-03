#import "/lib/lib.typ": *
#import deps: cetz, fletcher

= The Sequent Calculus Compiler <ch:scc>
This chapter summarizes the complete Sequent Calculus Compiler (SCC) pipeline as presented by Müller et al. @Mueller2026.
It provides the technical foundation for the remainder of this thesis.

The SCC compiles a functional programming language, called #Fun, to native machine code.
The concrete target architecture is not conceptually essential and can easily be adapted.
In the implementation @Mueller2026scc, multiple backends are supported.
For this thesis, we pick #RISC-V as target architecture for simplicity.

The compiler consists of a sequence of translations through progressively lower-level representations.
The intermediate languages #Core and #AxCut are directly based on the classical sequent calculus and therefore form the conceptual center of the SCC design.

The following figure shows the full pipeline.
Each box represents a compiler stage and the arrows represent the translations between them.

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

The rest of this chapter introduces each stage and translation step-by-step.

== The Surface Language #Fun <sec:scc:fun>
Every compiler pipeline begins with a surface language: the language in which source programs are written.
For the SCC, this language is #Fun @Binder2024grokking.

#Fun is an expression-oriented, functional programming language.
It is not intended to be a production language, but a compact vehicle for demonstrating the SCC's concepts.
In particular, its support for control operators makes it well suited for studying how complex control flow is represented and compiled.

=== Syntax
This thesis uses several related languages, each with their own syntax.
To keep notation brief and consistent, shared concepts are written uniformly across sections.
We first fix naming conventions that remain valid throughout the thesis.

#definition(title: "Naming Conventions")[
  - $x,y,...$ are _variable names_,
  - $alpha, beta, ...$ are _covariable names_,
  - $T$ is some user-defined _type name_,
  - $K,D,X$ are _tags_ used for constructors and destructors,
  - and $f$ is a _label_ used for top-level definitions.
] <naming>

With these conventions in place, we can define #Fun.

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

At its core, #Fun is an ordinary direct-style functional language:
top-level (first-order) function definitions, variables, non-recursive let-bindings, machine integers, arithmetic (only addition is shown), and conditionals.

Besides built-in integers ($i64$), #Fun has user-defined algebraic data and codata types.
Data types are defined by constructors $K(sigma)$ that produce elements of the data type and consumed by pattern matching ($CASE$).
Dually, the less common codata types @Hagino1989 @Downen2019codata are defined by destructors $D(sigma)$ that consume elements of the codata type and produced by copattern matching ($NEW$) @Abel2013copattern.
This gives a uniform framework that can model many familiar language abstractions like lists, streams, and higher-order function types.

For this thesis, a crucial #Fun feature are control operators.
$LABEL$ captures the current computation context, the so-called _continuation_, and binds it to a covariable;
$GOTO$ invokes such a continuation and can therefore cause non-local control flow.
This is similar to how some Scheme languages provide explicit access to the current continuation via `let/cc` @Reynolds1972letcc.

Additionally, $EXIT$ terminates the program immediately with a status code.

#note[TODO: example]

=== Type System
All #Fun typing rules are listed in @app:form:fun:typing.
Most rules are standard.
For later chapters, the interesting rules are those for control operators:

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
))

Rule #rn("Label") extends the context with a continuation binding.
Rule #rn("Goto") invokes a continuation that is in scope and has a type matching the argument.
The whole expression may have an arbitrary type $tau'$ because control flow does not continue at this point.

== The High-Level Intermediate Language #Core <sec:scc:core>
The next stage is #Core.
It extends the $lambda mu tilde(mu)$-calculus @Curien2000, which is a term assignment system for Gentzen's classical sequent calculus LK @Gentzen1935a,
with integer arithmetic, top-level definitions, and algebraic (co)data.

#Core remains relatively high-level, but unlike #Fun it makes control flow explicit.
This resembles continuation-passing style (CPS) @Appel1991cps in spirit, but uses the symmetry of the sequent calculus.
Producers represent data and consumers represent first-class computation contexts.

=== Syntax
Many constructs from #Fun reappear in #Core, adapted to its two-sided structure.

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

#Core has three separate syntactic categories for terms: producers, consumers, and statements.
Producers and consumers describe how data can be introduced and eliminated;
statements drive computation.
The central computational form is the cut $cut(p, c)$ where a matching pair of a producer and a consumer interact.

A defining property of #Core is its producer/consumer symmetry.
For (co)data, constructs appear in dual pairs: constructors and destructors, pattern matches and copattern matches.
This is possible because, in contrast to #Fun, pattern matches and destructor invocations are represented independently of the value they act on.
Built-in integers and arithmetic are the main asymmetric exception.

Top-level definitions and destructors in #Core do not have a return type.
Instead, the interaction between caller and callee is generalized by allowing arbitrary consumer arguments that act as _continuations_.
The equivalent of returning from a function or destructor is passing a value to a continuation.
Neatly, since destructors no longer have a return type, the definition of data and codata types become perfectly symmetric.

The abstractions $mu$ and $tilde(mu)$ capture the current opposite side:
$mu alpha. s$ is a producer that captures the current consumer and binds it as covariable $alpha$ in its body $s$;
$tilde(mu) x. s$ is a consumer that captures the current producer and binds it as $x$.
The ability for producers and consumers to abstract over the other side of a cut is central to the language
and corresponds to $LET$-bindings and control operators.

In #Core, each context binding is annotated with its chirality, i.e. whether it is a producer ($prd$) or consumer ($cns$).

=== Type System
@fig:scc:core:typing shows the typing rules for #Core.
To keep the presentation concise, well-formedness rules for programs and declarations are omitted.
We assume that all types and names that are used in the program are well-defined and unique.

There is one judgment form per syntactic category:
#box($Theta mid Gamma tack p :^prd tau$) for producers,
#box($Theta mid Gamma tack c :^cns tau$) for consumers,
and #box($Theta mid Gamma tack s$) for statements.
Statements, representing computation, have no type.
$Theta$ is the global context that holds all top-level declarations and is often omitted in rules that do not mention it.
$Gamma$ is the local context of active (co)variable bindings.

We explicitly include structural context rules that define how bindings in the local context can be manipulated.
Specifically, they make it possible to drop, duplicate, and reorder bindings in the context.
This matters later in @ch:lin, where these rules are restricted for continuation linearity.

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

  Analogous rules exist for consumer, producer, and argument typing.
] <def:scc:core:structural>

#figure(
  kind: "Figure",
  supplement: "Figure",
  caption: [Typing rules for #Core.],
  block(width: 100%)[
    #def-box[Declaration Typing: $Theta tack delta$]
    #rule-set(
      prooftree(rule(
        name: rn("Def"),
        $Theta mid Gamma tack s$,
        $Theta tack DEF f(Gamma) br(s)$,
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

The side-by-side presentation of the rules expose the language symmetry clearly:
except for integer-specific rules, producer and consumer rules occur in dual pairs.

The right activation rule #rn("Act-R") types a producer $mu alpha. s$ that abstracts over a consumer in its body.
Dually, the left activation rule #rn("Act-L") types a consumer $tilde(mu) x. s$ that abstracts over a producer in its body.
In both cases, the abstracted (co)variable must have the same base type as the abstraction, but with opposite chirality.

#rn("Cut") enforces that the producer and consumer that meet in a cut have matching types.
This ensures that they can meaningfully interact.

== Translating #Fun to #Core <sec:scc:f2c>
We now define the translation $f2c(dot)$ that maps direct-style #Fun to continuation-explicit #Core.
The definition is shown in @fig:scc:f2c.

Generally, the translation is designed to avoid unnecessary administrative redexes.
However, this thesis presents a simplified version.
The original definition @Mueller2026[ sec. 5] incorporates several optimizations to eliminate as many administrative redexes as possible,
along with additional performance-oriented improvements.

Conceptually, this step resembles a CPS transformation @Danvy2003cps:
the translation is parameterized by the current continuation and threads it to the right place.
In this way, the translation turns implicit return flow into explicit continuation passing.

Top-level definitions and codata destructors receive an additional consumer argument at the end of their parameter lists.
Calls and destructor invocations pass the current continuation explicitly.

The translations of the control operators are of particular relevance to this thesis,
as they are the only constructs for which the current continuation $c$ is not passed through linearly.
$
  f2c(LABEL alpha br(p), with: c) := cut(mu alpha. f2c(p, with: alpha), c) #h(4em)
  f2c(GOTO alpha sp (p), with: c) & := f2c(p, with: alpha) \
$
$LABEL$ translates to a $mu$ abstraction directly.
By explicitly binding the right-hand side of the cut to a covariable,
it makes it possible for the current continuation to be referenced multiple times.
$GOTO$ discards the current continuation altogether and continues the translation using the specified covariable instead.

#figure(
  kind: "Figure",
  supplement: "Figure",
  caption: [Translation from #Fun to #Core.],
  block(width: 100%)[
    #set math.lr(size: 1em)

    #def-box[$f2c(dot) : "Declaration"_Fun -> "Declaration"_Core$]
    $
      f2c(DEF f(Gamma) : tau br(p)) & := DEF f(Gamma, alpha :^cns tau) br(f2c(p, with: alpha)) quad(alpha "fresh") \
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
      // @typstyle off
      $
      f2c(LET x = p_1\; sp p_2, with: c) & := cut(f2c(p_1), tilde(mu) x. f2c(p_2, with: c))\
        f2c(p_1 + p_2, with: c) & := cut(f2c(p_1) + f2c(p_2), c) \
        f2c(p.D(sigma), with: c) & := cut(f2c(p), D(f2c(sigma), c)) \
        f2c(EXIT p, with: c) & := EXIT f2c(p) \
        f2c(GOTO alpha sp (p), with: c) & := f2c(p, with: alpha) \
      $
    ]
    $
      f2c(NEW br(D_1(Gamma_1) => p_1, ...), with: c) & := && cut(NEW br(D_1(Gamma_1, alpha_1) => f2c(p_1, with: alpha_1), ...), c) \
      f2c(p.CASE br(K_1(Gamma_1) => p_1, ...), with: c) & := && f2c(p, with: CASE br(K_1(Gamma_1) => f2c(p_1, with: c), sp ...)) \
      f2c(IF p equiv 0 br(p_1) ELSE br(p_2), with: c) & := && IF f2c(p) equiv 0 br(f2c(p_1, with: c)) ELSE br(f2c(p_2, with: c)) \
    $

    #def-box[$f2c(dot) : "Arguments"_Fun -> "Arguments"_Core$]
    $
      f2c(empty) := empty quad quad
      f2c(sigma\, p) := f2c(sigma), f2c(p) quad quad
      f2c(sigma\, alpha) := f2c(sigma), alpha
    $
  ],
) <fig:scc:f2c>

== Transformations on #Core <sec:scc:transformations>
Before translating a #Core program to #AxCut, we must bring it in a certain normal form.
We split this process into two transformations, each targeting a small fragment of #Core.

=== Focusing
The focusing transformation $focus(dot)$ gives names to all subterms by lifting complex terms out of argument position.
This is an extension of static focusing @Curien2000.
The full transformation definition can be found in @app:form:focusing.
The resulting focused #Core fragment is similar to A-normal form @Flanagan1993anf @Binder2022anf in that terms in argument position must be a variable or covariable.

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

#note[TODO: example]

=== Shrinking
After focusing, we apply the shrinking transformation $shrink(dot)$.
It reduces the syntax of the language to only statements by inlining all producers and consumers into cuts.
Then, it eliminates as many cut combinations as possible from the language.

Many combinations of producers and consumers meeting in a cut cannot occur anyway because of typing.
Cuts that only introduce new names for (co)variables can be removed by renaming.
Critical pairs --- where a $mu$ abstraction meets a $tilde(mu)$ abstraction --- can be removed by choosing the side to expand;
this choice exactly corresponds to evaluation order, we choose call-by-value for data and call-by-name for codata.
Unknown cuts --- where a variable and a covariable meet --- can be removed by $eta$-expansion of one side, again depending on the polarity.

Thus, the transformation leaves us with a shrunk fragment of #Core that only consists of certain cuts and statements.

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

#note[TODO: example]

== The Lower-Level Intermediate Language #AxCut <sec:scc:axcut>
The next compiler stage is #AxCut.
This is the final intermediate representation of the pipeline which is directly translated into machine code.
It is close to shrunk #Core but is structured to make it better suitable for code generation.

Due to the symmetry of #Core, there are still some redundancies left.
Specifically, shrunk #Core has a number of completely dual constructs that carry the exact same computational meaning @Ostermann2022.
For example, both $cut(K(sigma), tilde(mu)x. s)$ and $cut(mu alpha. s, D(sigma))$ bind a tagged variant to a name.
In #AxCut, these dual constructs are merged into a unified syntax.
This also means, the distinction between producers and consumers becomes blurrier: variables and covariables are treated identically.

In #AxCut, the context of currently active bindings has an explicit order and statements expect it to be in a certain shape.
Explicit substitutions manipulate the (co)variables that are currently in scope and to prepare them for subsequent statements.
Formerly implicit context operations --- reordering, duplicating, and dropping of (co)variables --- become explicit on the term level in #AxCut.
This resembles the register operations that are needed in machine code.

=== Syntax
#note[very short introduction for this section]

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
      $EXIT v$,
      $f(sigma)$,
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

#note[Explain every construct of #AxCut]

=== Type System
#note[Some intro sentence.]

The duality of the rules allows for a uniform presentation of the rules.
We formulate these symmetric rules using the following notation, connecting polarity and chirality.

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

At its basis, the type system of #AxCut is ordered.
That means, there are no structural rules --- like for #Core --- that can be used to implicitly manipulate the context.
Instead, the context in #AxCut should be understood as strictly ordered list which is only modified explicitly by the statements of the program.
The only exception to that are the rules concerning built-in integers where the position in the context does not matter.

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
          name: rn("Exit"),
          $v :^prd i64 in Gamma$,
          $Gamma tack EXIT v$,
        )),
      ),
      (
        prooftree(rule(
          name: rn("Call"),
          $DEF f(Gamma) br(...) in Theta$,
          $Theta mid Gamma tack f(Gamma)$,
        )),
        prooftree(rule(
          name: rn("Substitute"),
          $Gamma tack sigma : Gamma'$,
          $Gamma' tack s$,
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
        $v :^chi tau in Gamma$,
        $Gamma tack (sigma, v) : (Gamma', sp v :^chi tau)$,
      )),
    )
  ],
) <fig:scc:axcut:typing>

The #rn("Substitute") rule is the explicit replacement for the structural rules of exchange, weakening, and contraction.
It allows rearranging the current context, where the new context can arbitrarily reorder, duplicate, and drop (co)variables from the old context.

In the rules #rn("Plus"), #rn("IfZ"), and #rn("Exit"), the arguments are checked to be integers.
Notably, it is only important that the corresponding binding exists somewhere in the context, the position is not relevant.
This is different for all other rules.

By rule #rn("Call"), a top-level function invocation is only valid if the arguments exactly match the current context.
This is denotet by $f(Gamma)$, meaning $f$ is applied exactly to the (co)variables in the context.
This means, in a program a function call is usually preceded by an $SUBSTITUTE$ statement that brings the context into the right shape.

The most important rules for the purposes of this thesis are the four rules concerning (co)variables of (co)data types.
They are parameterized by the polarity (data or codata) of the variable they introduce/eliminate.

In #rn("Let"), a constructor or destructor is bound to a (co)variable.
The fields must exactly match the last part of the current context and are then removed from the context.
The subsequent statement is typed with the (co)variable in scope, with the binding annotating the chirality:
producer for a constructor and as consumer for a destructor.

#rn("Create") is similar to #rn("Let").
Here we allocate a closure object and bind it to a (co)variable.
Like the fields of $LET$, the $CREATE$ statement consumes its closure environment $Gamma_0$ from the context.
This closure environment is used to type check the branches of the object.
In the subsequent statement, the object (co)variable is now in scope; as consumer for data types and as producer for codata types.

The #rn("Switch") rule ensures that $SWITCH$ consumes the (co)variable it acts on from the context,
the remaining context is used to type check the branches.
Because a producer scrutinee must be data and a consumer scrutinee must be codata, the (co)variable must stem from a $LET$ statement.

And dually, the #rn("Invoke") only allows for (co)variables that were introduced by $CREATE$.
Here, the (co)variable must be the final binding of the context and the rest must exactly match the arguments of the constructor/destructor.

== Translating #Core to #AxCut <sec:scc:c2a>
#note[Intro text for the final translation.]

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
        $BNE r sp r sp o$,
      ),
      alt(
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
The conditional branching instructions $BEQ$ and $BNE$ compare the values of the two register operands:
$BNE$ jumps to the given destination if they are equal, otherwise the execution just continues;
$BNE$ branches if they are not equal.

Lastly, $ECALL$ is used to make a system call.
Before invoking it, the required arguments must be placed in certain registers, specified by the operating system.

=== The Runtime Model
#AxCut is already pretty close to how the program execution works in machine code.

A program in machine code is a sequence of instructions that primarily modify the state of the processor registers for computation.
Besides the registers, it also uses the main memory to store data.
A program in #AxCut is a sequence of statements that modify the state of the typing context.
Indeed, the current state of the context in #AxCut directly models the registers while execution.

In a running program, we reserve some registers for special purposes, the rest is used to store the (co)variable bindings.
Each (co)variable occupies two registers.

#figure(cetz.canvas({
  import cetz.draw: *
  import diagram: *

  let regy = 4

  slots(
    11,
    labels: (none, reg("temp"), reg("heap"), reg("todo"), none),
    data: (imm(0),) + (none,) * 9 + (ddd,),
    offset: (0, regy),
    open-right: true,
  )

  brace(6, offset: (4, regy), label: $Gamma$)
  brace(2, offset: (4, regy - 1), label: $v_1$, flipped: true)
  brace(2, offset: (6, regy - 1), label: $v_2$, flipped: true)
  brace(2, offset: (8, regy - 1), label: ddd, flipped: true)
}))

The register #reg(0) is always #imm(0), $TEMP$ is used as scratch register, and $HEAP$ and $TODO$ are used for memory management.
The rest of the registers is used for storing the context bindings.
Of course, in practice there is only a limited number of registers (32 in #RISC-V), which means sometimes not all (co)variables can be stored in the registers.
We ignore this restriction in this thesis, but in the implementation this is solved by spilling any (co)variables that do not fit to memory.

#note[
  TODO:
  - Objects are Virtual Tables, Closures are Memory Blocks, Destructor Invocations are Indirect Jumps
  - Highlight: $LET$ and $CREATE$ acquire memory, $SWITCH$ and $INVOKE$ release memory
  - $SHARE$, $ERASE$, and $MOVE$
  - $REG_1$, $REG_2$
]

=== Memory Management <sec:scc:codegen:mem>
(Co)variables can reference memory-allocated data.
In particular, a $LET$ statement stores the fields of the constructor/destructor in memory, and $CREATE$ stores the closure environment in memory.
This means, we need an automatic memory management to track allocated memory.


In the SCC, we do not maintain a stack like what other compilers commonly do.
Instead, we only use heap memory that is managed using a constant-time reference counting @Lam2024 strategy.
That means, we conceptually divide the memory into equal-sized blocks that we allocate and free individually.
Each block contains eight slots that hold one word.
Two consecutive slots are referred to as field, so there are four fields per block.

The memory blocks are managed in two separate free lists.
The $HEAP$ register points to the first block of the linear free list which contains blocks that are immediatly free to use.
The $TODO$ register points to the lazy free list. The blocks in the lazy free list may still contain references to other blocks and that must be erased before using the block.

==== Memory Layout
For both free lists, the first slot of each block stores the pointer to the next block. If there is no next block, this first slot must contain #imm(0).
We will refer to the offset into the memory block to get to pointer to the next block of the free list as $NEXTBLOCKOFFSET$.
$ NEXTBLOCKOFFSET := #imm(0) $

We always maintain the invariant that $HEAP$ must point to a free-to-use memory block.
The $TODO$ register, on the other hand, may be #imm(0) if there is no block in the lazy free list.

If a memory block was allocated from a free list and is in use,
only the latter three fields can be used for actual payload.
The first field is reserved for metadata.
In the current design, that is only the reference count for the allocated memory block.
This reference count is stored in the first slot, the offset into the block to reach the reference count is referred to as $REFCOUNTOFFSET$.
$ REFCOUNTOFFSET := #imm(0) $

The following figure illustrates the layout of memory blocks.
Here, `next` stands for the pointer to the next block of the free list --- potentially #imm(0) if there is none ---,
and `rc` denotes the reference count for allocated blocks.
They reserved slots are marked in gray, the slots that are free-to-use are highlighted in green.

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

Now we will introduce the memory management primitives.

==== Share and Erase
Memory blocks that are in use store a reference count in their first slot.
If there is exactly one (co)variable that stores a pointer to this block, the reference count is #imm(0).
For each additional reference, it is increased by one.
The primitive operation that increments the reference count is called sharing, and the operation that decrements it is called erasing.

$SHAREBLOCK$ expects the address of a memory block in a register $r$ and an immediate value $n$.
It checks if $r$ contains a valid pointer and then increments the reference count of the block by $n$.
The label $l$ is fresh.
$
  SHAREBLOCK r sp n & := && BEQ r #reg(0) l \
                    &    && #hide[$l:$] LW TEMP REFCOUNTOFFSET r \
                    &    && #hide[$l:$] ADDI TEMP TEMP n \
                    &    && #hide[$l:$] SW TEMP REFCOUNTOFFSET sp r \
                    &    && l: \
$

$SHAREFIELDS$ is used to share the children of a given memory block.
It calls #box[$SHAREBLOCK f sp 1$] for every field of the block where $f$ is the content of the first slot of the field.
This is #imm(0) for integers --- and thus skipped by $SHAREBLOCK$ --- and a pointer to the referenced data for (co)variables of (co)data types.

Corresponding primitives exists for erasing.

$ERASEBLOCK$ handles the situation if a reference to memory block is dropped.
If the given register $r$ contains a valid pointer, it checks if the reference count is #imm(0).
If that is the case, it prepends the block to the lazy free list.
Importantly, it does not free its children fields in this process, this will happen on demand when the block is needed.
If the reference count is positive, it is just decremented.
The labels $l_1,l_2$ are fresh.

$
  ERASEBLOCK r & := && BEQ r #reg(0) l_1 \
               &    && #hide[$l_1:$] LW TEMP REFCOUNTOFFSET r \
               &    && #hide[$l_1:$] BEQ TEMP #reg(0) l_2 \
               &    && #hide[$l_1:$] #hide[$l_2:$] ADDI TEMP TEMP #imm(-1) \
               &    && #hide[$l_1:$] #hide[$l_2:$] SW TEMP REFCOUNTOFFSET r \
               &    && #hide[$l_1:$] #hide[$l_2:$] JUMP l_1 \
               &    && #hide[$l_1:$] l_2: SW TODO NEXTBLOCKOFFSET r \
               &    && #hide[$l_1:$] #hide[$l_2:$] MV TODO r \
               &    && l_1: \
$

$ERASEFIELDS$ erases the children of a given memory block by calling #box[$ERASEBLOCK f$] for all fields of the block.
Again, $f$ refers to the first slot of each field.

==== TODO
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

=== Translating #AxCut to #RISC-V
The next subsections define the translation function $a2m(dot)$ that generates RISC-V assembly code from #AxCut.
Each #AxCut construct is explained separately.

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

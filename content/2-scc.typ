#import "/lib/lib.typ": *
#import deps: cetz, fletcher

= The Sequent Calculus Compiler <ch:scc>
This chapter summarizes the complete Sequent Calculus Compiler (SCC) pipeline @Mueller2026.
It provides the technical foundation for the remainder of this thesis.

The SCC compiles a functional programming language, called #Fun, to native machine code.
The concrete target architecture is not conceptually relevant and can easily be adapted.
In the implementation @Mueller2026scc, multiple backends are supported.
For this thesis, we pick #RISC-V as target architecture for simplicity.

The compiler consists of a sequence of translations through progressively lower-level representations.
The intermediate languages #Core and #AxCut are directly based on the classical sequent calculus and form the conceptual center of the SCC design.

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
It is not intended to be a production language, but a compact vehicle for demonstrating how the SCC operates.
In particular, its support for control operators makes it well suited for studying how complex control flow is represented and compiled.

=== Syntax
This thesis covers several related languages, each with its own syntax.
To keep notation brief and consistent, shared concepts are written uniformly across sections.
We first fix naming conventions that remain valid throughout the thesis.

#definition(title: "Naming Conventions")[
  - $x,y,...$ are _variable names_,
  - $alpha, beta, ...$ are _covariable names_,
  - $T$ is a user-defined _type name_,
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
Data types are defined by constructors $K(sigma)$ that produce elements of the data type and are consumed by pattern matching ($CASE$).
Dually, codata types @Hagino1989 @Downen2019codata are defined by destructors $D(sigma)$ that consume elements of the codata type and are produced by copattern matching ($NEW$) @Abel2013copattern.
This gives a uniform framework that can model many familiar language abstractions like lists, streams, and higher-order function types.

For this thesis, a crucial feature of #Fun is its control operators.
$LABEL$ captures the current computation context, the so-called _continuation_, and binds it to a covariable;
$GOTO$ invokes such a continuation and can therefore cause non-local control flow.

#example[
  Consider the following #Fun program that illustrates core features of the language,
  including data and codata types, (co)pattern matching, and function calls.
  It serves as a running example throughout the remainder of this chapter.

  Notably, the example does not include control operators.
  Programs that make use of $LABEL$ and $GOTO$ are analyzed in @sec:lin:flow.

  #figure[
    #set align(left)
    #stack(
      dir: ttb,
      spacing: 1em,
      pseudo(
        $DATA Bool br(quad True, quad False quad)$,
        $DATA List br(quad Nil, quad Cons(x : i64, xs : List) quad)$,
        $CODATA Pred br(quad apply(x : i64): Bool quad)$,
      ),
      stack(
        dir: ltr,
        spacing: 1fr,
        pseudo(
          indent: 1.5em,
          $DEF all(p : Pred, ell : List): Bool {$,
          (
            $ell .CASE {$,
            (
              $Nil => True,$,
              $Cons(x, xs) => p.apply(x).CASE {$,
              (
                $True => all(p, xs),$,
                $False => False,$,
              ),
              $}$,
            ),
            $}$,
          ),
          $}$,
        ),
        pseudo(
          indent: 1.5em,
          $DEF f(): Bool {$,
          (
            $LET ell = Cons(#imm(0), Cons(#imm(1), Nil));$,
            $LET p = NEW { sp apply(x) =>$,
            (
              $IF x equiv #imm(0) br(True)$,
              $ELSE sp sp sp sp sp br(False)$,
            ),
            $};$,
            $all(p, ell)$,
          ),
          $}$,
        ),
      ),
    )
  ]
  The example defines standard Boolean and integer list data types.
  Predicates are represented as codata with a single $apply(#none)$ destructor
  --- conceptually, a predicate can be viewed as a first-class function of type $i64 -> Bool$.

  The function $all(#none)$ recursively traverses the list $ell$ and returns $False$ as soon as the predicate $p$ does not hold for one of its elements;
  if the predicate holds for every element, the function returns $True$.
  This is achieved by pattern matching on the list and on the Boolean value returned by the predicate's destructor.

  Function $f$ demonstrates a use of $all(#none)$.
  It constructs a list and binds it to the variable $ell$.
  It then creates a predicate by copattern matching, binds it to $p$,
  and finally invokes $all(#none)$ with these two arguments.
  Here, $f$ returns $False$ because not all elements of $ell$ are #imm(0).
] <ex:scc:fun>

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
It is based on the $lambda mu tilde(mu)$-calculus @Curien2000, which is a term assignment system for Gentzen's classical sequent calculus LK @Gentzen1935a.
#Core extends it with integer arithmetic, top-level definitions, and algebraic (co)data types.

#Core makes control flow explicit by reifying computation contexts as first-class constructs called consumers.
This is similar to continuation-passing style (CPS) @Appel1991cps, where computation contexts are instead encoded as functions.

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

#Core has three separate syntactic categories for terms: producers, consumers, and statements (also known as commands).
Producers and consumers describe how data can be introduced and eliminated;
statements drive computation.
The central computational form is the cut $cut(p, c)$, where a matching producer and consumer interact.

A defining property of #Core is its producer/consumer symmetry.
For (co)data, constructs appear in dual pairs: constructors and destructors, pattern matches and copattern matches.
This is possible because, in contrast to #Fun, pattern matches and destructor invocations are represented independently of the value they act on.
Built-in integers and arithmetic have no consumer counterparts.

Top-level definitions and destructors in #Core do not have a return type.
Instead, the interaction between caller and callee is generalized by allowing arbitrary consumer arguments that act as _continuations_.
In #Core, returning from a function or destructor corresponds to passing a value to a continuation.
Since destructors no longer have a return type, the definitions of data and codata types become perfectly symmetric.

The abstractions $mu$ and $tilde(mu)$ capture the current opposite side of a cut:
$mu alpha. s$ is a producer that captures the current consumer and binds it as covariable $alpha$ in its body $s$;
$tilde(mu) x. s$ is a consumer that captures the current producer and binds it as $x$.
The ability for producers and consumers to abstract over the other side of a cut is central to the language,
and subsumes control operators and $LET$-bindings in #Fun.

In #Core, each binding is annotated with its chirality, i.e., whether it is a producer ($prd$) or consumer ($cns$).

#example[
  This is the #Core equivalent of @ex:scc:fun.
  The formal translation is presented later in @sec:scc:f2c.

  #figure[
    #set align(left)
    #stack(
      dir: ttb,
      spacing: 1em,
      pseudo(
        $DATA Bool br(quad True, quad False quad)$,
        $DATA List br(quad Nil, quad Cons(x :^prd i64, xs :^prd List) quad)$,
        $CODATA Pred br(quad apply(x :^prd i64, alpha :^cns Bool) quad)$,
      ),
      stack(
        dir: ltr,
        spacing: 1fr,
        pseudo(
          indent: 1.5em,
          $DEF all(#none)(p :^prd Pred,$,
          $#h(3.7em) ell :^prd List, sp kappa :^cns Bool) sp {$,
          (
            $cl ell | CASE {$,
            (
              $Nil => cut(True, kappa),$,
              $Cons(x, xs) => cl p | apply(#none)($,
              (
                $x,$,
                $CASE {$,
                (
                  $True => all(p, xs, kappa),$,
                  $False => cut(False, kappa),$,
                ),
                $})cr$,
              ),
            ),
            $} cr$,
          ),
          $}$,
        ),
        pseudo(
          indent: 1.5em,
          $DEF f(kappa :^cns Bool) sp {$,
          (
            $cl Cons(#imm(0), Cons(#imm(1), Nil)) sp | sp tilde(mu) ell. cl$,
            (
              $NEW { sp apply(x, alpha) =>$,
              (
                $IF x equiv #imm(0) br(cut(True, alpha))$,
                $ELSE sp sp sp sp sp br(cut(False, alpha))$,
              ),
              $} sp | sp tilde(mu) p. all(p, ell, kappa) cr cr$,
            ),
          ),
          $}$,
        ),
      ),
    )
  ]

  Top-level function definitions and destructors no longer return values, as in #Fun.
  Instead, return types are replaced by an additional consumer argument representing the continuation
  (here $kappa$ for functions and $alpha$ for destructors).
  Computation proceeds by explicitly invoking or forwarding the continuation rather than returning a result.

  This change is also reflected at the call site of functions or destructors.
  Instead of receiving a returned value and using it, a consumer is passed directly as an argument to the called function or destructor, acting as the continuation.

  In $f$, the $tilde(mu)$ abstraction binds producers to variables.
  This corresponds directly to $LET$-bindings in #Fun.
] <ex:scc:core>

=== Type System
@fig:scc:core:typing shows the typing rules for #Core.
To keep the presentation concise, well-formedness rules for programs and declarations are omitted.
We assume that all types and names that are used in the program are well-defined and unique.

There is one judgment form per syntactic category:
- #box($Theta mid Gamma tack p :^prd tau$) for producers,
- #box($Theta mid Gamma tack c :^cns tau$) for consumers,
- and #box($Theta mid Gamma tack s$) for statements.
Statements, representing computation, have no type.
$Theta$ is the global context that holds all top-level declarations and is often omitted in rules that do not mention it.
$Gamma$ is the local context of in-scope (co)variable bindings.

In #Core, we conceptually treat the typing context as a set.
For typing, the order of bindings is irrelevant.
Since (co)variables may be dropped or used multiple times, the rules #rn("Var") and #rn("Covar") only check whether the relevant binding is present in the context.

The side-by-side presentation of the rules expose the language symmetry clearly:
except for integer-specific rules, producer and consumer rules occur in dual pairs.

The right activation rule #rn("Act-R") types a producer $mu alpha. s$ that abstracts over a consumer in its body.
Dually, the left activation rule #rn("Act-L") types a consumer $tilde(mu) x. s$ that abstracts over a producer in its body.
In both cases, the abstracted (co)variable must have the same type as the abstraction, but with opposite chirality.

#rn("Cut") enforces that the producer and consumer that meet in a cut have matching types.
This ensures that they can meaningfully interact.

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
          $alpha :^cns tau in Gamma$,
          $Gamma tack alpha :^cns tau$,
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
        $Gamma tack IF p equiv 0 br(s_1) ELSE br(s_2)$,
      )),
      prooftree(rule(
        name: rn("Call"),
        $DEF f(Gamma') br(...) in Theta$,
        $Theta mid Gamma tack sigma : Gamma'$,
        $Theta mid Gamma tack f(sigma)$,
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

== Translating #Fun to #Core <sec:scc:f2c>
We now define the translation $f2c(dot)$ that maps direct-style #Fun to #Core with explicit continuations.
The full definition is shown in @fig:scc:f2c.

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
as they are the only constructs for which the current continuation $c$ is not passed along linearly.
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
        #hide[$f2c(x, with: c) & := cut(x, c)$] \
        f2c(p_1 + p_2, with: c) & := cut(f2c(p_1) + f2c(p_2), c) \
        f2c(p.D(sigma), with: c) & := cut(f2c(p), D(f2c(sigma), c)) \
        f2c(LET x = p_1\; sp p_2, with: c) & := cut(f2c(p_1), tilde(mu) x. f2c(p_2, with: c))\
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
Before translating #Core to #AxCut, the SCC applies two normalization steps.
Both transformations target a progressively smaller subset of #Core.

=== Focusing <sec:scc:focusing>
The focusing transformation $focus(dot)$ lifts complex subterms out of argument positions by binding them to a name.
This is an extension of static focusing @Curien2000.
The transformation is defined in @app:form:focusing.

The resulting fragment resembles A-normal form @Flanagan1993anf @Binder2022anf:
arguments are restricted to variables and covariables.
The differences from @def:scc:core are highlighted.

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

#example[
  This is the focused version of the $all(#none)$ function from the running example.

  #figure[
    #pseudo(
      $DEF all(p :^prd Pred, ell :^prd List, kappa :^cns Bool) sp {$,
      (
        $cl ell | CASE {$,
        (
          $Nil => cut(True, kappa),$,
          $Cons(x, xs) => cl mu alpha. cut(p, apply(x, alpha)) | CASE {$,
          ($True => all(p, xs),$, $False => cut(False, kappa),$),
          $} cr$,
        ),
        $} cr$,
      ),
      $}$,
    )
  ]

  In @ex:scc:core, the inner pattern match appears directly as an argument to $apply(#none)$.
  The focusing transformation lifts such complex terms out of argument position by introducing a covariable via a $mu$ abstraction, which names the intermediate computation.
] <ex:scc:focused>

=== Shrinking <sec:scc:shrinking>
After focusing, the shrinking transformation $shrink(dot)$ reduces syntax further by inlining producers and consumers into cuts and then eliminating redundant cut patterns.

Many cuts are ruled out directly by typing.
Trivial naming cuts are removed by renaming.
Critical pairs ($mu$ against $tilde(mu)$) are resolved by $eta$-expanding one side.
The choice of which side to expand corresponds to the evaluation strategy:
we choose call-by-value for data and call-by-name for codata to ensure that all $eta$-laws hold @Binder2024grokking.
Unknown cuts (variable against covariable) are also handled by $eta$-expansion.
The full definition is in @app:form:shrinking.

The result is a small statement-only fragment.

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

The focused version of the running example from @ex:scc:focused already lies within this shrunk fragment and is therefore not affected by the transformation.

== The Lower-Level Intermediate Language #AxCut <sec:scc:axcut>
#AxCut is the final compiler stage before machine code.
It is close to shrunk #Core, but restructured to be more suitable for code generation.
There are two main differences to shrunk #Core.

First, #AxCut merges dual constructs from #Core that have identical computational content @Ostermann2022.
For example, both $cut(K(sigma), tilde(mu)x. s)$ and $cut(mu alpha. s, D(sigma))$ binds a tagged variant to a name.
#AxCut represents such duals uniformly.
As a consequence, the distinction between variables and covariables becomes less visible, syntactically and operationally.

Second, context operations are made explicit:
reordering, duplication, and dropping of context bindings are no longer implicit structural properties,
but explicit term-level actions via substitutions.

=== Syntax
We first define #AxCut's syntax.

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

Conditionals and calls to top-level definitions remain unchanged.
Integers and arithmetic have separate syntactic constructs.

The treatment of (co)data and (co)variables is unified and appears in dual pairs.
$LET$ binds a constructor or destructor to a name, and $SWITCH$ matches on it.
$CREATE$ introduces a closure object with methods, which can be invoked with a destructor/constructor via $INVOKE$.

Generally, a producer variable for data is introduced by $LET$.
A producer variable for codata is introduced by $CREATE$.
Dually, a continuation for data is introduced by $CREATE$,
while a continuation for codata is introduced by $LET$.

In #Fun and #Core, bound (co)variables may be used multiple times or not at all.
In #AxCut, however, the context must be managed via explicit substitutions.
The new #box[$SUBSTITUTE[Gamma := sigma]$] statement replaces the context with $Gamma$, which is constructed from currently active bindings.
Within $Gamma$, bindings may be reordered, duplicated, or omitted.
The notation #box[$v'_1 := v_1, v'_2 := v_2, ...$] is used as shorthand for a substitution in which $v'_1, v'_2, ...$ form the new context $Gamma$.

#example[
  In #AxCut, the $all(#none)$ function from the running example is represented as follows.
  The general translation from shrunk #Core is defined in @sec:scc:c2a.

  #figure[
    #pseudo(
      $DEF all(p :^prd Pred, ell :^prd List, kappa :^cns Bool) sp {$,
      (
        $SUBSTITUTE[p := p, sp kappa := kappa, sp ell := ell];$,
        $SWITCH ell sp {$,
        (
          $Nil =>$,
          (
            $SUBSTITUTE[kappa := kappa];$,
            $INVOKE kappa True,$,
          ),
          $Cons(x, xs) =>$,
          (
            $SUBSTITUTE[p_2 := p, sp x := x, sp kappa := kappa, sp xs := xs, sp p_1 := p];$,
            $CREATE alpha = (kappa, sp xs, sp p_1) sp {$,
            (
              $True =>$,
              (
                $SUBSTITUTE[p_1 := p_1, sp xs := xs, sp kappa := kappa];$,
                $all(p_1, xs, kappa),$,
              ),
              $False =>$,
              (
                $SUBSTITUTE[kappa := kappa]$,
                $INVOKE kappa False$,
              ),
            ),
            $};$,
            $SUBSTITUTE[x := x, sp alpha := alpha, sp p_2 := p_2];$,
            $INVOKE p_2 apply(x, alpha)$,
          ),
        ),
        $}$,
      ),
      $}$,
    )
  ]

  Like in shrunk #Core, control flow is completely explicit and every intermediate computation is named.

  The pattern match on $ell$ is represented by a $SWITCH$ statement.
  In the $Nil$ branch, the continuation $kappa$ is invoked directly.
  In the $Cons(#none)$ branch, the predicate's destructor is invoked with an explicit continuation.
  This continuation is encoded as the closure $alpha$, which represents the case distinction on the Boolean result.
  It captures the relevant bindings from the environment and forwards them to the recursive call in the $True$ branch.

  Preceding each statement, explicit substitutions modify the context.
  Depending on the subsequent computation, bindings are either propagated, dropped, or duplicated as required.
]

=== Type System
The typing rules for #AxCut are presented in @fig:scc:axcut:typing.

To allow for a compact presentation of dual rules, we relate polarity and chirality via the following notation.

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

The #AxCut type system is ordered: the context is strictly treated as a list.
Context manipulation is done through statements.

#rn("Substitute") makes this explicit.
Substitutions can reorder, drop, and duplicate (co)variables by building a new context from old bindings.

For most rules, the order of the context matters.
The exceptions are integer-specific statements:
#rn("Plus") and #rn("IfZ") only require the existence of integer bindings in the context, not exact position, and they do not consume these variables.
Usually, statements in #AxCut are preceded by an explicit substitution that prepares the context for the subsequent statement.

For this thesis, the four (co)data rules are particularly relevant.

The #rn("Let") rule binds a constructor or destructor to a (co)variable.
The fields must exactly match the final part of the current context and are then removed from it.
The body is type-checked with the bound (co)variable in scope, where the binding is annotated with its chirality:
as a producer for constructors and as a consumer for destructors.

#rn("Create") is similar.
It allocates a closure object and binds it to a (co)variable.
As with the fields consumed by $LET$, the $CREATE$ statement removes its closure environment $Gamma_0$ from the context.
The closure environment is used to type-check the methods of the object.
In the subsequent statement, the object (co)variable is in scope, acting as a consumer for data and as a producer for codata.

The #rn("Switch") rule ensures that $SWITCH$ consumes the (co)variable it acts on from the context,
while the remaining context is used to type-check the branches.
Since a producer scrutinee must be data and a consumer scrutinee must be codata, the (co)variable must have been introduced by a $LET$ statement.

Dually, #rn("Invoke") only permits (co)variables introduced by $CREATE$.
The invoked (co)variable must be the final binding in the context, while the remainder of the context must exactly match the arguments of the corresponding constructor or destructor.

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
          name: rn("Call"),
          $DEF f(Gamma) br(...) in Theta$,
          $Theta mid Gamma tack f(Gamma)$,
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

== Translating #Core to #AxCut <sec:scc:c2a>
After shrinking, #Core statements are translated to #AxCut by $c2a(dot)$.
This translation makes context restructuring explicit and maps dual cut patterns to unified #AxCut constructs.
The full translation is given in @fig:scc:c2a.

The translation frequently introduces fresh names for bindings in explicit substitutions.
We use the following notation: $v^f$ denotes a fresh name for the variable $v$, and in $Gamma^f$ every binding is replaced with a fresh name.

#figure(
  kind: "Figure",
  supplement: "Figure",
  caption: [Translation from shrunk #Core to #AxCut.],
)[
  #set math.lr(size: 1em)

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
    "where" &&& Gamma' = union_i "freeVars"(s_i) subset Gamma \
    c2a(cut(NEW br(D_1(Gamma_1) => s_1, ...), alpha), ctx: Gamma) & := && SUBSTITUTE[Gamma' := Gamma', alpha^f := alpha]; \
    &&& SWITCH alpha br(D_1(Gamma_1) => c2a(s_1, ctx: Gamma'\,Gamma_1), ...) \
    "where" &&& Gamma' = union_i "freeVars"(s_i) subset Gamma \
    c2a(cut(mu alpha. s, CASE br(K_1(Gamma_1) => s_1, ...)), ctx: Gamma) & := && SUBSTITUTE[Gamma'^f := Gamma', Gamma_0 := Gamma_0]; \
    &&& CREATE alpha = Gamma_0 br(K_1(Gamma_1) => c2a(s_1, ctx: Gamma_1\, Gamma_0), ...); \
    &&& c2a(s[Gamma' mapsto Gamma'^f], ctx: Gamma'^f\, alpha) \
    "where" &&& Gamma_0 = union_i "freeVars"(s_i) subset Gamma quad Gamma' = "freeVars"(s) subset Gamma \
    c2a(cut(NEW br(D_1(Gamma_1) => s_1, ...), tilde(mu)x. s), ctx: Gamma) & := && SUBSTITUTE[Gamma'^f := Gamma', Gamma_0 := Gamma_0]; \
    &&& CREATE x = Gamma_0 br(D_1(Gamma_1) => c2a(s_1, ctx: Gamma_1\, Gamma_0), ...); \
    &&& c2a(s[Gamma' mapsto Gamma'^f], ctx: Gamma'^f\, x) \
    "where" &&& Gamma_0 = union_i "freeVars"(s_i) subset Gamma quad Gamma' = "freeVars"(s) subset Gamma \
    c2a(cut(n, tilde(mu)x. s), ctx: Gamma) & := && SUBSTITUTE[Gamma' := Gamma']; sp LIT x <- n; sp c2a(s, ctx: Gamma'\, x) \
    "where" &&& Gamma' = "freeVars"(s) subset Gamma \
    c2a(cut(x_1 + x_2, tilde(mu)x. s), ctx: Gamma) & := && SUBSTITUTE[Gamma' := Gamma']; sp x <- x_1 + x_2; sp c2a(s, ctx: Gamma'\, x) \
    "where" &&& Gamma' = ({x_1, x_2} union "freeVars"(s)) subset Gamma \
    c2a(IF x equiv 0 br(s_1) ELSE br(s_2), ctx: Gamma) & := && IF x equiv 0 br(c2a(s_1, ctx: Gamma)) ELSE br(c2a(s_2, ctx: Gamma)) \
    c2a(f(Gamma_0), ctx: Gamma) & := && SUBSTITUTE[Gamma_0^f := Gamma_0]; sp f(Gamma_0^f) \
  $
] <fig:scc:c2a>

== Code Generation <sec:scc:codegen>
The final step is code generation from #AxCut to native machine code.
For this thesis, we target #RISC-V @Waterman2014riscv.
The translation style is largely backend-independent and uses only common assembly-level mechanisms.

=== The Target Language #RISC-V <sec:scc:codegen:riscv>
We use the following subset of #RISC-V.

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
The register #reg(0) always holds the value #imm(0)\; all other registers are general-purpose.
A program is a sequence of instructions.
Labels may be attached to instructions and referenced as jump destinations.

$ADD$ and $ADDI$ add the values of their second and third operand and write the sum into the first operand's register.
$MV$ copies the contents of the second register into the first.
$LI$ loads an integer into a register and $LA$ loads an instruction address, given by a label.

$LW$ and $SW$ are responsible for memory access.
Both of them compute a memory address by adding an offset, given by the immediate operand, to the value in the third operand's register.
Then, $LW$ loads the word at this address in memory into its first operand's register,
and $SW$ writes the contents of the first register to the memory address.

There are four instructions for jumping.
The destination of the unconditional jump $JUMP$ is specified directly, whereas the indirect jump $JR$ computes it by adding an immediate offset to the address in its register operand.
The conditional branching instructions $BEQ$ and $BNE$ compare the values of the two register operands:
$BEQ$ jumps to the given destination if they are equal, $BNE$ if they are not;
otherwise, the execution just continues.

=== The Runtime Model
#AxCut already resembles the low-level execution model closely.
Its context state corresponds to the register state during execution.

Some registers are reserved for special purposes.
All remaining registers encode currently active (co)variable bindings.
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

Register #reg(0) is constant #imm(0), $TEMP$ is a scratch register, $HEAP$ and $TODO$ are used for memory management.
All other registers are mapped to context bindings.

For each (co)variable $v$ in the context, we denote its corresponding first register by $REG_1 sp v$ and its corresponding second register by $REG_2 sp v$.

There is only a limited number of registers (32 in #RISC-V), which means, in practice, sometimes not all (co)variables can be stored in registers.
We ignore this restriction in this thesis, but this is solved by spilling any additional (co)variables to memory.

=== Memory Management <sec:scc:codegen:mem>
(Co)variables may point to heap-allocated memory.
In particular, $LET$ stores constructor/destructor fields in memory, and $CREATE$ stores closure environments.
Therefore, code generation requires automatic memory management.

The SCC uses heap-only allocation with constant-time reference counting @Lam2024.
This means memory is conceptually partitioned into equal-sized blocks that are allocated and freed individually.
Each block contains eight slots --- one slot is one word --- and two slots form a field.

#figure(cetz.canvas({
  import cetz.draw: *
  import diagram: *

  scale(0.7)

  let regy = 4

  content((0, regy - 0.5), [Registers])
  slots(
    17,
    labels: (none, reg("temp"), reg("heap"), reg("todo")),
    data: (imm(0),) + (none,) * 15 + (ddd,),
    offset: (2, regy),
    open-right: true,
  )

  let memy1 = 2
  let memy2 = 0
  let memx1 = 2
  let memx2 = 11
  content((0, memy1 - 0.5), [Memory])
  memblock(offset: (memx1, memy1))
  memblock(offset: (memx1, memy2))
  memblock(offset: (memx2, memy1))
  memblock(offset: (memx2, memy2))

  // linear free list
  ptr(
    (4.5, regy - 0.6),
    (4.5, regy - 1.4),
    (memx1 + 0.5, regy - 1.4),
    (memx1 + 0.5, memy1),
  )

  ptr(
    (memx1 + 0.5, memy1 - 0.6),
    (memx1 + 0.5, memy2),
  )

  halfptr1(
    (memx1 + 0.5, memy2 - 0.6),
    (memx1 + 0.5, memy2 - 1.2),
  )

  halfptr2(
    (memx1 + 0.5, memy2 - 1.2),
    (memx1 + 0.5, memy2 - 2),
  )

  // lazy free list
  ptr(
    (5.5, regy - 0.6),
    (5.5, regy - 1.4),
    (memx2 + 0.5, regy - 1.4),
    (memx2 + 0.5, memy1),
  )

  ptr(
    (memx2 + 0.5, memy1 - 0.6),
    (memx2 + 0.5, memy2),
  )

  halfptr1(
    (memx2 + 0.5, memy2 - 0.6),
    (memx2 + 0.5, memy2 - 1.2),
  )

  halfptr2(
    (memx2 + 0.5, memy2 - 1.2),
    (memx2 + 0.5, memy2 - 2),
  )
}))

Unallocated memory blocks are managed in two separate free lists.

The $HEAP$ register points to the first block of the _linear_ free list, which contains blocks that are immediately free to use.
The memory management operations must always maintain the invariant that $HEAP$ points to a directly usable block.

The $TODO$ register points to the _lazy_ free list where blocks may still contain references to other blocks that must be erased before being used.
If the lazy free list is empty, $TODO$ points to the beginning of the remaining unused memory region.
This region is automatically allocated at program initialization and consists entirely of zeros.

==== Memory Layout
In both free lists, the first slot of each block stores the pointer to the next block.
$ NEXTBLOCKOFFSET := #imm(0) $
The last block of the linear free list stores a #imm(0) in its first slot;
the last block of the lazy free list points to the unused memory region.

When a block is allocated, its first field contains metadata.
Hence, only the latter three fields are usable for payload.
That metadata is the reference count that is stored in the first slot.
$ REFCOUNTOFFSET := #imm(0) $

The following figure illustrates the layout of memory blocks.
Here, `next` stands for the pointer to the next block of the free list and `rc` denotes the reference count for allocated blocks.
The reserved slots are marked in gray, the slots that can contain payload are highlighted in green.

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

Now, we will introduce the memory management primitives.

==== Share and Erase
Allocated blocks store reference counts.
If exactly one (co)variable references a block, the count is #imm(0).
Each additional reference increments it by one.

$SHAREBLOCK$ increments the reference count of a block by $n$ if $r$ contains a non-null memory pointer.
$
  SHAREBLOCK r sp n & := && BEQ r #reg(0) l \
                    &    && #hide[$l:$] LW TEMP REFCOUNTOFFSET r \
                    &    && #hide[$l:$] ADDI TEMP TEMP n \
                    &    && #hide[$l:$] SW TEMP REFCOUNTOFFSET sp r \
                    &    && l: \
$

$SHAREFIELDS$ applies #box[$SHAREBLOCK f sp 1$] to each child field pointer $f$ in a block.

Erasing is dual.
$ERASEBLOCK$ checks whether a memory block has a reference count of #imm(0):
if yes, it prepends the block to the lazy free list (but without erasing its children);
if not, it decrements the reference count.
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

$ERASEFIELDS$ applies #box[$ERASEBLOCK f$] to all child field pointers $f$.

==== Acquire
$ACQUIRE$ allocates a new memory block.
More precisely, it removes the first block from the linear free list, initializes its reference count to #imm(0), and stores a pointer to the block in the register $r$.
It then reestablishes the invariant that $HEAP$ always points to a block that can be allocated immediately.

In the best case, the linear free list contains another block
and $HEAP$ is simply updated to point to the next block in the list.

If the linear free list contains only a single block, $ACQUIRE$ attempts to restore the invariant by moving the first block of the lazy free list to the linear free list.
Before this block can be reused, its children must be erased by $ERASEFIELDS$.

Finally, if the lazy free list is also empty, a new block is obtained using bump allocation.

$
  ACQUIRE r & := && MV r HEAP \
            &    && LW HEAP NEXTBLOCKOFFSET HEAP \
            &    && BEQ HEAP #reg(0) l_1 \
            &    && #hide[$l_1:$] SW #reg(0) REFCOUNTOFFSET r \
            &    && #hide[$l_1:$] JUMP l_2 \
            &    && l_1: MV HEAP TODO \
            &    && #hide[$l_1:$] LW TODO NEXTBLOCKOFFSET TODO \
            &    && #hide[$l_1:$] BEQ TODO #reg(0) l_3 \
            &    && #hide[$l_1:$] #hide[$l_3:$] SW #reg(0) NEXTBLOCKOFFSET HEAP \
            &    && #hide[$l_1:$] #hide[$l_3:$] ERASEFIELDS HEAP \
            &    && #hide[$l_1:$] #hide[$l_3:$] JUMP l_2 \
            &    && #hide[$l_1:$] l_3: ADDI TODO HEAP #imm(32) \
            &    && l_2: \
$

==== Store
To store the bindings in $Gamma$ to memory, $STORE$ writes them from back to front to the first block of the linear free list
and then uses $ACQUIRE$ to move the block's pointer into a register.

$
            STORE r sp Gamma & := && STOREV r sp Gamma \
                             &    && ACQUIRE r \
  STOREV (Gamma, v:^chi tau) & := && SW (REG_2 sp v) sp (OFFSET_2 sp v) sp HEAP \
                             &    && SW (REG_1 sp v) sp (OFFSET_1 sp v) sp HEAP \
                             &    && STOREV r sp Gamma \
$

Here, $OFFSET_1 sp v$ and $OFFSET_2 sp v$ denote the offsets within a memory block that correspond to the first and second components of the (co)variable $v$, respectively.

If $Gamma$ contains more bindings than can fit into a single memory block, multiple blocks are chained together.
The details of this mechanism are not relevant to this thesis and are therefore omitted.

==== Release
$RELEASE$ is used to free a memory block that is loaded into registers.
If its reference count is #imm(0), the block is prepended to the linear free list.
Otherwise, it cannot be freed.
Instead, its reference count is decremented, and its children are shared, since the values loaded into the registers now hold additional references to them.

$
  RELEASE r & := && LW TEMP REFCOUNTOFFSET r \
            &    && BEQ TEMP #reg(0) l_1 \
            &    && #hide[$l_1:$] ADDI TEMP TEMP #imm(-1) \
            &    && #hide[$l_1:$] SW TEMP REFCOUNTOFFSET sp r \
            &    && #hide[$l_1:$] SHAREFIELDS r \
            &    && #hide[$l_1:$] JUMP l_2 \
            &    && l_1: SW HEAP NEXTBLOCKOFFSET sp r \
            &    && #hide[$l_1:$] MV HEAP r \
            &    && l_2: \
$

==== Load
To load values from memory into registers, $LOAD$ first releases the memory block and then copies it into the corresponding registers from back to front.
$
                 LOAD r sp Gamma & := && RELEASE r \
                                 &    && LOADV r sp Gamma \
  LOADV r sp (Gamma, v:^chi tau) & := && LW (REG_2 sp v) sp (OFFSET_2 sp v) sp r \
                                 &    && LW (REG_1 sp v) sp (OFFSET_1 sp v) sp r \
                                 &    && LOADV r sp Gamma \
$

=== Translating #AxCut to #RISC-V <sec:scc:codegen:a2m>
We now present $a2m(dot)$, the translation from #AxCut statements to #RISC-V instructions.

==== Programs, Top-Level Definitions, and Calls
An #AxCut program is a list of type declarations and top-level definitions.
Type declarations have no runtime behavior and are not translated.

Top-level definitions are translated by attaching labels to translated bodies.
$ a2m(DEF f(Gamma) br(s)) & := && f: a2m(s) $

A function call translates to a direct jump.
$ a2m(f(Gamma)) := JUMP f $

Argument handling is done beforehand via $SUBSTITUTE$.

==== Explicit Substitutions
$SUBSTITUTE$ prepares registers for the next statement.

If bindings are duplicated or dropped, heap reference counts must be updated accordingly.
For this, we introduce the following operations:
$
  SHARE [Gamma' := sigma] sp (Gamma, v :^chi tau) & := && METAIF NUMREFS v sp [Gamma' := sigma] > 1 \
  &&& quad SHAREBLOCK (REG_1 sp v) sp (NUMREFS v sp [Gamma' := sigma] - 1) \
  &&& SHARE [Gamma' := sigma] sp Gamma \
  ERASE [Gamma' := sigma] sp (Gamma, v :^chi tau) & := && METAIF NUMREFS v sp [Gamma' := sigma] = 0 \
  &&& quad ERASEBLOCK (REG_1 sp v) \
  &&& ERASE [Gamma' := sigma] sp Gamma \
$
Here, $NUMREFS v sp [Gamma' := sigma]$ denotes how many times $v$ is mentioned in the substitution.

Register reordering uses a parallel moves algorithm @Rideau2008parallelmoves, written as $MOVE$.

Together, these three operations --- sharing duplicated (co)variables, erasing dropped ones, and reordering registers --- form explicit substitution.

$
  a2m(SUBSTITUTE[Gamma' := sigma]\; sp s) & := && SHARE [Gamma' := sigma] \
                                          &    && ERASE [Gamma' := sigma] \
                                          &    && MOVE [Gamma' := sigma] \
                                          &    && a2m(s)
$

==== Machine Integers and Conditionals
Literals, arithmetic, and conditionals map directly to machine instructions.
$
  a2m(LIT v <- n\; sp s) & := && LI (REG_2 sp v) sp n \
  & && a2m(s) \
  a2m(v <- v_1 + v_2\; sp s) & := && ADD (REG_2 sp v) sp (REG_2 sp v_1) sp (REG_2 sp v_2) \
  & && a2m(s) \
  a2m(IF v equiv 0 br(s_1) ELSE br(s_2)) & := && BEQ (REG_2 sp v) #reg(0) l \
  & && #hide[$l:$] a2m(s_2) \
  & && l: a2m(s_1) \
$

==== Let-Bindings and Pattern Matches
$LET$ binds a constructor/destructor to a variable.
Code generation stores fields in memory via $STORE$, then creates a two-register (co)variable:
pointer in the first component, tag index in the second.
$
  a2m(LET v = X(Gamma_0)\; s) & := && STORE (REG_1 sp v) sp Gamma_0 \
                              &    && LI (REG_2 sp v) sp (INDEX X) \
                              &    && a2m(s)
$
$INDEX X$ is the jump-table byte offset of tag $X$ (constructor/destructor position multiplied by four).

$LET$-bound (co)variables in #AxCut are consumed by pattern matches using the $SWITCH$ statement.
The translation function turns it into an indirect jump into a generated jump table.
$
  a2m(SWITCH v sp b) & := && JR (REG_2 sp v) sp l \
                     &    && l: JTABLE b sp Gamma \
$

Jump tables are defined as follows.
$
  JTABLE br(overline(X_i (Gamma_i) => s_i)) sp Gamma & := && overline(JUMP l_i) \
  &&& JTABLEB br(overline(X_i (Gamma_i) => s_i)) sp Gamma sp overline(l_i) \
  JTABLEB br(X_1(Gamma_1) => s_1, b) sp Gamma sp \(l_1, overline(l)\) & := && l_1: LOAD (REG_1 sp x) sp Gamma_1 #h(4em) && (x "fresh after" Gamma) \
  &&& #hide[$l_1:$] a2m(s_1) \
  &&& JTABLEB b sp Gamma sp overline(l)
$

The tag selects the entry of the jump table; each entry reloads the fields from memory and continues with the translation of the branch code.

==== Objects and Invocations
$CREATE$ allocates a closure object.
It stores the captured environment in memory and generates a virtual table.
The pointer to the environment is stored in the first component of the created (co)variable,
and the instruction pointer to the virtual table in the second.

$
  a2m(CREATE v = Gamma_0 sp b\; sp s) & := && STORE (REG_1 sp v) sp Gamma_0 \
                                      &    && LA (REG_2 sp v) sp l \
                                      &    && a2m(s) \
                                      &    && l: VTABLE b sp Gamma_0 \
$

Virtual tables are defined as follows.

$
  VTABLE br(overline(X_i (Gamma_i) => s_i)) sp Gamma_0 & := && overline(JUMP l_i) \
  &&& VTABLEB br(overline(X_i (Gamma_i) => s_i)) sp Gamma_0 sp overline(l_i) \
  VTABLEB br(X_1(Gamma_1) => s_1, b) sp Gamma sp \(l_1, overline(l)\) & := && l_1: LOAD (REG_1 sp x) sp Gamma_0 #h(4em) && (x "fresh after" Gamma_1) \
  &&& #hide[$l_1:$] a2m(s_1) \
  &&& VTABLEB b sp Gamma_0 sp overline(l)
$

A (co)variable that was introduced by $CREATE$ is consumed by $INVOKE$.
In machine code, that is an indirect jump into the virtual table.
$
  a2m(INVOKE v sp X(Gamma)) & := && JR (REG_2 sp v) sp (INDEX X) \
$

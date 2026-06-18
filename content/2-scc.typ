#import "/lib/lib.typ": *
#import deps.fletcher

= The Sequent Calculus Compiler
This chapter provides a brief summary of the Sequent Calculus Compiler (SCC) pipeline @Mueller2026
since it is foundational for the later chapters that will modify and extend it.

== Overview
The SCC takes a functional programming language, called #Fun, as surface language and compiles it to native machine code.
The concrete target architecture is not very relevant here and can easily be adapted.
In the implementation @Mueller2026scc, multiple backend architectures are supported but for the sake of simplicity we only consider #RISC-V in this thesis.

The interesting parts of the compiler are the intermediate representations, #Core and #AxCut, which are based on the sequent calculus and thus form the heart of the SCC.

Here is an illustration of the complete SCC compilation pipeline,
where each box represents a compiler stage and the arrows represent the translations between them:

#figure({
  import fletcher: diagram, edge, node

  let colored-node(color) = node.with(stroke: color, fill: color.lighten(65%))

  let fun = (0, 0)
  let core = (2, 0)
  let axcut = (4, 0)
  let riscv = (6, 0)

  show ref: set text(size: settings.font-size-normal - 3pt)

  diagram(
    debug: false,
    node-stroke: 1pt,
    label-sep: 0.2em,
    colored-node(red)(fun, [#Fun \ @scc:fun]),
    colored-node(green)(core, [#Core \ @scc:core]),
    colored-node(blue)(axcut, [#AxCut \ @scc:axcut]),
    colored-node(orange)(riscv, [#RISC-V \ @scc:codegen]),
    edge(fun, core, "-|>", label: $f2c(dot)$, label-side: left),
    edge(fun, core, "-|>", label: [@scc:f2c], label-side: right, stroke: none),
    edge(core, axcut, "-|>", label: $c2a(dot)$, label-side: left),
    edge(
      core,
      axcut,
      "-|>",
      label: [@scc:c2a],
      label-side: right,
      stroke: none,
    ),
    edge(axcut, riscv, "-|>", label: $a2m(dot)$, label-side: left),
    edge(
      axcut,
      riscv,
      "-|>",
      label: [@scc:codegen],
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
        #set par(leading: 0pt)

        $focus(dot), shrink(dot)$ \
        @scc:focus, @scc:shrink
      ],
    ),
  )
})

The following sections will explain every stage and translation step-by-step.

== The Surface Language #Fun <scc:fun>
Every compiler needs a surface language: the language in which its input programs are written, typically by a human.
In the case of the SCC, this language is called #Fun @Binder2024grokking.
It is designed as an expression-oriented, functional programming language, extended with some advanced features to showcase the power of the compiler pipeline.
#Fun is not intended as a production-ready programming language, but rather as vehicle for demonstrating what the SCC can handle and how it operates.

=== Syntax
#definition(title: "Naming Conventions")[
  The rest of this thesis uses the following naming conventions:
  - $x,y,...$ are _variable names_,
  - $alpha, beta, ...$ are _covariable names_,
  - $T$ is some user-defined _type name_,
  - $K,D,X$ are _tags_ used for constructors and destructors,
  - and $f$ is a _label_ used for top-level definitions.
]

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
]

#Fun supports standard features such as top-level (first-order) functions, variables, simple arithmetic and conditional expressions, and (non-recursive) let-bindings.

Additionally, there are user-definable algebraic data and codata types.
Algebraic data types are a familiar concept from many popular statically-typed functional programming languages.
They are defined by their constructors $K(sigma)$, which produce elements of the data type, and are consumed by pattern matching ($CASE$).
Dually, the less common algebraic codata types @Hagino1989 @Downen2019codata are defined by their destructors $D(sigma)$, which consume elements of the codata type, and are produced by copattern matching ($NEW$) @Abel2013copattern.
They are very similar to interfaces in object-oriented programming.

Another very interesting feature, especially with regard to the contents of this thesis, are the control operators $LABEL$ and $GOTO$.
They work in a similar fashion to `let/cc` @Reynolds1972letcc, known from the LISP family of programming languages. $LABEL$ captures the current computation context --- the so-called _continuation_ --- and binds it to a covariable.
With $GOTO$ such a computation context can be invoked, resulting in non-local control flow.

#inline-note[This could go further...]

=== Typing Rules
The typing rules for #Fun are shown in @fig:scc:fun:typing.
To keep the presentation concise, well-formedness rules for programs and declarations are omitted.
We assume that all types and names that are used in the program are well-defined and unique.

There are three judgment forms for producers, consumers, and argument lists, respectively.
The judgment $Theta mid Gamma tack p : tau$ means that under the global context $Theta$, which keeps track of top-level declarations,
and the local context $Gamma$, which keeps track of currently active (co)variable bindings, the term $p$ has the type $tau$.
Similarly, $Theta mid Gamma tack c :^cns tau$ denotes that $c$ is a well-typed consumer for $tau$.
The judgment $Theta mid Gamma tack sigma : Gamma'$ means that the arguments list $sigma$ matches the parameter list $Gamma'$.
In many rules, the global context $Theta$ is not referenced.
If that is the case, it is omitted to improve readability.

#figure(
  kind: "Figure",
  supplement: "Figure",
  caption: [Typing rules for #Fun.],
)[
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
    column-gutter: 2em,
    prooftree(rule(
      name: rn($#smallcaps("Arg") _1$),
      $Gamma tack empty : empty$,
    )),
    prooftree(rule(
      name: rn($#smallcaps("Arg") _2$),
      $Gamma tack sigma : Gamma'$,
      $Gamma tack p : tau$,
      $Gamma tack (sigma,p) : (Gamma', sp x:tau)$,
    )),
    prooftree(rule(
      name: rn($#smallcaps("Arg") _3$),
      $Gamma tack sigma : Gamma'$,
      $Gamma tack c :^cns tau$,
      $Gamma tack (sigma,c) : (Gamma', sp alpha:^cns tau)$,
    )),
  )
] <fig:scc:fun:typing>

Most of the rules are standard.
Interesting are the control operators.
In #rn("Label"), a covariable $alpha$ is added to the context when typing the body of the expression.
If there is a covariable in the current context, #rn("Goto") can be used to invoke it. Here, the argument must be of the same type as the consumer covariable. The expression as a whole, however, is allowed to have any type $tau'$ because the computation will not continue here.
Similarly in the rule #rn("Exit"), the expression's type is arbitrary because, again, the computation will not continue.

== The High-Level Intermediate Language #Core <scc:core>
The next step of the compilation pipeline is the intermediate representation #Core.
It is an extension of the $lambda mu tilde(mu)$-calculus @Curien2000, a term assignment system for classical sequent calculus @Gentzen1935a,
equipped with integer arithmetic, top-level function definitions, and algebraic data and codata types. The translation from #Fun to #Core is covered in @scc:f2c.

=== Syntax
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
]

In sequent-calculus-based languages, like #Core, we distinguish three different syntactic categories: producers, consumers and statements.
Producers represent the data of a program, similar to regular terms.
Consumers are a first-class representation of evaluation contexts.
In contrast to #Fun, pattern matches and destructor invocations in #Core are separated from the value they act on, and appear as self-contained consumers.
Computation happens in the third syntactic category of statements.
Most importantly, in a _cut_ $cut(p, c)$ a producer and a consumer interact.
The $mu$ and $tilde(mu)$ operators are used to abstract producers and consumers.
#note[Awkward paragraph. Rephrase..]

Note that top-level functions and codata destructors no longer specify a return type. Instead, an additional consumer argument, the _continuation_, takes its place.
#note[More on that later...]

Special about the sequent-calculus-based representation is the symmetry of producers and consumers.
In the typing environments, which also serve as parameter lists, both variables and covariables are tracked.
Hence, each binding is annotated with its _chirality_, i.e. whether it is a producer or consumer.
Also, since destructors no longer have a return type, the definition of data and codata types is perfectly symmetric.

=== Typing Rules
@fig:scc:core:typing shows the typing rules for #Core.
Again, the well-formedness of declarations is assumed implicitly, and the global context $Theta$ is omitted where possible.

For every syntactic category, there is a typing judgment form: $Theta mid Gamma tack p :^prd tau$ means that $p$ is a producer of type $tau$ in the context $Gamma$.
Analogously for $Theta mid Gamma tack c :^cns tau$ is $c$ a consumer of type $tau$.
And $Theta mid Gamma tack s$ means that $s$ is a well-typed statement.
Since statements represent computation, they do not have a return type.

#figure(
  kind: "Figure",
  supplement: "Figure",
  caption: [Typing rules for #Core.],
)[
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
] <fig:scc:core:typing>

#inline-note[Explain rules. Symmetry. Etc.]

== Translation from #Fun to #Core <scc:f2c>
#figure(
  kind: "Figure",
  supplement: "Figure",
  caption: [Translation from #Fun to #Core.],
)[
  #set math.lr(size: 1em)

  #def-box[$f2c(dot) : "Declaration"_Fun -> "Declaration"_Core$]
  $
    f2c(DEF f(Gamma) : i64 br(p)) & := DEF f(Gamma, alpha :^cns tau) br(f2c(p, with: alpha)) quad(alpha "fresh") \
    f2c(DEF "main"(Gamma) : i64 br(p)) & := DEF "main"(Gamma) br(f2c(p, with: tilde(mu)x.EXIT x)) \
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
      #note[bindvals not yet defined]
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
]

== The Focusing Transformation <scc:focus>

#figure(
  kind: "Figure",
  supplement: "Figure",
  caption: [The binding functions used for the focusing transformation.],
)[
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
]

#figure(
  kind: "Figure",
  supplement: "Figure",
  caption: [The focusing transformation.],
)[
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
]

== The Shrinking Transformation <scc:shrink>

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

== The Lower-Level Intermediate Language #AxCut <scc:axcut>

=== Syntax
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
  )
]

=== Typing Rules
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

#figure[
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
]

== Translation from #Core to #AxCut <scc:c2a>
#inline-note[Improve formatting.]
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
    &&& CREATE x = Gamma_0 br(K_1(Gamma_1) => c2a(s_1, ctx: Gamma_1\, Gamma_0), ...); \
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

== Code Generation <scc:codegen>

=== The Target Language #RISC-V
We use the following subset of #RISC-V @Waterman2014riscv as target for the code generation.

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
]

=== Overview
#inline-note[
  - Definitions are Labels, Calls are Direct Jumps
  - Explicit Substitutions are Parallel Moves
  - Externs are System Calls and Hardware Instructions
  - Constructors are Tags, Fields are Memory Blocks, Pattern Matches are Jump Tables
  - Objects are Virtual Tables, Closures are Memory Blocks, Destructor Invocations are Indirect Jumps
  - $LET$ and $CREATE$ acquire memory, $SWITCH$ and $INVOKE$ release memory
  - Constant-time lazy reference counting @Lam2024
  - Share increases refcount, erase decreases refcount
]

=== Translation from #AxCut to #RISC-V
#definition(title: "Auxiliary Definitions")[
  - $REG_1 sp v$ is the first register of a variable $v$.
  - $REG_2 sp v$ is the second register of a variable $v$.
  - $INDEX X$ is the index of the constructor/destructor $X$ in its signature, multiplied by four.
  - $OFFSET_1 sp v$ is the first memory offset for $v$ in the environment.
  - $OFFSET_2 sp v$ is the second memory offset for $v$ in the environment.
  - #todo[$MOVE [Gamma' := sigma]$ is ...]
  - #todo[...]
  - $TEMP$ is a reserved register for temporaries.
  - $TODO$ is a reserved register for the lazy free list.
  - $HEAP$ is a reserved register for the linear free list.
]

#figure(
  kind: "Figure",
  supplement: "Figure",
  caption: [Translation from #AxCut to #RISC-V.],
)[
  #set math.lr(size: 1em)

  #def-box[$a2m(dot) : "Definition"_AxCut -> I^*$]
  $
    a2m(DEF f(Gamma) br(s)) & := && f: a2m(s)
  $

  #def-box[$a2m(dot) : "Statement"_AxCut -> I^*$]
  $
    a2m(f(Gamma)) & := && JUMP f \
    a2m(SUBSTITUTE[Gamma' := sigma]\; sp s) & := && SHARE [Gamma' := sigma] \
    & && ERASE [Gamma' := sigma] \
    & && MOVE [Gamma' := sigma] \
    & && a2m(s) \
    a2m(EXIT v) & := && LI #reg(17) #imm(93) \
    & && MV #reg(10) (REG_2 sp v) \
    & && ECALL \
    a2m(LIT v <- n\; sp s) & := && LI (REG_2 sp v) sp n \
    & && a2m(s) \
    a2m(v <- v_1 + v_2\; sp s) & := && ADD (REG_2 sp v) sp (REG_2 v_1) sp (REG_2 sp v_2) \
    & && a2m(s) \
    a2m(IF v equiv 0 br(s_1) ELSE br(s_2)) & := && BEQ (REG_2 sp v) #reg(0) l \
    & && #hide[$l:$] a2m(s_2) \
    & && l: a2m(s_1) \
    a2m(LET v = X(Gamma_0)\; s) & := && STORE (REG_1 sp v) sp Gamma_0 \
    & && LI (REG_2 sp v) sp (INDEX X) \
    & && a2m(s) \
    a2m(CREATE v = Gamma_0 sp b\; s) & := && STORE (REG_1 sp v) sp Gamma_0 \
    & && LA (REG_2 sp v) sp l \
    & && a2m(s) \
    & && l: VTABLE b sp Gamma_0 \
    a2m(SWITCH v sp b) & := && JR (REG_2 sp v) sp l \
    & && l: JTABLE b sp Gamma \
    a2m(INVOKE v sp X(Gamma)) & := && JR (REG_2 sp v) sp (INDEX X) \
  $
]

=== Share & Erase
#inline-note[
  I think this can be skipped or moved to an appendix.
]

=== Virtual Tables & Jump Tables
#todo[TODO]

=== Memory Management
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

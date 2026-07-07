#import "/lib/lib.typ": *

= Introduction <ch:intro>
Compilers translate high-level programming languages into executable machine code
through a sequence of intermediate representations and transformations.
The choice of these intermediate representations is a central design decision in compiler construction:
they should be expressive enough for analysis and optimizations, while being suitable for generating efficient low-level machine code.

For functional programming languages in particular, compiler intermediate representations are usually based on the $lambda$-calculus which corresponds to the natural deduction proof system by Gentzen @Gentzen1935a[ sec. II].
More recently, however, Gentzen's sequent calculus @Gentzen1935a[ sec. III], or specifically its corresponding term assignment system, the $lambda mu tilde(mu)$-calculus @Curien2000, has been found to offer a compelling alternative basis for compiler design @Binder2024grokking @Downen2016sequent @Schuster2025 @Mueller2026.
In sequent-calculus-based intermediate representations, control flow and its duality to data flow are made explicit,
which is especially suitable for compilers that handle advanced control operators and complex control-flow behavior.

The _Sequent Calculus Compiler (SCC)_ @Mueller2026 @Mueller2026scc follows this approach.
It compiles a functional programming language to native machine code through the usage of sequent-calculus-based intermediate representations.
A key design feature of the SCC is that control flow is made explicit with first-class _consumers_
which represent _continuations_ of computation.

Consider this simple term, where a function $f$ is called and then $1$ is added to the result.
$ f(x) + 1 $
The remaining computation after the call to $f$ --- namely "add 1 to the result" --- is the continuation of $f$.
In the SCC, such computation contexts are made explicit with consumers that can be named, passed around, duplicated, and dropped.

This provides an expressive and uniform representation of computation
that can encode complex control effects (e.g. early returns, exceptions, asynchronous code).
However, this expressiveness comes at a cost because the runtime system must support the generalized control flow behavior.

This thesis is motivated by the observation that in many programs control flow is simple and continuations are _linear_, i.e. each continuation is used exactly once.
In such cases, the additional runtime overhead that is needed to track complex continuation usage is unnecessary.
If the compiler can statically prove that all continuations are linear, then it is possible to generate more efficient machine code for these cases.

Concretely, we investigate linear continuations in the SCC and how they can be exploited for code generation.
The central idea is to provide the low-level stages of the compilation pipeline with additional information about the linearity of continuations and use this information to optimize the memory layout and avoid unnecessary memory management operations at runtime.

We implement the optimization as an extension to the existing SCC implementation @Mueller2026scc,
modifying the low-level code generation stages for programs with only linear continuations.
#footnote[
  The implementation is available at #link("https://github.com/SequentCalculus/sequent-calculus-compiler"),
  commit #link("https://github.com/SequentCalculus/sequent-calculus-compiler/commit/083e60c28817ee421341fe91534ad213030c85d9")[`083e60c28817ee421341fe91534ad213030c85d9`].
]

The remainder of this thesis is organized as follows:

- In @ch:scc, we summarize the SCC pipeline that is the foundation of the thesis.
  We introduce all relevant compiler stages and the translations between them.

- In @ch:lin, we analyze how continuations are used to represent control flow in the SCC
  and formalize how to statically retain information about linear continuations.

- In @ch:codegen, we present the code generation modifications that exploit the linearity of continuations,
  which include changes to the memory layout and runtime memory management operations.

- In @ch:eval, we evaluate our approach with benchmarks and discuss the resulting performance improvements.

- To conclude, in @ch:conclusion we summarize the results of this thesis and give directions on future work.

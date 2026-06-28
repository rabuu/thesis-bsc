#import "/lib/lib.typ": *

= Introduction <ch:intro>
Compilers translate high-level programming languages into executable machine code
through a sequence of intermediate representations and transformations.
One of the main challenges in compiler design is finding the right intermediate representations that are expressive enough for analysis and optimization and are suitable for generating efficient low-level machine code.

For functional programming languages in particular, the design of such intermediate representations is usually based on the $lambda$-calculus and, closely related, Gentzen's natural deduction @Gentzen1935a[ section II].
In recent times, however, the sequent calculus @Gentzen1935a[ section III], another logical proof system like natural deduction by Gentzen, or specifically its corresponding term assignment system, the $lambda mu tilde(mu)$-calculus @Curien2000, has been found to offer a compelling alternative as basis for compiler design @Binder2024grokking @Downen2016sequent @Schuster2025 @Mueller2026.
A main selling point for sequent-calculus-based intermediate representations is that it makes control flow and its duality to data flow very explicit.
The treatment of computation contexts as first-class concept is especially suitable for compilers that have to handle advanced control operators and complex control flow.

The _Sequent Calculus Compiler (SCC)_ @Mueller2026 @Mueller2026scc follows this approach.
It compiles a functional programming language to native machine code through the usage of sequent-calculus-based intermediate representations.
A key design feature of the SCC is that control flow is made explicit with first-class _consumers_
which correspond to the computation contexts, or _continuations_, of programs.
This provides a very expressive and uniform representation of computation, even for complex control flow.
However, this expressiveness comes at a cost
because the runtime system must support the very generalized control flow behavior.

This thesis is motivated by the observation that in many programs control flow is simple because continuations are used _linearly_, i.e. each continuation is used exactly once.
In such cases, the additional runtime overhead that is needed to track complex continuation usage is unnecessary.
If the compiler can statically prove that continuations are linear, then it is possible to generate optimized machine code that is specialized for these cases.

Concretely, this thesis investigates linear continuations in the SCC and how they can be exploited for generating more efficient machine code.
The central idea is to provide the low-level stages of the compilation pipeline with additional information about the linearity of continuations and use this information for improved memory management in the resulting machine code.

The remainder of this thesis is organized as follows:

In @ch:scc, we summarize the SCC pipeline that is the foundation of the thesis.
It introduces all compiler stages and the translations between them.

In @ch:lin, we analyze how continuations are used to represent control flow in the SCC
and formalize how to statically retain information about linear continuations.

In @ch:codegen, we present the code generation modifications that exploit the linearity of continuations, which include changes to the memory layout and runtime memory management operations.

In @ch:eval, we evaluate the approach of the thesis by providing benchmarks and discussing the gained performance and memory usage improvements.

In @ch:conclusion, we conclude by summarizing the contributions of this thesis and giving directions on future work.

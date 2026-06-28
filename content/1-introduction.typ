#import "/lib/lib.typ": *

= Introduction <ch:intro>
Compilation is a complex process in which the source code of a high-level programming languages undergoes multiple transformations to finally result in executable machine code.
Finding the right intermediate representations is one of the main challenges when designing compilers.
On the one hand, they must be expressive enough to be useful for code analysis and optimization.
On the other hand, they need to bridge the gap between high-level and lower-level abstraction stages so that they can ultimately be translated to machine code.
For functional programming languages in particular, the design of such intermediate representations is usually based on the $lambda$-calculus which can be viewed as term assignment system of Gentzen's calculus of natural deduction @Gentzen1935a.

In recent times, however, an alternative foundation for the design of intermediate representations has been proposed: the sequent calculus @Gentzen1935a,
which is another logical proof system like natural deduction, also invented by Gentzen.
Classical sequent calculus or specifically its corresponding term assignment system, the $lambda mu tilde(mu)$-calculus @Curien2000, has been found to offer a compelling basis for compiler intermediate representations @Binder2024grokking @Downen2016sequent @Schuster2025 @Mueller2026.
Its symmetric treatment of both data and control flow as first-class concepts makes it especially suitable for encoding complex control operations.

This thesis builds upon one such compilation pipeline with intermediate representations based on the sequent calculus, the _Sequent Calculus Compiler (SCC)_ @Mueller2026 @Mueller2026scc.

#todo[
  TODO:
  The main part of the introduction is missing yet.

  Examples are important.
]

@ch:scc gives a summary of the SCC pipeline that is the foundation of the thesis.
It introduces all compiler stages and the translations between them.

In @ch:lin, the optimization is motivated, presented and formalized.
Here, the original compiler pipeline is modified by restricting it to a certain class of programs where the optimization is applicable.
This enables improving the generated machine code in many cases.

The low-level implementation of the optimization is presented in @ch:codegen.
It describes how code generation can be improved for linear continuations.

@ch:eval evaluates the results of the thesis by presenting benchmarks that show the improvements in terms of performance, memory usage and code size which are achieved by applying the optimization.

In @ch:conclusion, we conclude by summarizing the contributions of this thesis and presenting what can be done in future work.

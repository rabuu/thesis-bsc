#import "/lib/lib.typ": *

= Introduction <ch:intro>
Compilation is a complex process in which the source code of a high-level programming languages undergoes multiple transformations to finally result in executable machine code.
Finding the right intermediate representations is one of the main challenges when designing compilers.
On the one hand, they must be expressive enough to be useful for code analysis and optimization.
On the other hand, they need to bridge the gap between high-level and lower-level abstraction stages so that they can ultimately be translated to machine code.
For functional programming languages in particular, the design of such intermediate representations is usually based on the $lambda$-calculus which is --- through the lens of the Curry-Howard correspondence --- a term assignment system of natural deduction.

In recent times, however, an alternative foundation for the design of intermediate representations has been proposed: the sequent calculus.
The sequent calculus --- another logical proof system like natural deduction --- or specifically its correspondent term assignment system, the $lambda mu tilde(mu)$-calculus, has been found to offer a compelling basis for compiler intermediate representations.
Its symmetric treatment of both data and control flow as first-class concepts makes it especially suitable for encoding complex control operations.

One such compilation pipeline that bases its intermediate representations on the sequent calculus,
is described by #todo(cite(<Binder2024grokking>, form: "prose")).
#todo[And so on...]

#todo[Many things more...]

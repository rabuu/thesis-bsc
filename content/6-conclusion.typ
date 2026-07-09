#import "/lib/lib.typ": *

= Conclusion <ch:conclusion>

== Summary
In this thesis, we presented an optimization for the Sequent Calculus Compiler that exploits linear continuations to improve code generation.
We showed that the SCC represents local control flow as continuations that are used linearly,
which enables a more efficient memory representation and management strategy.

To make this optimization possible, we restricted the surface language #Fun by excluding control operators,
and identified the corresponding fragment of #Core in which all continuations are linear.
We extended #AxCut with linearity annotations to preserve this information.
Based on these annotations, we adapted code generation to distinguish between linear and unrestricted memory,
allowing linear continuations to use a more efficient memory layout and eliminating unnecessary reference counting operations.

We implemented the optimization and evaluated it on 30 benchmark programs.
The results show reductions in execution time for programs restricted to local control flow,
with substantial speedups for programs involving frequent function calls.

== Future Work
Although this thesis applies the extensions to #AxCut and code generation only to linear continuations, they are not specific to continuations.
The backend is already suited to generating more efficient code for arbitrary linear data, including producers.
However, to make full use of this, the compiler requires more static information about linearity than #Fun and #Core currently provide.
One way to obtain more information would be to design more elaborate linear type systems for #Fun and #Core.
An alternative, requiring no changes to the compiler frontend, would be to add a linearity detection pass to #AxCut that identifies exactly
which bindings are used linearly by tracking whether they are duplicated or dropped.

Since the optimization is currently implemented and evaluated only for the x86-64 backend, an obvious next step is to extend it to the other backends (#RISC-V and AArch64).
The evaluation could likewise be extended to a broader range of programs, and with further metrics, such as code size and memory usage.

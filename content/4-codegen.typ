#import "/lib/lib.typ": *

= Optimizing Code Generation
#inline-note[Chapter Introduction...]

== The Key Observation
A memory block that is allocated for linear use is statically known to be consumed exactly once.
The key observation here is that such a memory block will neither be shared nor erased.
#AxCut makes that very explicit with its $SUBSTITUTE$ statements:
a variable introduced by $LET_1$ or $CREATE_1$ is contained in every substitution exactly once, until it is consumed by its corresponding $SWITCH_1$ or $INVOKE$ statement, respectively.
And therefore, the reference count of a linearly allocated memory block is zero and will never change.

The central idea behind the optimization we are going for is obvious:
since the reference count is not used anyway, it can just be left out.
This not only increases the memory space we can use for actual data, but also reduces code size and runtime overhead that is needed for creating and checking the reference count.

== The Naïve Approach
#inline-note[Just remove the reference count, duh.]

=== ...and Where it Fails
#inline-note[Double meaning of first slot: next-block pointer and register where the memory pointer should end up.]

== Changing the Memory Layout
#inline-note[Move next-block offset, and reference count, from 0 to 1.]

== Linear Memory Management
#inline-note[$STORE_1$, $LOAD_1$, $ACQUIRE_1$, $RELEASE_1$]

== Translation from #AxCut to #RISC-V
#figure[
  #set math.lr(size: 1em)

  #def-box[$a2m(dot) : "Statement"_AxCut -> I^*$]
  $
    a2m(mark(LET_q) sp v = X(Gamma_0)\; s) & := && mark(STORE_q) sp (REG_1 sp v) sp Gamma_0 \
    & && LI (REG_2 sp v) sp (INDEX X) \
    & && a2m(s) \
    a2m(mark(CREATE_q) sp v = Gamma_0 sp b\; s) & := && mark(STORE_q) sp (REG_1 sp v) sp Gamma_0 \
    & && LA (REG_2 sp v) sp l \
    & && a2m(s) \
    & && l: mark(VTABLE_q) sp b sp Gamma_0 \
    a2m(mark(SWITCH_q) sp v sp b) & := && JR (REG_2 sp v) sp l \
    & && l: mark(JTABLE_q) sp b sp Gamma \
    a2m(INVOKE v sp X(Gamma)) & := && JR (REG_2 sp v) sp (INDEX X) \
  $
]

#inline-note[$VTABLE$ and $JTABLE$ are missing.]

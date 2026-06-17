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

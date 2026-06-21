#import "/lib/lib.typ": *
#import deps: cetz

= Optimizing Code Generation <ch:codegen>
#inline-note[Chapter Introduction...]

== The Key Observation
A memory block that is allocated for linear use is statically known to be consumed exactly once.
The key observation here is that such a memory block will neither be shared nor erased.
#AxCut makes that very explicit with its $SUBSTITUTE$ statements:
a variable introduced by $LET_1$ or $CREATE_1$ is contained in every substitution exactly once, until it is consumed by its corresponding $SWITCH_1$ or $INVOKE$ statement, respectively.
And therefore, the reference count of a linearly allocated memory block is zero and will never change.

The central idea behind the optimization we are going for is obvious:
since the reference count is not used anyway, it can just be left out.
This not only increases the memory space we can use for actual data, but also reduces code size and runtime overhead that is needed for maintaining the reference count.

== The Naïve Approach and Where it Fails
The first approach is to simply extend the memory operations $STORE$ and $LOAD$ to make use of all four fields.
But there is an issue.

Consider the following case where we want to store the registers from $Gamma_0$ to a new memory block, using every slot.
The naïve way would be to store all slots, from back to front, into the memory block and then call $ACQUIRE$.
In the following illustration, the latter seven slots are already stored.
A problem arises for the very first register ($a_1$ in the example).

#figure(cetz.canvas({
  import cetz.draw: *
  import diagram: *

  scale(0.8)

  let regy = 4

  content((0, regy - 0.5), [Registers])
  slots(
    15,
    labels: (none, reg("temp"), reg("heap"), reg("todo"), none),
    data: (0, none, none, none, ddd, ddd)
      + (data($a_1$),)
      + range(2, 9).map(i => data($a_#i$, active: false))
      + (ddd,),
    offset: (2, regy),
    open-right: true,
  )

  brace(1, offset: (7, regy), label: $Gamma$)
  brace(8, offset: (8, regy), label: $Gamma_0$)

  let memy1 = 2
  let memy2 = 0
  content((0, memy1 - 0.5), [Memory])
  memblock(
    offset: (5, memy1),
    data: (none,) + range(2, 9).map(i => data($a_#i$)),
  )
  memblock(offset: (5, memy2))

  ptr(
    (4.5, regy - 0.6),
    (4.5, memy1 - 0.5),
    (5, memy1 - 0.5),
  )

  ptr(
    (5.5, memy1 - 0.6),
    (5.5, memy2),
  )
}))

As soon as $a_1$ is written to the first slot of the memory block, the pointer to the next memory block is lost.
But we cannot $ACQUIRE$ the block either because that would put a pointer to the memory block into the first register after $Gamma$,
which would overwrite $a_1$.

And there is a completely symmetric problem when loading data from memory block.
In the following illustration we want to load all eight slots of a memory block into registers.
Naïvely, we would $RELEASE$ the block, and then load the slots from back to front.

#figure(cetz.canvas({
  import cetz.draw: *
  import diagram: *

  scale(0.8)

  let regy = 4

  content((0, regy - 0.5), [Registers])
  slots(
    15,
    labels: (none, reg("temp"), reg("heap"), reg("todo"), none),
    data: (0, none, none, none, ddd, ddd) + (none,) * 8 + (ddd,),
    offset: (2, regy),
    open-right: true,
  )

  brace(1, offset: (7, regy), label: $Gamma$)
  brace(2, offset: (8, regy), label: $v$)

  let memy1 = 2
  let memy2 = 0
  content((0, memy1 - 0.5), [Memory])
  memblock(
    offset: (5, memy1),
    data: range(1, 9).map(i => data($a_#i$)),
  )
  memblock(offset: (5, memy2))

  ptr(
    (4.5, regy - 0.6),
    (4.5, memy2 - 0.5),
    (5, memy2 - 0.5),
  )

  ptr(
    (8.5, regy - 0.6),
    (8.5, regy - 1.5),
    (5.5, regy - 1.5),
    (5.5, memy1),
  )
}))

$RELEASE$ puts the pointer to the next block of the free list into the first slot, overwriting $a_1$.
So it must be called at least after loading $a_1$.
But at the same time, loading $a_1$ into the first register after $Gamma$ overwrites the pointer to the memory block, which is needed for the rest of the loads and for $RELEASE$.

In both cases the deadlock results from the double meaning of the first slot.
In the current layout #note[reference], it is the slot where the pointer to the next block of the free list is stored.
But it also corresponds to the register with the memory pointer to the block itself.

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

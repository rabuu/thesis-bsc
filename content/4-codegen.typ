#import "/lib/lib.typ": *
#import deps: cetz

= Optimizing Code Generation <ch:codegen>
This chapter turns the linearity information from @ch:lin into concrete backend optimizations.
The guiding idea is straightforward:
if a memory block is statically known to be used linearly, then runtime machinery for sharing that block is unnecessary.
In SCC, this machinery is reference counting.
By exploiting linearity annotations from extended #AxCut, we derive specialized memory operations for linear blocks and integrate them into the translation to #RISC-V.

== The Key Observation
A memory block allocated for linear use is statically known to be consumed exactly once.
Such a block is neither shared nor dropped before consumption.

In #AxCut, this is reflected in the typing of substitutions:
a (co)variable introduced by $LET_1$ or $CREATE_1$ must occur exactly once in each relevant $SUBSTITUTE$ statement
and is ultimately consumed by the corresponding $SWITCH_1$ or $INVOKE$.
Reference counts are modified only by $SHARE$ and $ERASE$, and these operations have an effect only when a (co)variable pointing to the block is duplicated or dropped in a $SUBSTITUTE$ statement.
Hence, the effective reference count of a linearly allocated block is always zero and never changes.

The optimization follows directly:
if the reference count is never inspected or updated, we can omit it entirely in the linear case.
This increases the payload capacity per block and removes instruction overhead for reference-count maintenance.

== The Naïve Approach and Where it Fails <sec:codegen:naive>
A natural first attempt is to keep the original memory layout and simply let $STORE$ and $LOAD$ use all four fields for payload in linear blocks.
However, this leads to an ordering conflict.

Consider storing the registers from $Gamma_0$ into a fresh block while using all four fields.
A naïve strategy is to store from back to front and then call $ACQUIRE$, just like in @sec:scc:codegen:mem.
In the situation below, seven slots are already written.
The conflict arises at the first register ($a_1$).

#figure(cetz.canvas({
  import cetz.draw: *
  import diagram: *

  scale(0.8)

  let regy = 4

  content((0, regy - 0.5), [Registers])
  slots(
    15,
    labels: (none, reg("temp"), reg("heap"), reg("todo"), none),
    data: (imm(0), none, none, none, ddd, ddd)
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

As soon as $a_1$ is written into the first slot, the pointer to the next block is lost.
But calling $ACQUIRE$ earlier is also impossible:
it would place a pointer into the first register after $Gamma$, overwriting $a_1$ before it is stored.

A completely symmetric issue appears for loading.
Suppose we want to load all eight payload slots into registers.
Naïvely, we would call $RELEASE$ and then load back to front.

#figure(cetz.canvas({
  import cetz.draw: *
  import diagram: *

  scale(0.8)

  let regy = 4

  content((0, regy - 0.5), [Registers])
  slots(
    15,
    labels: (none, reg("temp"), reg("heap"), reg("todo"), none),
    data: (imm(0), none, none, none, ddd, ddd) + (none,) * 8 + (ddd,),
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

$RELEASE$ writes the free-list pointer into the first slot and thus overwrites $a_1$.
So $RELEASE$ must happen only after loading $a_1$.
But loading $a_1$ first overwrites the block pointer register, which is still needed for the remaining loads and for $RELEASE$ itself.

In both directions, the deadlock comes from the same source:
in the original layout (@fig:scc:codegen:layout), the first slot has a double role.
It stores the pointer to the next block of the free list,
but it also corresponds to the first register of the (co)variable which contains the pointer to the block itself.

== Changing the Memory Layout
To resolve this deadlock, the layout must be changed so metadata and payload do not compete for the same critical slot.
Two equivalent options are possible.
Either rearrange (co)variable components so that the memory pointer is stored in the second register,
or rearrange the free-list block layout so that the pointer to the next block is stored in the second slot.
In this thesis, we choose the latter and place the pointer to the next block of a free list in the second slot but the first.

To preserve the alignment between the next-block pointer and reference-count position,
nonlinear allocated blocks also store the reference count in the second slot.
This does not apply to linear blocks, since they do not carry a reference count.

$
  NEXTBLOCKOFFSET & := #imm(1) \
   REFCOUNTOFFSET & := #imm(1) \
$

Applying this modification to @fig:scc:codegen:layout yields:
#figure(
  kind: "Figure",
  supplement: "Figure",
  caption: [Modified layout of heap memory blocks.],
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
        data: (none, [`next`]),
      )
    }),

    [in use (nonlinear)],
    cetz.canvas({
      import diagram: *
      memblock(
        data: (none, [`rc`]),
        fill: (reserved,) * 2 + (free-to-use,) * 8,
      )
    }),

    [in use (linear)],
    cetz.canvas({
      import diagram: *
      memblock(
        fill: (free-to-use,) * 8,
      )
    }),
  )
]

Importantly, this change affects the memory layout of all heap blocks, not only linearly used ones.

== Linear Memory Management <sec:codegen:mem>
Using the modified layout, we now define linear variants of the memory primitives.
They mirror the originals from @sec:scc:codegen:mem, but omit reference-count handling and exploit the new layout arrangement.

=== Acquire
$ACQUIRE_1$ removes the head of the linear free list and reestablishes the invariant that $HEAP$ points to a free block.
Compared to $ACQUIRE$, it does not initialize a reference count.

$
  ACQUIRE_1 sp r & := && MV r HEAP \
  & && LW HEAP NEXTBLOCKOFFSET HEAP \
  & && BNE HEAP #reg(0) l_1 \
  & && #hide[$l_1:$] MV HEAP TODO \
  & && #hide[$l_1:$] LW TODO NEXTBLOCKOFFSET TODO \
  & && #hide[$l_1:$] BEQ TODO #reg(0) l_2 \
  & && #hide[$l_1:$] #hide[$l_2:$] SW #reg(0) NEXTBLOCKOFFSET HEAP \
  & && #hide[$l_1:$] #hide[$l_2:$] ERASEFIELDS HEAP \
  & && #hide[$l_1:$] #hide[$l_2:$] JUMP l_2 \
  & && #hide[$l_1:$] l_2: ADDI TODO HEAP #imm(32) \
  & && l_1:
$

=== Store
For $STORE_1$, there are two cases to consider.

If at most three fields are needed, no conflict occurs.
Similar to the original $STORE$, we fill from back to front using $STOREV$, then call $ACQUIRE_1$.

$
  STORE_1 sp r sp Gamma & := && STOREV r sp Gamma &&
  #h(2em) #text(font: settings.font-serif, weight: "bold", "if") |Gamma| < 4 \
  &&& ACQUIRE_1 sp r \
$

The interesting case is where all four fields are needed.
The following figures illustrate the required order for $STORE_1$.

#figure(cetz.canvas({
  import cetz.draw: *
  import diagram: *

  scale(0.8)

  let regy = 4

  content((0, regy - 0.5), [Registers])
  slots(
    15,
    labels: (none, reg("temp"), reg("heap"), reg("todo"), none),
    data: (imm(0), none, none, none, ddd, ddd)
      + range(1, 9).map(i => data($a_#i$))
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
  )
  memblock(offset: (5, memy2))

  ptr(
    (4.5, regy - 0.6),
    (4.5, memy1 - 0.5),
    (5, memy1 - 0.5),
  )

  ptr(
    (6.5, memy1 - 0.6),
    (6.5, memy1 - 1.5),
    (5.5, memy1 - 1.5),
    (5.5, memy2),
  )
}))

The goal is to store all eight registers from $Gamma_0$.
Unlike the naïve setup in @sec:codegen:naive, this is now feasible because `next` is stored in the second slot.
Still, the operation order matters.

First, store all non-conflicting slots: the latter three fields and the very first slot.

#figure(cetz.canvas({
  import cetz.draw: *
  import diagram: *

  scale(0.8)

  let regy = 4

  content((0, regy - 0.5), [Registers])
  slots(
    15,
    labels: (none, reg("temp"), reg("heap"), reg("todo"), none),
    data: (imm(0), none, none, none, ddd, ddd)
      + (data($a_1$, active: false), data($a_2$))
      + range(3, 9).map(i => data($a_#i$, active: false))
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
    data: (data($a_1$), none) + range(3, 9).map(i => data($a_#i$)),
    offset: (5, memy1),
  )
  memblock(offset: (5, memy2))

  ptr(
    (4.5, regy - 0.6),
    (4.5, memy1 - 0.5),
    (5, memy1 - 0.5),
  )

  ptr(
    (6.5, memy1 - 0.6),
    (6.5, memy1 - 1.5),
    (5.5, memy1 - 1.5),
    (5.5, memy2),
  )
}))

Two steps remain: write $a_1$ and call $ACQUIRE_1$.
Now, there is no deadlock, but the order is fixed.
$ACQUIRE_1$ must come first, otherwise writing $a_2$ would destroy the free-list pointer before the $HEAP$ invariant is restored.

#figure(cetz.canvas({
  import cetz.draw: *
  import diagram: *

  scale(0.8)

  let regy = 4

  content((0, regy - 0.5), [Registers])
  slots(
    15,
    labels: (none, reg("temp"), reg("heap"), reg("todo"), none),
    data: (imm(0), none, none, none, ddd, ddd)
      + (none, data($a_2$))
      + range(3, 9).map(i => data($a_#i$, active: false))
      + (ddd,),
    offset: (2, regy),
    open-right: true,
  )

  brace(1, offset: (7, regy), label: $Gamma$)
  brace(2, offset: (8, regy), label: $v$)

  let memy1 = 2
  let memy2 = 0
  content((0, memy1 - 0.5), [Memory])
  memblock(
    data: (data($a_1$), none) + range(3, 9).map(i => data($a_#i$)),
    offset: (5, memy1),
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

  ptr(
    (6.5, memy1 - 0.6),
    (6.5, memy1 - 1.5),
    (5.5, memy1 - 1.5),
    (5.5, memy2),
  )
}))

Finally, write $a_2$ into the second slot.
Since $HEAP$ already points to the correct free-list block, overwriting the `next` pointer is now safe.

#figure(cetz.canvas({
  import cetz.draw: *
  import diagram: *

  scale(0.8)

  let regy = 4

  content((0, regy - 0.5), [Registers])
  slots(
    15,
    labels: (none, reg("temp"), reg("heap"), reg("todo"), none),
    data: (imm(0), none, none, none, ddd, ddd, none)
      + range(2, 9).map(i => data($a_#i$, active: false))
      + (ddd,),
    offset: (2, regy),
    open-right: true,
  )

  brace(1, offset: (7, regy), label: $Gamma$)
  brace(2, offset: (8, regy), label: $v$)

  let memy1 = 2
  let memy2 = 0
  content((0, memy1 - 0.5), [Memory])
  memblock(
    data: range(1, 9).map(i => data($a_#i$)),
    offset: (5, memy1),
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

Using this approach, all four fields can be used as payload in the linear case.

$
  STORE_1 sp r sp (v :^chi tau, Gamma) & := && STOREV r sp Gamma &&
  #h(2em) #text(font: settings.font-serif, weight: "bold", "if") |v :^chi tau, Gamma| = 4 \
  &&& SW (REG_1 sp v) sp (OFFSET_1 sp v) HEAP && \
  &&& ACQUIRE_1 sp r && \
  &&& SW (REG_2 sp v) sp (OFFSET_2 sp v) HEAP && \
$

=== Release
When loading from a block, $RELEASE$ in the nonlinear case checks and decrements reference counts and maybe returns the block to the free list.
For a linear block, no reference-count logic is needed.
$RELEASE_1$ directly prepends the block to the linear free list.

$
  RELEASE_1 sp r & := && SW HEAP NEXTBLOCKOFFSET r \
                 &    && MV HEAP r \
$

=== Load
$LOAD_1$ is the dual of $STORE_1$, again with two cases.

If at most three fields are loaded, we can call $RELEASE_1$ first, and then use $LOADV$.
No needed payload is destroyed.

$
  LOAD_1 sp r sp Gamma & := && RELEASE_1 sp r &&
  #h(2em) #text(font: settings.font-serif, weight: "bold", "if") |Gamma| < 4 \
  &&& LOADV r sp Gamma \
$

For the case that all four fields are loaded, the operation order must be adjusted again.

#figure(cetz.canvas({
  import cetz.draw: *
  import diagram: *

  scale(0.8)

  let regy = 4

  content((0, regy - 0.5), [Registers])
  slots(
    15,
    labels: (none, reg("temp"), reg("heap"), reg("todo"), none),
    data: (imm(0), none, none, none, ddd, ddd) + (none,) * 8 + (ddd,),
    offset: (2, regy),
    open-right: true,
  )

  brace(1, offset: (7, regy), label: $Gamma$)
  brace(2, offset: (8, regy), label: $v$)

  let memy1 = 2
  let memy2 = 0
  content((0, memy1 - 0.5), [Memory])
  memblock(
    data: range(1, 9).map(i => data($a_#i$)),
    offset: (5, memy1),
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

First load the non-conflicting slots, which are all but the very first slot ($a_1$).

#figure(cetz.canvas({
  import cetz.draw: *
  import diagram: *

  scale(0.8)

  let regy = 4

  content((0, regy - 0.5), [Registers])
  slots(
    15,
    labels: (none, reg("temp"), reg("heap"), reg("todo"), none),
    data: (imm(0), none, none, none, ddd, ddd, none)
      + range(2, 9).map(i => data($a_#i$))
      + (ddd,),
    offset: (2, regy),
    open-right: true,
  )

  brace(1, offset: (7, regy), label: $Gamma$)
  brace(2, offset: (8, regy), label: $v$)

  let memy1 = 2
  let memy2 = 0
  content((0, memy1 - 0.5), [Memory])
  memblock(
    data: (data($a_1$),) + range(2, 9).map(i => data($a_#i$, active: false)),
    offset: (5, memy1),
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

The first slot cannot be loaded directly, because that would overwrite the memory block pointer register.
But at this point, we can safely call $RELEASE_1$:
it writes the `next` pointer to the second slot which has already been loaded.

#figure(cetz.canvas({
  import cetz.draw: *
  import diagram: *

  scale(0.8)

  let regy = 4

  content((0, regy - 0.5), [Registers])
  slots(
    15,
    labels: (none, reg("temp"), reg("heap"), reg("todo"), none),
    data: (imm(0), none, none, none, ddd, ddd, none)
      + range(2, 9).map(i => data($a_#i$))
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
    data: (data($a_1$), none)
      + range(3, 9).map(i => data($a_#i$, active: false)),
    offset: (5, memy1),
  )
  memblock(offset: (5, memy2))

  ptr(
    (4.5, regy - 0.6),
    (4.5, memy1 - 0.5),
    (5, memy1 - 0.5),
  )

  ptr(
    (6.5, memy1 - 0.6),
    (6.5, memy1 - 1.5),
    (5.5, memy1 - 1.5),
    (5.5, memy2),
  )

  ptr(
    (8.5, regy - 0.6),
    (8.5, regy - 1.5),
    (5.5, regy - 1.5),
    (5.5, memy1),
  )
}))

Finally, load $a_1$ to complete the operation.

#figure(cetz.canvas({
  import cetz.draw: *
  import diagram: *

  scale(0.8)

  let regy = 4

  content((0, regy - 0.5), [Registers])
  slots(
    15,
    labels: (none, reg("temp"), reg("heap"), reg("todo"), none),
    data: (imm(0), none, none, none, ddd, ddd)
      + range(1, 9).map(i => data($a_#i$))
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
    data: (data($a_1$, active: false), none)
      + range(3, 9).map(i => data($a_#i$, active: false)),
    offset: (5, memy1),
  )
  memblock(offset: (5, memy2))

  ptr(
    (4.5, regy - 0.6),
    (4.5, memy1 - 0.5),
    (5, memy1 - 0.5),
  )

  ptr(
    (6.5, memy1 - 0.6),
    (6.5, memy1 - 1.5),
    (5.5, memy1 - 1.5),
    (5.5, memy2),
  )
}))

Thus, all four payload fields can be loaded in the linear case.

$
  LOAD_1 sp r sp (v :^chi tau, Gamma) & := && LOADV r sp Gamma &&
  #h(2em) #text(font: settings.font-serif, weight: "bold", "if") |v :^chi tau, Gamma| = 4 \
  &&& LW (REG_2 sp v) sp (OFFSET_2 sp v) sp r && \
  &&& RELEASE_1 sp r && \
  &&& LW (REG_1 sp v) sp (OFFSET_1 sp v) sp r && \
$

=== Jump Tables and Virtual Tables
#note[TODO: Write this down once decided on a notation in @sec:scc:codegen:mem.]

== Extending the Translation from #AxCut to #RISC-V
With linear memory primitives available, translation from extended #AxCut to #RISC-V can map quantity annotations directly to backend operations.
An $omega$ annotation selects the original nonlinear behavior from @sec:scc:codegen:mem,
while a $1$ annotation selects the linear variants introduced above.

#figure(
  kind: "Figure",
  supplement: "Figure",
  caption: [Modifications for the translation from extended #AxCut to #RISC-V.],
  block(width: 100%)[
    #set math.lr(size: 1em)

    // #def-box[$a2m(dot) : "Statement"_AxCut -> I^*$]
    $
      a2m(LET_q sp v = X(Gamma_0)\; s) & := && STORE_q sp (REG_1 sp v) sp Gamma_0 \
      & && LI (REG_2 sp v) sp (INDEX X) \
      & && a2m(s) \
      a2m(CREATE_q sp v = Gamma_0 sp b\; s) & := && STORE_q sp (REG_1 sp v) sp Gamma_0 \
      & && LA (REG_2 sp v) sp l \
      & && a2m(s) \
      & && l: VTABLE_q sp b sp Gamma_0 \
      a2m(SWITCH_q sp v sp b) & := && JR (REG_2 sp v) sp l \
      & && l: JTABLE_q sp b sp Gamma \
      a2m(INVOKE v sp X(Gamma)) & := && JR (REG_2 sp v) sp (INDEX X) \
    $
  ],
)

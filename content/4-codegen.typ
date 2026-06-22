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

== The Naïve Approach and Where it Fails <sec:codegen:naive>
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
To solve the deadlock, the memory layout must be modified.
There are two equally viable possibilities.
Either swap the components of a variable so that second slot contains the memory pointer
or store the pointer to the next block in a free list in the second slot instead of the first.
In this thesis, the latter approach is chosen.

To keep the property that the position of the next block in the free list is also the position of the reference count in an allocated block,
we now also store the reference count in the second slot.
This, of course, only affects nonlinear blocks, since

Modifying the original layout in @fig:scc:codegen:layout yields the following result.
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
    [on the free list],
    cetz.canvas({
      import diagram: *
      memblock(
        data: (none, [`next`]),
      )
    }),

    [nonlinearly in use],
    cetz.canvas({
      import diagram: *
      memblock(
        data: (none, [`rc`]),
        fill: (reserved,) * 2 + (free-to-use,) * 8,
      )
    }),

    [linearly in use],
    cetz.canvas({
      import diagram: *
      memblock(
        fill: (free-to-use,) * 8,
      )
    }),
  )
]

As in the other figure, `next` stands for the pointer to the next block in the free list (potentially zero if there is none),
and `rc` for the reference count of an allocated memory block.
Reserved slots of in-use slots are illustrated with grey background, slots that can freely be used for payload data are highlighted in green.

Importantly, the modification affects the memory layout of all blocks, not only those used linearly.
#inline-note[Use a auxiliary definition to parametrize this. Otherwise, the nonlinear memory mechanisms would have to be updated.]

== Linear Memory Management
#inline-note[intro]

=== Acquire
As a first step of the optimization, we modify $ACQUIRE$ for linear blocks and call it $ACQUIRE_1$.
Its job is to maintain the invariant that the $HEAP$ register points to a free memory block.
The difference to its nonlinear variant from @sec:scc:codegen:mem is that it does not have to initialize a reference count.

$
  ACQUIRE_1 sp r & := && MV r HEAP \
                 &    && LW HEAP #imm(1) HEAP \
                 &    && BEQ HEAP #reg(0) l_1 \
                 &    && #hide[$l_1:$] JUMP l_2 \
                 &    && l_1: MV HEAP TODO \
                 &    && #hide[$l_1:$] LW TODO #imm(1) TODO \
                 &    && #hide[$l_1:$] #note[or use `bne`] BEQ TODO #reg(0) l_3 \
                 &    && #hide[$l_1:$] #hide[$l_3:$] SW #reg(0) #imm(1) HEAP \
                 &    && #hide[$l_1:$] #hide[$l_3:$] ERASEFIELDS HEAP \
                 &    && #hide[$l_1:$] #hide[$l_3:$] JUMP l_2 \
                 &    && #hide[$l_1:$] l_3: ADDI TODO HEAP #imm(32) \
                 &    && l_2: \
$

=== Store
The first thing to note is that we only need to modify the storing procedure if we need to fill all four fields of the memory block.
If only three or less fields should be stored, $STOREV$ is used to fill the memory block from back to front, without touching the first field at all,
and then $ACQUIRE_1$ is called.

The more difficult situation is when all four fields of the memory block should get filled.
The following illustrations show how to $STORE_1$ operates in this situation.

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

The goal is to store the eight registers from $Gamma_0$ into the memory block.
In contrast to the scenario from @sec:codegen:naive, the memory pointer to the second free list block is located in the second slot of the first block due to the layout modifications.

First, the latter three fields and the very first slot can be stored as usual because this does not overwrite anything.

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

There are two actions left to do:
storing $a_2$ and using $ACQUIRE_1$ to restore the invariant that $HEAP$ points to some ready-to-use memory block.
Because of the layout change this is not a deadlock situation anymore.
But it is important to use $ACQUIRE_1$ before storing $a_2$, otherwise the pointer to the next memory block would be overwritten.
By using $ACQUIRE_1$ now, the free list invariant is established.

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

And finally, because the $HEAP$ already points to the correct memory block,
$a_2$ can be stored into the second slot of the memory block, overwriting the old pointer.

#figure(cetz.canvas({
  import cetz.draw: *
  import diagram: *

  scale(0.8)

  let regy = 4

  content((0, regy - 0.5), [Registers])
  slots(
    15,
    labels: (none, reg("temp"), reg("heap"), reg("todo"), none),
    data: (0, none, none, none, ddd, ddd, none)
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

#todo[TODO]

$
  STORE_1 sp r sp Gamma & := && STOREV r sp Gamma &&
  #h(2em) #text(font: settings.font-serif, weight: "bold", "if") |Gamma| < 4 \
  &&& ACQUIRE_1 sp r \
  STORE_1 sp r sp (v :^chi tau, Gamma) & := && STOREV r sp Gamma &&
  #h(2em) #text(font: settings.font-serif, weight: "bold", "if") |Gamma| = 4 \
  &&& SW (REG_1 sp v) sp (OFFSET_1 sp v) HEAP && \
  &&& ACQUIRE_1 sp r && \
  &&& SW (REG_2 sp v) sp (OFFSET_2 sp v) HEAP && \
$

=== Release
#todo[TODO]

$
  RELEASE_1 sp r & := && SW HEAP #note[parameter]#imm(1) sp r \
                 &    && MV HEAP r \
$

=== Load
#todo[TODO]

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

#todo[TODO]

#figure(cetz.canvas({
  import cetz.draw: *
  import diagram: *

  scale(0.8)

  let regy = 4

  content((0, regy - 0.5), [Registers])
  slots(
    15,
    labels: (none, reg("temp"), reg("heap"), reg("todo"), none),
    data: (0, none, none, none, ddd, ddd, none)
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

#todo[TODO]

#figure(cetz.canvas({
  import cetz.draw: *
  import diagram: *

  scale(0.8)

  let regy = 4

  content((0, regy - 0.5), [Registers])
  slots(
    15,
    labels: (none, reg("temp"), reg("heap"), reg("todo"), none),
    data: (0, none, none, none, ddd, ddd, none)
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

#todo[TODO]

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

#todo[TODO]

$
  LOAD_1 sp r sp Gamma & := && RELEASE_1 sp r &&
  #h(2em) #text(font: settings.font-serif, weight: "bold", "if") |Gamma| < 4 \
  &&& LOADV r sp Gamma \
  LOAD_1 sp r sp (v :^chi tau, Gamma) & := && LOADV r sp Gamma &&
  #h(2em) #text(font: settings.font-serif, weight: "bold", "if") |Gamma| = 4 \
  &&& LW (REG_2 sp v) sp (OFFSET_2 sp v) sp r && \
  &&& RELEASE_1 sp r && \
  &&& LW (REG_1 sp v) sp (OFFSET_1 sp v) sp r && \
$

=== Jump Tables and Virtual Tables
#todo[TODO]

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

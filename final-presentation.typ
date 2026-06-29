#import "@preview/touying:0.7.3": *
#import themes.metropolis: *

#import "/lib/lib.typ": *
#import deps: cetz, fletcher

#show: syntax-config

#set list(marker: ([–], [‣]))

#let pseudo = pseudo.with(radius: 10pt)

#show: metropolis-theme.with(
  config-info(
    title: [Linear Continuations in the Sequent Calculus Compiler],
    subtitle: [Bachelor's Thesis: Final Presentation],
    author: [Rasmus Buurman],
    date: [01.07.2026],
  ),
)

#title-slide()

== The Sequent Calculus Compiler (SCC)
#slide[
  #set align(center + bottom)
  #{
    import fletcher: diagram, edge, node

    let colored-node(color) = node.with(stroke: color, fill: color.lighten(65%))

    let fun = (0, 0)
    let core = (2, 0)
    let axcut = (4, 0)
    let riscv = (6, 0)

    show ref: set text(size: settings.font-size-normal - 3pt)

    diagram(
      debug: false,
      node-stroke: 1pt,
      node-inset: 18pt,
      label-sep: 0.2em,
      colored-node(red)(fun, [#Fun]),
      colored-node(green)(core, [#Core]),
      colored-node(blue)(axcut, [#AxCut]),
      colored-node(orange)(riscv, [Machine Code]),
      edge(fun, core, "-|>"),
      edge(core, axcut, "-|>"),
      edge(axcut, riscv, "-|>"),
    )
  }
  #v(7em)
]

== The Scope of the Optimization
#slide[
  #set align(center + bottom)
  #{
    import fletcher: diagram, edge, node, shapes

    let colored-node(color) = node.with(stroke: color, fill: color.lighten(65%))

    let fun = (0, 0)
    let core = (2, 0)
    let axcut = (4, 0)
    let riscv = (6, 0)

    show ref: set text(size: settings.font-size-normal - 3pt)

    diagram(
      debug: false,
      node-stroke: 1pt,
      node-inset: 18pt,
      label-sep: 0.2em,
      node(
        enclose: ((0, 0), (2, 0), (1, -1)),
        shape: shapes.brace.with(dir: top, label: [
          #set text(size: 1.5em)
          Restrict
          #v(0.5em)
        ]),
      ),
      node(
        enclose: ((4, 0), (6, 0), (5, -1)),
        shape: shapes.brace.with(dir: top, label: [
          #set text(size: 1.5em)
          Extend
          #v(0.5em)
        ]),
      ),
      colored-node(red)(fun, [#Fun]),
      colored-node(green)(core, [#Core]),
      colored-node(blue)(axcut, [#AxCut]),
      colored-node(orange)(riscv, [Machine Code]),
      edge(fun, core, "-|>"),
      edge(core, axcut, "-|>"),
      edge(axcut, riscv, "-|>"),
    )
  }
  #v(7em)
]

= Linear Continuations

#slide(composer: (1fr, 1fr))[
  #pseudo(
    stroke: red,
    inset: 1em,
    numbers: auto,
    $DEF f(): i64 sp {$,
    (
      $g(#imm(1)) + #imm(2)$,
    ),
    $}$,
    none,
    $DEF g(x: i64): i64 sp {$,
    (
      $IF x equiv #imm(0) sp { quad #imm(42) quad }$,
      $ELSE { quad x + x quad }$,
    ),
    $}$,
  )
][
  #pause
  #pseudo(
    stroke: green,
    inset: 1em,
    numbers: auto,
    $DEF f(kappa :^cns i64) sp {$,
    (
      $cut((mu alpha. g(#imm(1), sp alpha)) + #imm(2), kappa)$,
    ),
    $}$,
    none,
    $DEF g(x :^prd i64, sp kappa :^cns i64) sp {$,
    (
      $IF x equiv #imm(0) sp { quad cut(#imm(42), kappa) quad }$,
      $ELSE { quad cut(x + x, kappa) quad }$,
    ),
    $}$,
  )
]

== Nonlinear Continuations

#slide(composer: (1fr, 1.2fr))[
  #pseudo(
    stroke: red,
    inset: 1em,
    numbers: auto,
    $DEF f(): i64 {$,
    (
      $LABEL alpha sp {$,
      (
        $g(#imm(1), sp alpha) + #imm(2)$,
      ),
      $}$,
    ),
    $}$,
    none,
    $DEF g(x: i64, sp alpha :^cns i64): i64 sp {$,
    (
      $IF x equiv #imm(0) sp { quad GOTO alpha sp (#imm(42)) quad }$,
      $ELSE { quad x+x quad }$,
    ),
    $}$,
  )
][
  #pause
  #pseudo(
    stroke: green,
    inset: 1em,
    numbers: auto,
    $DEF f(kappa :^cns i64) sp {$,
    (
      $cl mu alpha.$,
      (
        $cut((mu beta. g(#imm(1), sp alpha, sp beta)) + #imm(2), alpha)$,
      ),
      $| kappa cr$,
    ),
    $}$,
    none,
    $DEF g(x :^prd i64, sp alpha :^cns i64, sp kappa :^cns i64) sp {$,
    (
      $IF x equiv #imm(0) sp { quad cut(#imm(42), alpha) quad }$,
      $ELSE { quad cut(x + x, kappa) quad }$,
    ),
    $}$,
  )
]

== Restrictions
#slide(composer: (1fr, 1.2fr))[
  - Restrict #Fun:

    - no control operators ($LABEL$, $GOTO$)

    - only local control flow
][
  - Restrict #Core:

    - image of the translation from restricted #Fun

    - only linear continuations
]

== Linearity Annotations in #AxCut

#slide(composer: (1fr, 0.7fr))[
  #set align(center + top)

  #let (Unit, unit) = (`Unit`, `U`)
  #let (Fun, ap) = (`Fun`, `ap`)

  #pseudo(
    stroke: blue,
    inset: 1em,
    numbers: auto,
    $DEF f(kappa_f :^cns Unit) sp {$,
    (
      $LET u :^prd Unit = unit;$,
      $CREATE h :^prd Fun = () sp { sp ap(u, sp kappa_h) =>$,
      (
        $INVOKE kappa_h sp U$,
      ),
      $};$,
      $CREATE alpha :^cns Unit = (kappa_f, sp h) sp { sp unit =>$,
      (
        $LET x :^prd Unit = U;$,
        $INVOKE h ap(x, sp kappa_f)$,
      ),
      $};$,
      $LET beta :^cns Fun = ap(u, sp alpha); quad g(beta)$,
    ),
    $}$,
  )
][
  #set align(center + top)

  #let (Unit, unit) = (`Unit`, `U`)
  #let (Fun, ap) = (`Fun`, `ap`)

  #pseudo(
    stroke: blue,
    inset: 1em,
    $DATA Unit sp { quad unit quad }$,
    none,
    $CODATA Fun {$,
    (
      $ap(x :^prd Unit, kappa :^cns Unit)$,
    ),
    $}$,
    none,
    $DEF g(kappa_g :^cns Fun) sp { sp ... sp }$,
  )
]
#slide(composer: (1fr, 0.7fr))[
  #set align(center + top)

  #let (Unit, unit) = (`Unit`, `U`)
  #let (Fun, ap) = (`Fun`, `ap`)

  #pseudo(
    stroke: blue,
    inset: 1em,
    numbers: auto,
    $DEF f(kappa_f :^cns Unit) sp {$,
    (
      $highlight(LET sp u :^prd Unit, color: #green) = unit;$,
      $highlight(CREATE sp h :^prd Fun, color: #green) = () sp { sp ap(u, sp kappa_h) =>$,
      (
        $INVOKE kappa_h sp U$,
      ),
      $};$,
      $highlight(CREATE sp alpha :^cns Unit, color: #orange) = (kappa_f, sp h) sp { sp unit =>$,
      (
        $LET x :^prd Unit = U;$,
        $INVOKE h ap(x, sp kappa_f)$,
      ),
      $};$,
      $highlight(LET sp beta :^cns Fun, color: #orange) = ap(u, sp alpha); quad g(beta)$,
    ),
    $}$,
  )
][
  #set align(center + top)

  #let (Unit, unit) = (`Unit`, `U`)
  #let (Fun, ap) = (`Fun`, `ap`)

  #pseudo(
    stroke: blue,
    inset: 1em,
    $DATA Unit sp { quad unit quad }$,
    none,
    $CODATA Fun {$,
    (
      $ap(x :^prd Unit, kappa :^cns Unit)$,
    ),
    $}$,
    none,
    $DEF g(kappa_g :^cns Fun) sp { sp ... sp }$,
  )
]

#slide(composer: (1fr, 0.7fr))[
  #set align(center + top)

  #let (Unit, unit) = (`Unit`, `U`)
  #let (Fun, ap) = (`Fun`, `ap`)

  #pseudo(
    stroke: blue,
    inset: 1em,
    numbers: auto,
    $DEF f(kappa_f :^cns Unit) sp {$,
    (
      $highlight(LET_omega sp u :^prd Unit, color: #green) = unit;$,
      $highlight(CREATE_omega sp h :^prd Fun, color: #green) = () sp { sp ap(u, sp kappa_h) =>$,
      (
        $INVOKE kappa_h sp U$,
      ),
      $};$,
      $highlight(CREATE_1 sp alpha :^cns Unit, color: #orange) = (kappa_f, sp h) sp { sp unit =>$,
      (
        $LET_omega sp x :^prd Unit = U;$,
        $INVOKE h ap(x, sp kappa_f)$,
      ),
      $};$,
      $highlight(LET_1 sp beta :^cns Fun, color: #orange) = ap(u, sp alpha); quad g(beta)$,
    ),
    $}$,
  )
][
  #set align(center + top)

  #let (Unit, unit) = (`Unit`, `U`)
  #let (Fun, ap) = (`Fun`, `ap`)

  #pseudo(
    stroke: blue,
    inset: 1em,
    $DATA Unit sp { quad unit quad }$,
    none,
    $CODATA Fun {$,
    (
      $ap(x :^prd Unit, kappa :^cns Unit)$,
    ),
    $}$,
    none,
    $DEF g(kappa_g :^cns Fun) sp { sp ... sp }$,
  )
]

= Optimizing Code Generation

== Memory Management
#slide[
  #set align(center + bottom)

  #cetz.canvas({
    import cetz.draw: *
    import diagram: *

    scale(1.5)
    set-style(stroke: 2pt)

    let regy = 4

    content((0, regy - 0.5), [Registers])
    slots(
      15,
      labels: (none, none, reg("heap"), none),
      data: (none,) * 14 + (ddd,),
      offset: (2, regy),
      open-right: true,
    )

    brace(11, offset: (6, regy), label: $Gamma$)

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
      (5.5, memy1 - 0.6),
      (5.5, memy2),
    )

    ptr(
      (5.5, memy2 - 0.6),
      (5.5, -2),
    )
  })

  #v(2em)
]

#slide[
  #set align(center + bottom)

  #cetz.canvas({
    import cetz.draw: *
    import diagram: *

    scale(1.5)
    set-style(stroke: 2pt)

    let regy = 4

    content((0, regy - 0.5), [Registers])
    slots(
      15,
      labels: (none, none, reg("heap"), none),
      data: (none,) * 14 + (ddd,),
      offset: (2, regy),
      open-right: true,
    )

    brace(2, offset: (9, regy), label: $v_1$)

    let memy1 = 2
    let memy2 = 0
    content((0, memy1 - 0.5), [Memory])
    memblock(
      offset: (5, memy1),
      data: (`rc`, none),
      fill: (reserved, reserved) + (free-to-use,) * 6,
    )
    memblock(offset: (5, memy2))

    ptr(
      (4.5, regy - 0.6),
      (4.5, memy2 - 0.5),
      (5, memy2 - 0.5),
    )

    ptr(
      (5.5, memy2 - 0.6),
      (5.5, -2),
    )

    ptr(
      (9.5, regy - 0.6),
      (9.5, regy - 1.5),
      (5.5, regy - 1.5),
      (5.5, memy1),
    )
  })

  #v(2em)
]

#slide[
  #set align(center + bottom)

  #cetz.canvas({
    import cetz.draw: *
    import diagram: *

    scale(1.5)
    set-style(stroke: 2pt)

    let regy = 4

    content((0, regy - 0.5), [Registers])
    slots(
      15,
      labels: (none, none, reg("heap"), none),
      data: (none,) * 14 + (ddd,),
      offset: (2, regy),
      open-right: true,
    )

    brace(2, offset: (9, regy), label: $v_1$)
    brace(2, offset: (13, regy), label: $v_2$)

    let memy1 = 2
    let memy2 = 0
    content((0, memy1 - 0.5), [Memory])
    memblock(
      offset: (5, memy1),
      data: (`rc`, none),
      fill: (reserved, reserved) + (free-to-use,) * 6,
    )
    memblock(offset: (5, memy2))

    ptr(
      (4.5, regy - 0.6),
      (4.5, memy2 - 0.5),
      (5, memy2 - 0.5),
    )

    ptr(
      (5.5, memy2 - 0.6),
      (5.5, -2),
    )

    ptr(
      (9.5, regy - 0.6),
      (9.5, regy - 1.5),
      (5.5, regy - 1.5),
      (5.5, memy1),
    )

    ptr(
      (13.5, regy - 0.6),
      (13.5, memy1 - 1.5),
      (5.5, memy1 - 1.5),
      (5.5, memy1 - 1),
    )
  })

  #v(2em)
]

== Optimizing for Linearity
#slide[
  #set align(center + bottom)

  #cetz.canvas({
    import cetz.draw: *
    import diagram: *

    scale(1.5)
    set-style(stroke: 2pt)

    let regy = 4

    content((0, regy - 0.5), [Registers])
    slots(
      15,
      labels: (none, none, reg("heap"), none),
      data: (none,) * 14 + (ddd,),
      offset: (2, regy),
      open-right: true,
    )

    brace(2, offset: (9, regy), label: [linear $v$])

    let memy1 = 2
    let memy2 = 0
    content((0, memy1 - 0.5), [Memory])
    memblock(
      offset: (5, memy1),
      fill: (free-to-use,) * 8,
    )
    memblock(offset: (5, memy2))

    ptr(
      (4.5, regy - 0.6),
      (4.5, memy2 - 0.5),
      (5, memy2 - 0.5),
    )

    ptr(
      (5.5, memy2 - 0.6),
      (5.5, -2),
    )

    ptr(
      (9.5, regy - 0.6),
      (9.5, regy - 1.5),
      (5.5, regy - 1.5),
      (5.5, memy1),
    )
  })

  #v(2em)
]

#slide[
  #set align(top)

  *Advantages:*

  - Better memory usage

  - Smaller code size

  - Less runtime overhead
][
  #set align(top)

  *Disadvantages:*

  #pause
  - none :)
]

== Implementation
#image("resources/img/final-presentation/pr.png")

== Evaluation

#focus-slide[
  BENCHMARKS
]

== Future Work
#slide[
  *Implementation:*

  - implementation for `AArch64` and `RISC-V`

  - some implementation details (e.g. spilling)
][
  *Make Better Use of the Backend:*

  - full linear type system (#Fun and #Core)

  - linearity detection in #AxCut
]

#focus-slide[
  Thank you!

  I hope you had #Fun!
]

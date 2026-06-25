#import "@preview/touying:0.7.3": *
#import themes.metropolis: *

#import "/lib/lib.typ": *
#import deps: fletcher

#show: metropolis-theme.with(
  config-info(
    title: [Linear Continuations in the Sequent Calculus Compiler],
    subtitle: [Bachelor's Thesis: Final Presentation],
    author: [Rasmus Buurman],
    date: [01.07.2026],
  ),
)

#title-slide()

= The Sequent Calculus Compiler

#figure({
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
    colored-node(orange)(riscv, [#RISC-V]),
    edge(fun, core, "-|>", label: $f2c(dot)$, label-side: left),
    edge(
      fun,
      core,
      "-|>",
      label-side: right,
      stroke: none,
    ),
    edge(core, axcut, "-|>", label: $c2a(dot)$, label-side: left),
    edge(
      core,
      axcut,
      "-|>",
      label-side: right,
      stroke: none,
    ),
    edge(axcut, riscv, "-|>", label: $a2m(dot)$, label-side: left),
    edge(
      axcut,
      riscv,
      "-|>",
      label-side: right,
      stroke: none,
    ),
    edge(
      core,
      core,
      "-|>",
      bend: -135deg,
      label: $focus(dot), shrink(dot)$,
    ),
  )
})

= Linear Continuations

= Optimizing Code Generation

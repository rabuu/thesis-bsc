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

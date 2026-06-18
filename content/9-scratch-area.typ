#import "/lib/lib.typ": *
#import deps: cetz

#show heading: set heading(outlined: false)

= Scratch Area

== Diagrams
#figure(cetz.canvas({
  import cetz.draw: *
  import cetz.decorations: brace
  import diagram: *

  scale(0.8)

  let t = text.with(size: 0.8em)
  let reg(it) = t(raw(it))
  let data(it) = text(fill: green, it)

  let ptr = line.with(stroke: purple, mark: (end: (symbol: ")>", fill: purple)))

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

  brace((7, regy), (8, regy))
  content((7.5, regy + 0.5), t($Gamma$))

  brace((8, regy), (16, regy))
  content((12, regy + 0.5), t($Gamma_0$))

  let memy1 = 2
  let memy2 = 0
  content((0, memy1 - 0.5), [Memory])
  memblock(offset: (5, memy1))
  memblock(offset: (5, memy2))

  ptr(
    (4.5, regy - 0.6),
    (4.5, memy1 - 0.5),
    (5, memy1 - 0.5),
  )

  ptr(
    (6.5, memy1 - 0.6),
    (6.5, memy1 - 1.3),
    (5.5, memy1 - 1.3),
    (5.5, memy2),
  )
}))

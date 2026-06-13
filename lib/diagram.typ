#import "deps.typ": cetz

#import cetz.draw: *

#let slot(
  n,
  data: none,
  offset: (0, 0),
  fields: false,
  size: 1,
  open-left: false,
  open-right: false,
) = {
  let (dx, dy) = offset
  let (x, y) = (dx + n * size, dy)
  let nw = (x, y)
  let ne = (x + size, y)
  let sw = (x, y - size)
  let se = (x + size, y - size)

  line(nw, ne)
  line(sw, se)

  if n == 0 and not open-left {
    line(nw, sw)
  }

  if not open-right {
    let dash = if calc.even(n) and fields { "dashed" } else { "solid" }
    line(se, ne, stroke: (dash: dash))
  }

  if data != none {
    let center = (x + size / 2, y - size / 2)
    content(center, [#data])
  }
}

#let slots(
  n,
  data: (),
  offset: (0, 0),
  fields: false,
  size: 1,
  open-left: false,
  open-right: false,
) = {
  for i in range(0, n) {
    let data = data.at(i, default: none)
    let open-left = open-left and i == 0
    let open-right = open-right and i == n - 1
    slot(
      i,
      data: data,
      offset: offset,
      fields: fields,
      size: size,
      open-left: open-left,
      open-right: open-right,
    )
  }
}

#let memblock(data: (), offset: (0, 0), size: 1) = slots(
  8,
  data: data,
  offset: offset,
  fields: true,
  size: size,
)

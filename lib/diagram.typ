#import "deps.typ": cetz

#import cetz.draw: *

#let ddd = $dot dot dot$

#let t = text.with(size: 0.8em)
#let reg(it) = t(raw(it))
#let data(it, active: true) = text(fill: if active { green } else { gray }, it)
#let ptr = line.with(stroke: purple, mark: (end: (symbol: ")>", fill: purple)))

#let brace(range, offset: (0, 0), label: none) = {
  let (dx, dy) = offset
  cetz.decorations.brace((dx, dy), (dx + range, dy))
  if label != none {
    content((dx + (range / 2), dy + 0.5), t(label))
  }
}

#let slot(
  n,
  offset: (0, 0),
  data: none,
  label: none,
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

  if label != none {
    let pos = (x + size / 2, y + size / 2 - size / 10)
    content(pos, [#label], anchor: "north")
  }
}

#let slots(
  n,
  data: (),
  labels: (),
  offset: (0, 0),
  fields: false,
  size: 1,
  open-left: false,
  open-right: false,
) = {
  for i in range(0, n) {
    let data = data.at(i, default: none)
    let label = labels.at(i, default: none)
    let open-left = open-left and i == 0
    let open-right = open-right and i == n - 1
    slot(
      i,
      data: data,
      label: label,
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

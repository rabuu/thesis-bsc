#import "deps.typ": cetz
#import "globals.typ": *

#import cetz.draw: *

#let ddd = $dot dot dot$

#let t = text.with(size: 0.8em)
#let reg(it) = t(raw(it))
#let data(it, active: true) = text(fill: if active { green } else { gray }, it)

#let ptr-color = black
#let ptr = line.with(stroke: ptr-color, mark: (
  end: (symbol: ")>", fill: ptr-color),
))
#let halfptr1 = line.with(stroke: (paint: ptr-color, dash: "solid"))
#let halfptr2 = line.with(stroke: (paint: ptr-color, dash: "dashed"))

#let reserved = gray.lighten(20%)
#let free-to-use = lightgreen

#let brace(
  range,
  offset: (0, 0),
  label: none,
  flipped: false,
) = {
  let (dx, dy) = offset

  let start = (dx, dy)
  let end = (dx + range, dy)

  if flipped {
    cetz.decorations.brace(end, start)
  } else {
    cetz.decorations.brace(start, end)
  }

  if label != none {
    let x = dx + (range / 2)
    let y = if flipped { dy - 0.5 } else { dy + 0.5 }
    content((x, y), t(label))
  }
}

#let slot(
  n,
  offset: (0, 0),
  data: none,
  label: none,
  fill: none,
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

  if fill != none {
    rect(nw, se, stroke: none, fill: fill)
  }

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
  fill: (),
  offset: (0, 0),
  fields: false,
  size: 1,
  open-left: false,
  open-right: false,
) = {
  for i in range(0, n) {
    let data = data.at(i, default: none)
    let label = labels.at(i, default: none)
    let fill = fill.at(i, default: none)
    let open-left = open-left and i == 0
    let open-right = open-right and i == n - 1
    slot(
      i,
      data: data,
      label: label,
      fill: fill,
      offset: offset,
      fields: fields,
      size: size,
      open-left: open-left,
      open-right: open-right,
    )
  }
}

#let memblock(
  data: (),
  fill: (),
  offset: (0, 0),
  size: 1,
) = slots(
  8,
  data: data,
  fill: fill,
  offset: offset,
  fields: true,
  size: size,
)

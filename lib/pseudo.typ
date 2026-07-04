#let default-number-style(i) = {
  raw(str(i))
  h(1em)
}

#let pseudo(
  ..lines,
  numbers: none,
  resize-parens: false,
  indent: 2em,
  width: auto,
  height: auto,
  fill: none,
  stroke: (:),
  radius: (:),
  inset: (:),
  outset: (:),
) = {
  let lines = lines.pos()

  let apply-indent(it, depth: 0, first: true) = {
    if type(it) == array {
      let depth = if first { depth } else { depth + 1 }
      return it.map(apply-indent.with(depth: depth, first: false)).flatten()
    }

    let it = [#it]
    let indent = ((h(indent),) * depth).join()

    indent
    it
  }

  let lines = apply-indent(lines)

  if numbers != none {
    let number-style = if numbers == auto {
      default-number-style
    } else {
      numbers
    }

    lines = lines
      .enumerate(start: 1)
      .map(iline => {
        let (i, line) = iline
        (number-style(i), line)
      })
  }

  set math.lr(size: 1em) if not resize-parens

  let columns = auto
  let align = left + horizon

  if numbers != none {
    columns = (auto, columns)
    align = (right + horizon, align)
  }

  block(
    width: width,
    height: height,
    fill: fill,
    stroke: stroke,
    radius: radius,
    inset: inset,
    outset: outset,
    grid(
      columns: columns,
      rows: 1.5em,
      align: align,
      ..lines.flatten()
    ),
  )
}

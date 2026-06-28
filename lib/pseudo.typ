#let default-number-style(i, size: 0.6em) = {
  set align(horizon)
  text(size: size, str(i))
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
  inset: 0.3em,
  outset: (:),
) = {
  let lines = lines.pos()

  let apply(it, depth: 0, line: 1, first: true) = {
    if type(it) == array {
      let depth = if first { depth } else { depth + 1 }
      return it
        .map(apply.with(depth: depth, line: line, first: false))
        .flatten()
    }

    let it = [#it]

    let indent = ((h(indent),) * depth).join()
    (
      math.equation({
        $&$
        indent
        it
      })
    )
  }

  let body = for (i, line) in apply(lines).enumerate(start: 1) {
    let number = if numbers != none {
      let number-style = if numbers == auto {
        default-number-style
      } else {
        numbers
      }
      number-style(i)
    }
    math.equation[#number#line#linebreak()]
  }

  set math.lr(size: 1em) if not resize-parens

  block(
    width: width,
    height: height,
    fill: fill,
    stroke: stroke,
    radius: radius,
    inset: inset,
    outset: outset,
    math.equation(block: true, body),
  )
}

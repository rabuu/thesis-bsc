#let bnf(
  def-symbol: $::=$,
  sep-symbol: $|$,
  column-gutter: 1em,
  row-gutter: 0.75em,
  padding-line: false,
  ..body,
) = {
  assert(body.named().len() == 0)
  let body = body.pos()
  assert(body.len() >= 1)
  assert(type(body.at(0)) == array)

  let rows = ()
  let waiting = false
  let first = true
  for el in body {
    if type(el) == array {
      if padding-line and not first {
        rows.push((none,) * 4)
      }
      assert(el.len() == 2)
      let var = el.at(0)
      let annot = h(column-gutter) + emph(el.at(1))
      rows.push((var, def-symbol, none, annot))
      waiting = true
    } else {
      let body = el
      if waiting {
        let last-line = rows.pop()
        last-line.at(2) = body
        rows.push(last-line)
        waiting = false
      } else {
        rows.push((none, sep-symbol, body, none))
      }
    }
    first = false
  }

  grid(
    // meta-variable, symbol, body, annotation
    columns: 4,
    column-gutter: column-gutter,
    row-gutter: row-gutter,
    align: (right, right, left, left + horizon),
    ..rows.flatten()
  )
}

#let alt(
  separation-symbol: $|$,
  pad: 1em,
  ..alternatives,
) = {
  assert(alternatives.named().len() == 0)
  let alternatives = alternatives.pos()

  alternatives.intersperse(h(pad) + separation-symbol + h(pad)).join()
}

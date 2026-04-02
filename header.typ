#let header(
  padding-top: 0.2em,
  padding-bottom: 0.2em,
  alignment: left,
  line: false,
  ..contents,
) = {
  assert(contents.named().len() == 0, message: "Unexpected named argument")

  let header = {
    set align(alignment)

    contents.pos().join(h(1fr))

    if line {
      v(-0.8em)
      std.line(length: 100%, stroke: black)
    }
  }

  pad(top: padding-top, bottom: padding-bottom, header)
}

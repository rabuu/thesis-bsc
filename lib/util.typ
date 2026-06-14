#let pagebreak-to(
  disable-header: true,
  disable-numbering: true,
  to: "odd",
  weak: true,
) = {
  set page(header: none, footer: none, numbering: none)
  pagebreak(to: "odd", weak: true)
}

#let def-box(
  inset: 0.5em,
  stroke: 1pt,
  it,
) = align(right, block(inset: inset, stroke: stroke, it))

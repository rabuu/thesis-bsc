#let pagebreak-to(
  disable-header: true,
  disable-numbering: true,
  to: "odd",
  weak: true,
) = {
  set page(header: none, footer: none, numbering: none)
  pagebreak(to: "odd", weak: true)
}

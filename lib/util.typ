#import "settings.typ"

#let pagebreak-to(
  disable-header: true,
  disable-numbering: true,
  to: "odd",
  weak: true,
) = {
  set page(header: none, footer: none, numbering: none)
  pagebreak(to: "odd", weak: true)
}

#let appendix(
  /// The supplement of the appendix sections. -> content | str | function | none
  supplement: "Appendix",
  /// The numbering pattern for the appendix sections. -> str | none
  numbering: "A.1",
  /// The appendix body itself. -> content
  body,
) = [
  #set heading(numbering: numbering, supplement: supplement)

  #counter(heading).update(0)

  #body
]

#let todo(body) = text(fill: red, body)

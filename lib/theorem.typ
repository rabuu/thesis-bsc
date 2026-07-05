#import "deps.typ": theorion

#let (
  definition-counter,
  definition-box,
  definition,
  show-definition,
) = theorion.make-frame(
  "definition",
  "Definition",
  inherited-levels: 1,
  render: theorion.cosmos.simple.render-fn.with(style: "definition", inset: (
    x: 1.5em,
    y: 0.3em,
  )),
)

#let (
  example-counter,
  example-box,
  example,
  show-example,
) = theorion.make-frame(
  "example",
  "Example",
  counter: definition-counter,
  render: theorion.cosmos.simple.render-fn.with(style: "remark", inset: (
    x: 1.5em,
    y: 0.3em,
  )),
)

#let theorem-config(it) = {
  show: theorion.show-theorion
  theorion.set-theorion-numbering("1.1")
  it
}

#import "deps.typ": curryst
#import curryst: prooftree, rule

// Rule name
#let rn(name) = {
  box(smallcaps(name))
}

#let mid = scale(sym.bar.v, y: 50%)

#let rule-set(
  column-gutter: 3em,
  row-gutter: 2em,
  manual-grouping: false,
  ..it,
) = {
  set par(leading: row-gutter)

  if manual-grouping {
    let subsets = it
      .pos()
      .map(subset => {
        if type(subset) != array { subset = (subset,) }
        subset.map(box).join(h(column-gutter, weak: true))
      })
    block(subsets.join(linebreak()))
  } else {
    let rules = it
    block(rules.pos().map(box).join(h(column-gutter, weak: true)))
  }
}

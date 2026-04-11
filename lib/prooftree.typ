#import "settings.typ"
#import "deps.typ": curryst
#import curryst: prooftree, rule, rule-set

// Rule name
#let rn(name) = {
  smallcaps(name)
}

#let mid = scale(sym.bar.v, y: 50%)

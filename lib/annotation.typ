#import "deps.typ"

#let todo = text.with(fill: red)

#let sidenote = deps.drafting.margin-note
#let note = deps.drafting.inline-note

// math annotations
#let mark = deps.mannot.markhl.with(color: yellow)
#let erase = deps.mannot.mark.with(color: gray)
#let highlight = deps.mannot.markhl.with(color: gray, outset: 0.1em)

#import "deps.typ"

#let todo = text.with(fill: red)

#let sidenote = deps.drafting.margin-note
#let note = deps.drafting.inline-note

// FIX: see https://github.com/ryuryu-ymj/mannot/issues/9
#let mannot-mark-fixed(
  body,
  tag: none,
  color: auto,
  outset: (y: .1em),
) = {
  if color != auto {
    return context {
      set text(fill: color)
      deps.mannot.core-mark(body, tag: tag, color: color, outset: outset)
    }
  } else {
    return context {
      let color = text.fill
      deps.mannot.core-mark(body, tag: tag, color: color, outset: outset)
    }
  }
}

// math annotations
#let mark = deps.mannot.markhl.with(color: yellow)
#let erase = mannot-mark-fixed.with(color: gray)
#let highlight = deps.mannot.markhl.with(color: gray, outset: 0.1em)

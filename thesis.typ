#import "@preview/hydra:0.6.2": hydra

// TODO: Replace with @preview
#import "@local/theseus:0.1.0"

#import "metadata.typ" as meta

#set document(
  title: meta.title,
  author: meta.author,
)

#set page(
  paper: "a4",
)

#set text(
  font: "Libertinus Serif",
  size: 12pt,
)

#set par(
  justify: true,
)

//
// TITLE
//

#theseus.title.se-tuebingen(
  author: meta.author,
  title: meta.title-linebreak,
  title-unformatted: meta.title,
  thesis-type-title: meta.thesis-type-title,
  university: meta.university,
  department: meta.department,
  institute: meta.institute,
  student-id: meta.student-id,
  submission-date: meta.submission-date,
  period: [Thesis period: #meta.period],
  reviewer: (
    name: meta.reviewer,
    department: meta.reviewer-department,
    university: meta.reviewer-university,
  ),
  backside: true,
)

//
// FRONTMATTER
//

#set page(numbering: "i")
#counter(page).update(1)

#include "content/frontmatter.typ"
#pagebreak(to: "odd")

//
// TABLE OF CONTENTS
//

#set page(numbering: "1")
#counter(page).update(1)

#outline()
#pagebreak(to: "odd")

//
// MAIN PART
//

#set page(
  header: context {
    let odd = calc.odd(here().page())
    let text = if odd {
      hydra(1, skip-starting: true)
    } else {
      hydra(2, skip-starting: false)
    }
    let alignment = if odd { left } else { right }
    theseus.header.basic(text, alignment: alignment)
  },
  margin: (
    inside: 3.5cm,
    outside: 2.5cm,
  ),
)

#set heading(numbering: "1.")

= First Chapter
#lorem(400)

= Second Chapter
#lorem(500)

= Third Chapter
#lorem(300)

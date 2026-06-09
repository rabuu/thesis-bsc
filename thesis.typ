#import "lib/lib.typ": *
#import deps: hydra, theseus

#import hydra: hydra
#import theseus: appendix

#set document(
  title: meta.title,
  author: meta.author,
)

#set page(
  paper: "a4",
  binding: settings.binding,
  margin: (
    inside: settings.margin-inside,
    outside: settings.margin-outside,
  ),
)

#set text(
  font: settings.font-serif,
  size: settings.font-size-normal,
)

#show math.equation: set text(font: settings.font-math)

// NOTE: smallcaps don't work in math font
#show smallcaps: set text(font: settings.font-serif)

#set par(
  justify: true,
)

#set list(marker: ([–], [‣]))
#set figure(gap: 2em)

#show heading: set text(font: settings.font-sans)
#show heading.where(level: 1): set text(size: settings.font-size-chapter)

#show: syntax-config
#show: theorem-config

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

#counter(page).update(1)
#set page(
  numbering: "i",
  footer: context {
    let current-page = here().page()
    let chapters = query(heading.where(level: 1))

    let even = calc.even(here().page())
    let alignment = if even { left } else { right }

    align(alignment, counter(page).display())
  },
)

#include "content/0-frontmatter.typ"
#pagebreak-to()

//
// MAIN PART
//

#counter(page).update(1)

#set page(
  numbering: "1",
  header: context {
    let current-page = here().page()
    let even = calc.even(current-page)

    let chapters = query(heading.where(level: 1))
    if chapters.any(chapter => chapter.location().page() == current-page) {
      return none
    }

    let text = if even {
      hydra(1, skip-starting: false)
    } else {
      hydra(2, skip-starting: false)
    }

    let alignment = if even { left } else { right }

    theseus.header.basic(text, alignment: alignment, line: true)
  },
)

#set heading(numbering: "1.1")

#show heading: it => block({
  if it.has("numbering") and it.numbering != none {
    counter(heading).display(it.numbering) + h(1em) + it.body
  } else {
    it
  }
})

#show heading.where(level: 1): it => {
  pagebreak-to()
  pad(it, top: 3cm, bottom: 1cm)
}

#include "content/1-introduction.typ"
#include "content/2-scc.typ"
#include "content/3-linear-continuations.typ"
#include "content/4-codegen.typ"
#include "content/5-conclusion.typ"
#include "content/9-scratch-area.typ"

#bibliography(
  "references.yaml",
  style: "association-for-computing-machinery",
  title: "References",
)

#show: appendix.with(title: none)

#include "content/A-implementation.typ"

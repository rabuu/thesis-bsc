// TODO: Replace with @preview
#import "@local/theseus:0.1.0"

#import "metadata.typ" as meta

#set document(
  title: meta.title,
  author: meta.author,
)

#set page(
  paper: "a4",
  numbering: none,
)

#set text(
  font: "Libertinus Serif",
  size: 12pt,
)

#set par(
  justify: true,
)

#theseus.title.basic(
  author: meta.author,
  title: meta.title,
  thesis-type-title: meta.thesis-type-title,
  university: meta.university,
  department: meta.department,
  institute: meta.institute,
  submission-date: meta.submission-date,
  reviewer: (
    name: meta.reviewer,
    department: meta.reviewer-department,
    university: meta.reviewer-university,
  ),
)

#set page(
  header: theseus.header.basic(
    meta.title,
    meta.author,
    line: true,
  ),
)

#set heading(numbering: "1.")

= First Chapter
#lorem(100)

= Second Chapter
#lorem(300)

= Third Chapter
#lorem(700)

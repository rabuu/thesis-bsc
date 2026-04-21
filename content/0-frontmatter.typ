#import "/lib/lib.typ": *

#set heading(outlined: false)
#show heading: it => {
  pad(it, top: 1cm, bottom: 1cm)
}

= Abstract
#lorem(100)

#pagebreak()

#[
  #set text(lang: "de")

  = Zusammenfassung
  #lorem(100)
]

#pagebreak-to()

= Acknowlegements
#lorem(100)

#pagebreak-to()

//
// TABLE OF CONTENTS
//

#show outline.entry: it => {
  show linebreak: none
  it
}

#show outline.entry.where(level: 1): set outline.entry(fill: none)
#show outline.entry.where(level: 1): set block(above: 1.35em)
#show outline.entry.where(level: 1): set text(weight: "semibold")

#outline()

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

#show outline.entry.where(
  level: 1,
): it => {
  set block(above: 1.2em)
  strong(it)
}

#outline()

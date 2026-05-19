#import "/lib/lib.typ": *

#set heading(outlined: false)
#show heading: it => {
  pad(it, top: 1cm, bottom: 1cm)
}

= Abstract
The Sequent Calculus Compiler (SCC) is a research compiler that uses sequent-calculus-based intermediate representations to compile a functional programming language to native machine code.
In the SCC, control flow is made explicit through consumer types.
Continuations are consumers representing the control flow between function calls.
In standard functional programs, each continuation is used exactly once (linearly),
which enables simplified memory management in the generated code.
However, the SCC also supports special control operators that break this linearity assumption.
This thesis explores how to statically track the linearity of continuations and exploit it to generate more efficient machine code,
reducing both runtime overhead and memory usage.

#pagebreak()

#[
  #set text(lang: "de")

  = Zusammenfassung
  #lorem(100)
]

#pagebreak-to()

= Acknowledgments
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

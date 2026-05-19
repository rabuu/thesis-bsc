#import "/lib/lib.typ": *

#set heading(outlined: false)
#show heading: it => {
  pad(it, top: 1cm, bottom: 1cm)
}

= Abstract
The Sequent Calculus Compiler (SCC) is a research compiler that uses sequent-calculus-based intermediate representations to compile a functional programming language to native machine code.
Within the SCC, first-class consumer values make control flow explicit.
A continuation is a consumer that represents the remainder of a computation.
In standard functional programs, each continuation is used linearly, i.e. exactly once.
However, the SCC also supports control operators that break this linearity assumption.
This thesis describes how to statically track the linearity of continuations and exploit it to generate more efficient machine code, reducing both runtime overhead and memory usage.
To achieve that, the memory allocation mechanisms are extended for linear data.
In this work, these improvements are only applied specifically to continuations, but serve as a foundation for more general use cases.

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

#import "/lib/lib.typ": *

#set heading(outlined: false)
#show heading: it => {
  pad(it, top: 1cm, bottom: 1cm)
}

= Abstract
The Sequent Calculus Compiler (SCC) uses sequent-calculus-based intermediate representations to compile a functional programming language to native machine code.
Within the SCC, control flow is explicitly encoded using consumers.
A continuation is a consumer that represents the remainder of a computation.
In standard functional programs, each continuation is used linearly, i.e. exactly once.
However, the SCC also supports control operators that break this linearity assumption.
This thesis investigates how to statically track the linearity of continuations and exploit it to generate more efficient machine code, reducing both runtime overhead and memory usage.
To achieve that, the memory allocation mechanisms are extended for linear usage of data.
In this work, these improvements are only applied specifically to continuations, but serve as a foundation for more general use cases.

#pagebreak()

#[
  #set text(lang: "de")

  = Zusammenfassung
  Der Sequent Calculus Compiler (SCC) nutzt Zwischenrepräsentationen, die auf dem Sequenzenkalkül basieren, um eine funktionale Programmiersprache in nativen Maschinencode zu übersetzen.
  Im SCC wird der Kontrollfluss explizit durch sogenannte Consumer kodiert.
  Eine Continuation ist ein Consumer, der den Rest einer Berechnung repräsentiert.
  In einem normalen funktionalen Programm wird jede Continuation linear verwendet, also genau einmal.
  Der SCC unterstützt jedoch auch Kontrolloperatoren, die dieser Linearitätsannahme widersprechen.
  Diese Arbeit untersucht, wie sich die Linearität von Continuations statisch nachverfolgen lässt und wie sie zur Generierung effizienteren Maschinencodes genutzt werden kann,
  um sowohl Laufzeit-Overhead als auch Arbeitsspeicherverbrauch zu reduzieren.
  Dazu werden die Speicherallokationsmechanismen für den Gebrauch von linearen Daten erweitert.
  In dieser Arbeit werden diese Optimierungen zunächst nur für Continuations umgesetzt, sie bilden jedoch eine Grundlage für weitergehende Anwendungen.
]

#pagebreak-to()

= Acknowledgments
#todo[thank you]

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

#outline(depth: 2)

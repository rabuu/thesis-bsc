#import "/lib/lib.typ": *

#set heading(outlined: false)
#show heading: it => {
  pad(it, top: 1cm, bottom: 1cm)
}

= Abstract
The Sequent Calculus Compiler (SCC) compiles a functional programming language to machine code using intermediate representations based on the sequent calculus.
Within the SCC, control flow is made explicit by representing continuations as first-class values.
This enables expressive handling of complex control flow, but requires a memory management strategy general enough to support arbitrary continuation usage.
However, in many functional programs control flow is simple: continuations are linear, i.e. invoked exactly once.
This thesis investigates how programs with only linear continuations can be compiled into more efficient code by eliminating unnecessary memory management operations.
Benchmarks show that this optimization measurably reduces runtime overhead,
with the largest improvements for programs dominated by frequent function calls.

#pagebreak()

#[
  #set text(lang: "de")

  = Zusammenfassung
  Der Sequent Calculus Compiler (SCC) übersetzt eine funktionale Programmiersprache in Maschinencode,
  wobei Zwischendarstellungen verwendet werden, die auf dem Sequenzenkalkül basieren.
  Im SCC wird Kontrollfluss explizit, indem Continuations direkt als Werte repräsentiert werden.
  Das ermöglicht eine flexible Darstellung von komplexem Kontrollfluss,
  erfordert jedoch eine Speicherverwaltungsstrategie, die allgemein genug ist,
  um beliebige Verwendung von Continuations zu unterstützen.
  Allerdings ist in vielen funktionalen Programmen der Kontrollfluss einfach:
  Continuations sind linear, das heißt, sie werden genau einmal aufgerufen.
  In dieser Arbeit wird untersucht, wie Programme mit ausschließlich linearen Continuations zu effizienterem Code kompiliert werden können,
  indem unnötige Speicherverwaltungsoperationen eliminiert werden.
  Benchmarks zeigen, dass diese Optimierung den Laufzeit-Overhead messbar reduziert,
  wobei die größten Verbesserungen bei Programmen mit häufigen Funktionsaufrufen auftreten.
]

#pagebreak-to()

= Acknowledgments
I would like to thank Philipp Schuster, Marius Müller, and Tim Süberkrüb for suggesting this topic, for the opportunity to work on it as my thesis, and for the great help throughout the entire process.

I am also very grateful for the support from my family and friends, during this thesis and in general.
Special thanks go to Leander and Annika!

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

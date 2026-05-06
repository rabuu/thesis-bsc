#import "@preview/touying:0.7.3": *
#import themes.metropolis: *

#import "/lib/lib.typ": syntax
#import syntax: *

#import "@preview/codly:1.3.0": *
#show: codly-init

#let codly-languages = (
  fun: (name: "Fun", color: red),
  core: (name: "Core", color: green),
  axcut: (name: "AxCut", color: blue),
)

#codly(
  languages: codly-languages,
  zebra-fill: none,
)

#show: metropolis-theme.with(
  config-info(
    title: [Linear Continuations in the Sequent-Calculus-Compiler],
    subtitle: [Bachelor's Thesis: Initial Presentation],
    author: [Rasmus Buurman],
    date: [06.05.2026],
  ),
)

#show raw: set raw(syntaxes: (
  "misc/sublime/fun.sublime-syntax",
  "misc/sublime/core.sublime-syntax",
  "misc/sublime/axcut.sublime-syntax",
))

#title-slide()

= Introduction

== Sequent-Calculus-Compiler Overview

#slide[
  #figure(image("assets/initial-presentation/scc-overview.png", width: 100%))
]

== Linear Continuations
#slide(composer: (1fr, 1.2fr))[
  ```fun
  def f(x: i64): i64 {
      if x < 0 {
          0
      } else {
          x
      }
  }
  ```
][
  #pause
  ```core
  def f(x: prd i64, k: cns i64) {
      if x < 0 {
          ⟨0 | k⟩
      } else {
          ⟨x | k⟩
      }
  }
  ```
]

== Non-Linear Continuations

#slide(composer: (1fr, 1.2fr))[
  ```fun
  def f(α: cns i64): i64 {
      goto α (0)
  }

  def g(): i64 {
      label α { f(α) }
  }
  ```
][
  #pause
  ```core
  def f(α: cns i64, k: cns i64) {
      ⟨0 | α⟩
  }

  def g(k: cns i64) {
      ⟨μα.f(α, α) | k⟩
  }
  ```
]

== What Is the Thesis About?

#slide[
  + Statically tracking linear continuations through all compiler stages

    #v(1em)

  + Optimize the generated machine code

    #v(1em)

  + Profit
]

#show heading.where(level: 1): set heading(numbering: "1.")
= Tracking Quantities

== Example: Fibonacci (Fun)

#slide[
  ```fun
  def fib(n: i64): i64 {
      if n == 0 {
          0
      } else {
          if n == 1 {
              1
          } else {
              fib(n - 1) + fib(n - 2)
          }
      }
  }
  ```
]

== Example: Fibonacci (Core)

#slide[
  #codly(highlights: (
    (line: 1, start: 31, end: 31, fill: orange),
    (line: 8, start: 18, end: 21, fill: orange),
    (line: 8, start: 42, end: 46, fill: orange),
  ))
  ```core
  def fib(n: prd ω i64, k: cns 1 i64) {
      if n == 0 {
          ⟨0 | k⟩
      } else {
          if n == 1 {
              ⟨1 | k⟩
          } else {
              ⟨(μ1α.fib(n - 1, α)) + (μ1β.fib(n - 2, β)) | k⟩
          }
      }
  }
  ```
]

== Example: Fibonacci (AxCut)

#slide[
  #codly(highlights: (
    (line: 2, start: 1, end: 10, fill: orange),
    (line: 4, start: 5, end: 14, fill: orange),
  ))
  ```axcut
  substitute (n2 := n), (k := k), (n1 := n);
  create1 α = (k, n1) { (s1: ext i64) =>
      substitute (n1 := n1), (k := k), (s1 := s1);
      create1 β = (k, s1) { (s2: ext i64) =>
          sum ← s1 + s2;
          substitute (sum := sum), (k := k);
          invoke k (sum)
      };
      lit p3 ← 2;
      p4 ← n - p3;
      substitute (p4 := p4), (β := β);
      fib(p4, β)
  };
  ```
]

= Optimizing Code Generation

== Memory Management in SCC

#slide[
  - no stack

    #v(1em)

  - constant-sized memory blocks on the heap

    #v(1em)

  - reference counting (in constant-time)
]

== Memory Layout: Memory Block

#slide[
  #figure(image("assets/initial-presentation/codegen/layout1.png", width: 80%))
]

== Advantages of Linearity

#slide[
  Oberservation: there's always exactly one reference to a linearly used memory block

  $==>$ we don't have to care about reference counting

  #v(1em)

  Advantages:

  - more space in memory

  - less instructions

  #v(1em)

  Challenges:

  - storing to & loading from memory gets more complex
]

#show heading.where(level: 1): set heading(numbering: none)
= Conclusion

== Thesis Goals

- Formalizing the "quantity tracking"

  - Extending the intermediate representations

  - Extending the type systems & type safety proofs

  #v(2em)

- Formal translation from AxCut to RISC-V

  #v(2em)

- Implementation

  - Only one target backend: x86-64

== Preliminary Benchmark

`Fib` benchmark with prototype:
#figure(
  align(center)[
    #table(
      columns: 5,
      align: (left, right, right, right, right),
      table.header(
        [Command],
        [Mean \[s\]],
        [Min \[s\]],
        [Max
          \[s\]],
        [Relative],
      ),
      table.hline(),
      [`fib_lin  5 39`], [3.133 ± 0.014], [3.116], [3.161], [1.00],
      [`fib_main 5 39`], [3.514 ± 0.012], [3.499], [3.541], [1.12 ± 0.01],
    )],
)

$==>$ 12% faster

== Future Work / Stretch Goals

- Make full use of linear memory management

  - The backend infrastructure (storing & loading) is already there

  - Needs some "linearity detection"

#v(2em)

- Supporting more backends in the implementation

#show: appendix

= Bonus Slides: Store

== Memory Layout: Free List

#slide[
  #figure(image("assets/initial-presentation/codegen/freelist1.png"))
]

== Memory Layout: Heap

#slide(composer: (auto, 1fr))[
  #set align(top)
  #v(1.8em)
  Registers:
][
  #figure(image("assets/initial-presentation/codegen/heap.png"))
]

== Storing a Non-Linear Block

#slide[
  #figure(image("assets/initial-presentation/codegen/store/store1.png"))
]
#slide[
  #figure(image("assets/initial-presentation/codegen/store/store2.png"))
]
#slide[
  #figure(image("assets/initial-presentation/codegen/store/store3.png"))
]
#slide[
  #figure(image("assets/initial-presentation/codegen/store/store4.png"))
]

== Modifying the Memory Layout (Before)

#slide[
  free list:
  #figure(image(
    "assets/initial-presentation/codegen/freelist1.png",
    height: 50%,
  ))

  #v(1fr)
  #line(length: 100%)
  #v(1fr)

  memory block in use:
  #figure(image(
    "assets/initial-presentation/codegen/layout1.png",
    height: 11%,
  ))
]

== Modifying the Memory Layout (After)

#slide[
  free list:
  #figure(image(
    "assets/initial-presentation/codegen/freelist2.png",
    height: 50%,
  ))

  #v(1fr)
  #line(length: 100%)
  #v(1fr)

  memory block in use:
  #figure(image(
    "assets/initial-presentation/codegen/layout2.png",
    height: 11%,
  ))
]

== Storing a Linear Block

#slide[
  #figure(image("assets/initial-presentation/codegen/store1/store1.png"))
]
#slide[
  #figure(image("assets/initial-presentation/codegen/store1/store2.png"))
]
#slide[
  #figure(image("assets/initial-presentation/codegen/store1/store3.png"))
]
#slide[
  #figure(image("assets/initial-presentation/codegen/store1/store4.png"))
]
#slide[
  #figure(image("assets/initial-presentation/codegen/store1/store5.png"))
]
#slide[
  #figure(image("assets/initial-presentation/codegen/store1/store6.png"))
]


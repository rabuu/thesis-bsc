#import "@preview/touying:0.7.3": *
#import themes.metropolis: *

#import "/lib/lib.typ": *
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
#slide(composer: (1fr, 1.4fr))[
  ```fun
  def f(x: i64): i64 {
      if x < 0 {
          0
      } else {
          x
      }
  }

  def g(x: i64): i64 {
      f(2)
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

  def g(x: prd i64, k: cns i64) {
      f(2, k)
  }
  ```
]

== Non-Linear Continuations

#slide[
  ```fun
  def f(x: i64,
        α: cns i64): i64 {
      if x == 0 {
          goto α (x)
      } else {
          x
      }
  }

  def g(): i64 {
      label α { f(1, α) }
  }
  ```
][
  #pause
  ```core
  def f(x: prd i64,
        α: cns i64, k: cns i64) {
      if x == 0 {
          ⟨x | α⟩
      } else {
          ⟨x | k⟩
      }
  }

  def g(k: cns i64) {
      ⟨μα.f(1, α, α) | k⟩
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

== Sequent-Calculus-Compiler Overview, Actually

#slide[
  #alternatives[
    #figure(image("assets/initial-presentation/scc-overview.png", width: 100%))
  ][
    #figure(image("assets/initial-presentation/scc-overview2.png", width: 100%))
  ]
]

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
    (line: 1, start: 21, end: 21, fill: orange),
    (line: 8, start: 18, end: 20, fill: orange),
    (line: 8, start: 42, end: 44, fill: orange),
  ))
  ```core
  def fib(n: prd i64, k: cns i64) {
      if n == 0 {
          ⟨0 | k⟩
      } else {
          if n == 1 {
              ⟨1 | k⟩
          } else {
              ⟨(μα.fib(n - 1, α)) + (μβ.fib(n - 2, β)) | k⟩
          }
      }
  }
  ```
]

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

== Example: Fibonacci (Focusing)

#slide[
  #codly(highlights: (
    (line: 8, start: 15, fill: orange),
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

#slide(composer: (1fr, 1.5fr))[
  #codly(highlights: (
    (line: 2, start: 5, end: 8, fill: orange),
    (line: 4, start: 5, end: 8, fill: orange),
  ))
  ```core
  ⟨
    (μ1α.fib(n - 1, α))
    +
    (μ1β.fib(n - 2, β))
  | k⟩
  ```
][
  #pause
  #codly(highlights: (
    (line: 1, start: 4, end: 8, fill: orange),
    (line: 6, start: 8, end: 12, fill: orange),
  ))
  ```core
  ⟨μ1c1.
      ⟨1 | ​̃μp1.
          ⟨n - p1 | ​̃μp2.fib(p2, c1)⟩
      ⟩
  | ​̃μs1.
      ⟨μ1c2.
          ⟨2 | ​̃μp3.
              ⟨n - p3 | ​̃μp4.fib(p4, c2)⟩
          ⟩
      | ​̃μs2.
          ⟨s1 + s2 | k⟩
      ⟩
  ⟩
  ```
]

== Example: Fibonacci (AxCut)

#slide(composer: (1fr, 1.3fr))[
  #set text(size: 15pt)
  #codly(highlights: (
    (line: 1, start: 4, end: 8, fill: orange),
    (line: 6, start: 8, end: 12, fill: orange),
  ))
  ```core
  ⟨μ1c1.
      ⟨1 | ​̃μp1.
          ⟨n - p1 | ​̃μp2.fib(p2, c1)⟩
      ⟩
  | ​̃μs1.
      ⟨μ1c2.
          ⟨2 | ​̃μp3.
              ⟨n - p3 | ​̃μp4.fib(p4, c2)⟩
          ⟩
      | ​̃μs2.
          ⟨s1 + s2 | k⟩
      ⟩
  ⟩
  ```
][
  #set text(size: 15pt)
  #pause
  #codly(highlights: (
    (line: 2, start: 1, end: 10, fill: orange),
    (line: 4, start: 5, end: 14, fill: orange),
  ))
  ```axcut
  substitute (n2 := n), (k := k), (n1 := n);
  create1 c1 = (k, n1) { (s1: ext i64) =>
      substitute (n1 := n1), (k := k), (s1 := s1);
      create1 c2 = (k, s1) { (s2: ext i64) =>
          sum ← s1 + s2;
          substitute (sum := sum), (k := k);
          invoke k (sum)
      };
      lit p3 ← 2;
      p4 ← n - p3;
      substitute (p4 := p4), (c2 := c2);
      fib(p4, c2)
  };
  lit p1 ← 1;
  p2 ← n - p1;
  substitute (p2 := p2), (c1 := c1);
  fib(p2, c1)
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

  #v(2em)

  Advantages:

  - more space in memory

  - less instructions
]

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

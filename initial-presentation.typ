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

= Background

== Sequent-Calculus-Compiler Overview

#slide[
  #figure(image("assets/initial-presentation/scc-overview.png", width: 100%))
]

== What Is a Continuation?
#slide(composer: (1fr, 1.2fr))[
  ```fun
  def sq(x: i64): i64 {
      x * x
  }

  def foo(): i64 {
      let r: i64 = sq(2);
      println(r);
      r
  }
  ```
][
  #pause
  #codly(languages: (fun: (name: "CPS")))
  ```fun
  def sq(x: i64, k: i64 → ⊥) {
      k(x * x)
  }

  def foo(k: i64 → ⊥) {
      sq(2, λr =>
              println(r);
              k(r))
  }
  ```
  #codly(languages: codly-languages)
]

#slide(composer: (1fr, 1.1fr))[
  #codly(languages: (fun: (name: "CPS")))
  ```fun
  def sq(x: i64, k: i64 → ⊥) {
      k(x * x)
  }

  def foo(k: i64 → ⊥) {
      sq(2, λr =>
              println(r);
              k(r))
  }
  ```
  #codly(languages: codly-languages)
][
  #pause
  ```core
  def sq(x: prd i64, k: cns i64) {
      ⟨x * x | k⟩
  }

  def foo(k: cns i64) {
      sq(2, ​̃μr.
              println(r);
              ⟨r | k⟩)
  }
  ```
]

== Non-Linear Continuations

#slide[
  ```fun
  def foo(x: i64,
          α: cns i64): i64 {
      if x == 0 {
          goto α (x)
      } else {
          x
      }
  }

  def bar(): i64 {
      label α { foo(1, α) }
  }
  ```
][
  #pause
  ```core
  def foo(x: prd i64,
          α: cns i64, k: cns i64) {
      if x == 0 {
          ⟨x | α⟩
      } else {
          ⟨x | k⟩
      }
  }

  def bar(k: cns i64) {
      ⟨μα.foo(1, α, α) | k⟩
  }
  ```
]

== What Is the Thesis About?

#slide[
  + Statically tracking linear continuations through all compiler stages

    #pause
    #v(1em)

  + Optimize the generated machine code

    #pause
    #v(1em)

  + Profit
]

#show heading.where(level: 1): set heading(numbering: "1.")
= Tracking Quantities in the Type System

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
  #alternatives[
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
  ][
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
  ][
    #codly(highlights: (
      (line: 1, start: 16, end: 16, fill: orange),
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
]

== Sequent-Calculus-Compiler Overview, Actually

#slide[
  #alternatives[
    #figure(image("assets/initial-presentation/scc-overview.png", width: 100%))
  ][
    #figure(image("assets/initial-presentation/scc-overview2.png", width: 100%))
  ]
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
  ```core
  ⟨
    (μα.fib(n - 1, α))
    +
    (μβ.fib(n - 2, β))
  | k⟩
  ```
][
  #pause
  ```core
  ⟨μc1.
      ⟨1 | ​̃μp1.
          ⟨n - p1 | ​̃μp2.fib(p2, c1)⟩
      ⟩
  | ​̃μs1.
      ⟨μc2.
          ⟨2 | ​̃μp3.
              ⟨n - p3 | ​̃μp4.fib(p4, c2)⟩
          ⟩
      | ​̃μs2.
          ⟨s1 + s2 | k⟩
      ⟩
  ⟩
  ```
]

#slide(composer: (1fr, 1.5fr))[
  #codly(highlights: (
    (line: 2, start: 5, end: 7, fill: orange),
    (line: 4, start: 5, end: 7, fill: orange),
  ))
  ```core
  ⟨
    (μα.fib(n - 1, α))
    +
    (μβ.fib(n - 2, β))
  | k⟩
  ```
][
  #codly(highlights: (
    (line: 1, start: 4, end: 7, fill: orange),
    (line: 6, start: 8, end: 11, fill: orange),
  ))
  ```core
  ⟨μc1.
      ⟨1 | ​̃μp1.
          ⟨n - p1 | ​̃μp2.fib(p2, c1)⟩
      ⟩
  | ​̃μs1.
      ⟨μc2.
          ⟨2 | ​̃μp3.
              ⟨n - p3 | ​̃μp4.fib(p4, c2)⟩
          ⟩
      | ​̃μs2.
          ⟨s1 + s2 | k⟩
      ⟩
  ⟩
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
  ```core
  ⟨μc1.
      ⟨1 | ​̃μp1.
          ⟨n - p1 | ​̃μp2.fib(p2, c1)⟩
      ⟩
  | ​̃μs1.
      ⟨μc2.
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
  ```axcut
  substitute (n2 := n), (k := k), (n1 := n);
  create c1 = (k, n1) { (s1: ext i64) =>
      substitute (n1 := n1), (k := k), (s1 := s1);
      create c2 = (k, s1) { (s2: ext i64) =>
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

#slide(composer: (1fr, 1.3fr))[
  #set text(size: 15pt)
  #codly(highlights: (
    (line: 1, start: 4, end: 7, fill: orange),
    (line: 6, start: 8, end: 11, fill: orange),
  ))
  ```core
  ⟨μc1.
      ⟨1 | ​̃μp1.
          ⟨n - p1 | ​̃μp2.fib(p2, c1)⟩
      ⟩
  | ​̃μs1.
      ⟨μc2.
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
  #codly(highlights: (
    (line: 2, start: 1, end: 9, fill: orange),
    (line: 4, start: 5, end: 13, fill: orange),
  ))
  ```axcut
  substitute (n2 := n), (k := k), (n1 := n);
  create c1 = (k, n1) { (s1: ext i64) =>
      substitute (n1 := n1), (k := k), (s1 := s1);
      create c2 = (k, s1) { (s2: ext i64) =>
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

== Advantages of Linearity

#slide[
  Oberservation: there's always exactly one reference to a linearly used memory block

  $-->$ we don't have to care about reference counting

  #v(2em)

  Advantages:

  - more space in memory

  - less instructions
]

== Memory Layout: Memory Block

#slide[
  #alternatives[
    #figure(image("assets/initial-presentation/codegen/block.png", width: 80%))
  ][
    #figure(image(
      "assets/initial-presentation/codegen/layout1.png",
      width: 80%,
    ))
  ]
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
  #alternatives[
    #figure(image("assets/initial-presentation/codegen/store/store1.png"))
  ][
    #figure(image("assets/initial-presentation/codegen/store/store2.png"))
  ][
    #figure(image("assets/initial-presentation/codegen/store/store3.png"))
  ][
    #figure(image("assets/initial-presentation/codegen/store/store4.png"))
  ]
]

== Modifying the Memory Layout

#slide[
  memory block in use:
  #alternatives[
    #figure(image(
      "assets/initial-presentation/codegen/layout1.png",
      height: 11%,
    ))
  ][
    #figure(image(
      "assets/initial-presentation/codegen/layout2.png",
      height: 11%,
    ))
  ]

  #v(1fr)
  #line(length: 100%)
  #v(1fr)

  free list:
  #alternatives[
    #figure(image(
      "assets/initial-presentation/codegen/freelist1.png",
      height: 50%,
    ))
  ][
    #figure(image(
      "assets/initial-presentation/codegen/freelist2.png",
      height: 50%,
    ))
  ]
]

== Storing a Linear Block

#slide[
  #alternatives[
    #figure(image("assets/initial-presentation/codegen/store1/store1.png"))
  ][
    #figure(image("assets/initial-presentation/codegen/store1/store2.png"))
  ][
    #figure(image("assets/initial-presentation/codegen/store1/store3.png"))
  ][
    #figure(image("assets/initial-presentation/codegen/store1/store4.png"))
  ][
    #figure(image("assets/initial-presentation/codegen/store1/store5.png"))
  ][
    #figure(image("assets/initial-presentation/codegen/store1/store6.png"))
  ]
]

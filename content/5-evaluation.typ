#import "/lib/lib.typ": *

= Evaluation <ch:eval>
This chapter evaluates the impact of the compiler optimization presented in @ch:lin and @ch:codegen.
The evaluation focuses primarily on execution time, while other metrics are discussed only briefly.
To quantify the effect of the optimization,
we compare programs compiled using a version of the compiler that incorporates the optimizations presented in this thesis
against programs compiled using the unmodified compiler.

== Experimental Setup

=== Implementation
The SCC has a Rust #footnote(link("https://rust-lang.org")) implementation @Mueller2026scc.
The optimization was implemented as an extension of the original compiler, within the same project.
This ensures that all differences in measurements result from the optimization alone.

At the time of writing, the optimization is implemented exclusively for the x86-64 backend.
Consequently, all experiments presented in this chapter target only x86-64 code generation.
The backend emits x86-64 instructions that closely mirror the #RISC-V translation presented in this thesis.
The resulting assembly is compiled to object code by the Yasm Assembler #footnote(link("https://github.com/yasm/yasm"))
and linked with a small C driver and runtime that handles command-line arguments, memory allocation, and console output.

=== Benchmark Suite
To evaluate the optimization, we compare the performance of the unoptimized and optimized compiler on a collection of benchmark programs written in #Fun.
We use the original benchmark suite provided by the SCC project @Mueller2026sccbench,
which in turn draws many of its programs from the Manticore #footnote(link("https://github.com/ManticoreProject/benchmark")) and NoFib @Partain1993nofib suites.

Since the optimization only applies to programs without control operators, benchmarks that use $LABEL$ or $GOTO$ were excluded.
All remaining benchmarks are therefore programs to which the optimization applies.

In total, we evaluate the optimization on 30 programs of different sizes that use a variety of language features.
All benchmark programs are listed in @tab:bench:descr along with a short description @Mueller2026[ sec. 9].

#figure(
  caption: [Benchmark programs used for evaluation. @Mueller2026[ sec. 9]],
  table(
    columns: 3,
    align: (left, left, left),
    table.header([Benchmark], [Arguments], [Description]),
    `Ack`, [4, 3, 10], [The Ackermann function],
    `Boyer`, [2, 9], [The Boyer constraint solver],
    `Constraints`, [1, 6], [Tolmach and Nordin's constraint solver],
    `Cryptarithm1`, [1, 1], [Cryptarithm solver],
    `Deriv`, [1000000, 5, 7], [Symbolic differentiation],
    `Divrec`, [1000, 20000], [Recursively calculates division by 2],
    `EraseUnused`, [1, 10000], [Calculates $N$ by allocating linked lists],
    `Evenodd`, [10, 20000000], [Recursively calculates if input is even/odd],

    `FactorialAccumulator`,
    [1, 10000000],
    [Calculates the factorial with a constant],

    `Fib`, [1, 39], [Calculates Fibonacci numbers],
    `TailFib`, [10000000, 44], [`Fib` using tail recursion],
    `Fish`, [150], [Generates lines for a fractal],
    `Gcd`, [10, 400], [Calculates the greatest common divisor],
    `Integer`, [1, 4500001], [Integer operations $(*, +, ...)$ on ranges],

    `IterateIncrement`,
    [1, 100000000],
    [Computes $N$ using higher-order functions],

    `Lcss`, [400], [Hirschberg’s LCSS algorithm],
    `Life`, [1, 800], [Simulates the Game of Life],
    `LookupTree`, [1, 10000000], [Calculates $N$ by creating a binary tree],
    `Motzkin`, [1, 20], [Calculates Motzkin numbers],
    `MatchOptions`, [1, 10000000], [Computes $N$ using pattern matches],
    `Merge`, [500, 50000], [Creates two lists and merges them],
    `Minimax`, [1], [Solves Tic-Tac-Toe using Minimax],
    `Nqueens`, [1, 11], [Solves the Nqueens problem],
    `Perm`, [1, 3, 9], [Calculates permutations of lists],
    `Primes`, [10, 20000], [Implements the Sieve of Eratosthenes],
    `Sudan`, [1000000, 2, 2, 2], [Calculates the Sudan function],
    `SumRange`, [1, 10000000], [Sums a range of numbers],
    `Tak`, [1000, 21, 20, 11], [Calculates the Takeuchi function],
    `Takl`, [100, 21, 20, 11], [`Tak` using lists to encode natural numbers],
    `Cpstak`, [100, 21, 20, 11], [CPS-transformed Tak],
  ),
) <tab:bench:descr>

=== Measurements
All experiments were conducted on a machine with an AMD Ryzen 7 3800X processor running Debian 13.
Execution times were measured with the `hyperfine` #footnote(link("https://github.com/sharkdp/hyperfine")) tool,
which for each benchmark performs three warmup runs and then reports the mean runtime and standard deviation over ten executions.

== Results
#figure(
  image("/resources/benchmarks/runtime.svg"),
)

== Discussion

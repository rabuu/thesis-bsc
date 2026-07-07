#import "/lib/lib.typ": *

= Evaluation <ch:eval>
This chapter evaluates the impact of the compiler optimization presented in @ch:lin and @ch:codegen.
The evaluation focuses exclusively on execution time;
other aspects affected by the optimization like codesize and memory usage are likely to improve as well, but are not evaluated here.
To quantify the effect on performance,
we compare programs compiled using a version of the compiler that incorporates the optimization presented in this thesis
against programs compiled using the unmodified compiler.

== Experimental Setup

=== Implementation
The SCC has a Rust #footnote(link("https://rust-lang.org")) implementation @Mueller2026scc.
The optimization was implemented as an extension of the original compiler, within the same project.
For the evaluation, this ensures that the effect of the optimization is isolated from unrelated implementation details.

At the time of writing, the optimization is implemented only for the x86-64 backend,
so all measurements in this chapter are limited to that backend.
The compiler emits x86-64 instructions that closely mirror the #RISC-V translation presented in this thesis.
The resulting assembly is compiled to object code by the Yasm Assembler #footnote(link("https://github.com/yasm/yasm"))
and linked with a small C driver and runtime that handles command-line arguments, memory allocation, and console output.

=== Benchmark Suite
To evaluate the optimization, we compare the performance of the unoptimized and optimized compiler on a collection of benchmark programs written in #Fun.
We use the original benchmark suite provided by the SCC project @Mueller2026sccbench,
which in turn draws many of its programs from the Manticore #footnote(link("https://github.com/ManticoreProject/benchmark")) and NoFib @Partain1993nofib suites.

We do not include benchmark programs using $LABEL$ and $GOTO$ since the optimization does not apply to programs with control operators.
For all included benchmarks, the optimization causes changes to the generated code.

In total, we evaluate the optimization on 30 programs of different sizes that use a variety of language features.
All benchmark programs are listed in @tab:bench:descr along with a short description.

#figure(
  caption: [Benchmark programs used for evaluation, from @Mueller2026[ sec. 9].],
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
which for each benchmark performs three warmup runs and then reports the mean execution time and standard deviation over ten executions.

=== Limitations
Since all measurements were taken on a single machine using the x86-64 backend, results may differ on other hardware and architectures.
Also, the benchmark suite, while diverse, consists of relatively short-running programs;
the optimization's effect on long-running, "real-world" applications remains untested.

== Results
#figure(
  caption: [Execution time comparison of the baseline and optimized compiler output.],
  image("/resources/benchmarks/runtime.svg"),
) <fig:eval:results>

@fig:eval:results shows the execution time of each benchmark for the baseline and optimized compiler, sorted by relative speedup.
The exact measurements for all benchmarks are provided in @app:bench.

== Discussion
The optimization's impact varies considerably from one program to another.
Averaged across all 30 benchmarks, it yields a geometric mean speedup of approximately #todo[TODO].

For 15 benchmarks, the optimization achieves a significant speedup of more than 5%;
for 11 benchmarks, it yields only a small speedup of less than 5%, or none at all;
and for the remaining 4 benchmarks, the measurements show minor regressions of less than 3%.

The regressions are small and lie within the range of measurement noise,
as indicated by their standard deviations,
so they are not considered a genuine slowdown introduced by the optimization.

The largest gains occur in benchmarks dominated by deep or frequent recursive #box[calls:]
`Ack` (35%), `IterateIncrement` (18%), `Boyer` (14%), `Tak` (14%), `Takl` (13%).
Here, `Ack` stands out as a clear outlier, achieving a speedup nearly twice that of the next-best benchmark,
which suggests that its recursive structure benefits especially strongly from the optimization.

Benchmarks with only small or no speedup tend to feature comparatively fewer function or method calls,
so less time is spent on executing code affected by the optimization.

In summary, the results indicate an overall positive effect of the optimization.
On average, the improvement is moderate, but for recursion-heavy programs, the speedups are substantial.

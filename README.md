# Linear-programming foundations

Lax submission **lax-109476**. This is a local submission draft prepared for
use as a dependency of algorithmic mathematics, particularly the
Leighton–Rao multicommodity-flow results.

The primal convention is maximization with `Ax ≤ b` and `x ≥ 0`; its dual
minimizes `bᵀy` with `Aᵀy ≥ c` and `y ≥ 0`. Dimensions may be zero.
Coefficient data can be real or rational. Rational programs are optimized
over real variables, with rational output certificates.

## Contents and proof status

| Result | Supplied proof | Assumptions from this submission |
| --- | --- | --- |
| Weak duality | Finite bilinear sum and inequality calculation | None |
| Complementary slackness | Nonnegative summands of the duality gap | None |
| Farkas certificate soundness | Contradiction from a nonnegative bilinear sum | None |
| Farkas alternative | Combine existence and soundness | Farkas certificate existence; certificate soundness |
| Optimal dual multipliers | Apply Farkas to the multiplier system; contradict primal optimality | Farkas certificate existence; weak duality |
| Strong duality | Obtain an attained primal optimizer and matching multipliers | Primal attainment; optimal dual multipliers |
| Improving-direction soundness | Move beyond any proposed bound along a feasible ray | None |
| Rational certificate soundness | Cast exact checks into the reals and verify all three outcomes | Weak duality; Farkas soundness; improving-direction soundness |
| Certified polynomial-time optimization | Reuse the solver's output and apply soundness | Exact polynomial-time solver; rational certificate soundness |

Four proof obligations remain open: Farkas certificate existence, primal
attainment, polynomial-size rational certificate existence, and the exact
polynomial-time solver. Conditional proofs preserve these dependencies;
they do not claim that the foundations or solver have been proved.

## Exact computation

Each rational is encoded by three natural numbers: a sign bit, the absolute
numerator, and the positive denominator of its canonical reduced form.
Program encodings start with the numbers of rows and columns, followed by
the row-major matrix, row bounds, and objective coefficients. Certificate
encodings begin with a status tag and the relevant rational vectors.

An optimality certificate carries matching primal and dual feasible points.
An infeasibility certificate carries nonnegative Farkas multipliers. An
unboundedness certificate carries both a feasible base point and a
nonnegative improving recession direction. Every output inequality is
checked over the rationals; the soundness theorem establishes its meaning
for real optimization.

The runtime claim is `Lax759944.RamPolytime.RamPolytime`, which uses the
binary encoding size, polynomial word-size and instruction bounds, and one
uniform RAM program. It refers to the existing registered
`Lax808846.Ram` machine semantics. It does not assume unit-cost exact
rational arithmetic or polynomial time merely in the number of variables.
Malformed word-list inputs impose no mathematical LP output requirement;
the computation predicate still requires a total polynomial-time function.

Pinned archive dependencies:

| Package | Repository | Revision | Subdirectory |
| --- | --- | --- | --- |
| Lax759944 | https://github.com/szymtor/RAM-TM | `134e398cef46599371df99f10c9007bc34ba3868` | `concepts` |
| Lax808846 (transitive) | https://github.com/lax-archive/lax-submissions | `9394e531cc51cb67a0214bca3f9264dfe97ba5c7` | `word-ram/concepts` |

Lean is pinned to `v4.33.0` and mathlib to
`db584cd6d46c92f209a44c0f1c829460d327499d`.

## Build and preview

Run `lax build --replay` from this directory to validate the concepts,
extract the kernel assumptions of each proof, and replay the proof checks.
Run `lax serve . --port 8124` for a local preview.

## Sources and use by Leighton–Rao

The mathematical foundations follow Alexander Schrijver's *Theory of
Linear and Integer Programming* (1986), particularly the duality and
rational-polyhedron results. The polynomial-time solvability claim is the
classical rational LP theorem originating with
[Khachiyan (1979)](https://www.mathnet.ru/eng/dan42319), with exact outcome
certificates. No ellipsoid implementation is included.

This submission supplies generic LP foundations. A multicommodity-flow
submission still needs to express its own LP, establish the correspondence
between LP points and graph flows or metrics, account for the size of the
LP representation, and connect constructive rounding to RAM computation.
The potentially exponential path formulation alone does not establish a
polynomial-time flow algorithm; it must be replaced by a polynomial-size
formulation or paired with a proved separation/reduction argument.

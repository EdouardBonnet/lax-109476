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
| Fourier–Motzkin elimination | Nonnegative row combinations and finite compatible bounds | None |
| Farkas certificate existence | Induct on variables after adding nonnegativity rows | Fourier–Motzkin elimination |
| Weak duality | Finite bilinear sum and inequality calculation | None |
| Complementary slackness | Nonnegative summands of the duality gap | None |
| Farkas certificate soundness | Contradiction from a nonnegative bilinear sum | None |
| Farkas alternative | Combine existence and soundness | Farkas certificate existence; certificate soundness |
| Optimal dual multipliers | Apply Farkas to the multiplier system; contradict primal optimality | Farkas certificate existence; weak duality |
| Primal attainment | Apply Farkas to the system attaining the finite supremum | Farkas certificate existence; Farkas soundness; weak duality |
| Strong duality | Obtain an attained primal optimizer and matching multipliers | Primal attainment; optimal dual multipliers |
| Improving-direction soundness | Move beyond any proposed bound along a feasible ray | None |
| Improving-direction existence | Apply Farkas to the normalized direction system; a contrary certificate gives a dual upper bound | Farkas certificate existence; weak duality |
| Rational feasible-point existence | Eliminate over the rationals and cast a contrary Farkas certificate into the reals | Farkas certificate soundness |
| Exact rational certificate existence | Rationalize a matching primal–dual pair or normalized direction; use rational Farkas for infeasibility | Rational feasible-point existence; strong duality; improving-direction existence |
| Rational certificate soundness | Cast exact checks into the reals and verify all three outcomes | Weak duality; Farkas soundness; improving-direction soundness |
| Polynomial RAM output size | At most one output word per instruction; bounded bit size per word | None |
| Polynomial-size rational certificates | Clear denominators, choose independent supports, and bound Gram determinants | Exact rational certificate existence |
| Exact polynomial-time solver | One fixed RAM program: ellipsoid decisions, exact recovery, and certificate output | Exact rational certificate existence |
| Certified polynomial-time optimization | Reuse the solver's output and apply soundness | Exact polynomial-time solver; rational certificate soundness |

All 18 public statements have supplied proofs. The proof network records the
public assumptions used by those proofs; internal implementation lemmas are
checked in the same proof package.

## Exact solver and ellipsoid implementation

The solver returns one of three exact rational certificates: matching primal
and dual feasible points for optimality, nonnegative Farkas multipliers for
infeasibility, or a feasible base point with an improving recession direction
for unboundedness. Certificate soundness establishes each outcome for real
optimization. Dimensions may be zero.

The implementation includes the complete rational ellipsoid feasibility
routine: central cuts, positive-definite shape updates, rational rounding,
integer-square-root approximation, containment, conditioning, determinant
contraction, separation, and finite termination. Padding handles dimensions
zero and one. Bounded feasible points and bounded Farkas multipliers justify
exact feasibility decisions through a normalized relaxation.

Exact recovery combines coordinate threshold queries, interval bisection,
and continued-fraction reconstruction. Slack-variable systems and determinant
bounds provide the required coordinate and denominator bounds. The solver
builds the three certificate systems from runtime input dimensions, selects
a feasible system, recovers its point, and emits canonical certificate words.
Its source coefficient arrays remain immutable while separate workspaces
hold the decision and recovery systems.

`RamExactSolverProgram.solve` is one fixed structured command. The proofs
cover its branching execution, accepted noncanonical rational encodings,
and termination on every logical word-list input. Malformed inputs have
no mathematical certificate requirement. `RamSolverAllocation` supplies the
initial array extents, `RamAutomaticLayout` proves a compiler layout, and
`RamUniformSolver` transfers execution to the existing registered RAM model.

The runtime predicate is `Lax759944.RamPolytime.RamPolytime`, using binary
input size, polynomial word width, and polynomial instruction bounds. The
transfer uses the existing `Lax808846.Ram` semantics and its proved compiler.
Correctness and execution bounds hold for every larger word width. Polynomial
bounds are proved for the entire program, including decoding, denominator
clearing, auxiliary queries, exact recovery, and output.

Standalone rational certificates have encoding size at most
`512 * (L + 1)^3`, where `L` is the registered binary input size. The normalized
feasibility cut budget is at most `640000 * (L + 1)^4`; the complete solver's
word and instruction bounds are the polynomials constructed in
`RamUniformSolverBounds` and `RamResourcePolynomial`.

## Encodings and validation

Each rational uses three natural words: sign, absolute numerator, and
positive denominator. Canonical encodings use reduced fractions. Program
encodings start with row and column counts, followed by the row-major
matrix, row bounds, and objective coefficients. Certificate encodings start
with an outcome tag and the corresponding rational vectors.

The proof package is checked by Lean and strict kernel replay. Compiled RAM
checks cover arithmetic, continued fractions and reconstruction, coordinate
query construction, all three certificate-system builders, zero dimensions,
and certificate output. The full solver is verified by execution and resource
proofs rather than a full native execution benchmark.

Run `lax build --replay` from this directory to check the submission and
extract its proof dependencies. Run `lax serve . --port 8124` for a local
preview.

## Pinned dependencies

| Package | Repository | Revision | Subdirectory |
| --- | --- | --- | --- |
| Lax759944 | https://github.com/szymtor/RAM-TM | `134e398cef46599371df99f10c9007bc34ba3868` | `concepts` |
| Lax808846Proofs | https://github.com/lax-archive/lax-submissions | `9394e531cc51cb67a0214bca3f9264dfe97ba5c7` | `word-ram/proofs` |
| Lax808846 (transitive) | https://github.com/lax-archive/lax-submissions | `9394e531cc51cb67a0214bca3f9264dfe97ba5c7` | `word-ram/concepts` |

Lean is pinned to `v4.33.0` and mathlib to
`db584cd6d46c92f209a44c0f1c829460d327499d`.

## Sources

The statements follow Schrijver's *Theory of Linear and Integer Programming*
(1986). Polynomial-time rational LP solvability originates with
[Khachiyan (1979)](https://www.mathnet.ru/eng/dan42319). The central-cut
calculations follow
[Goemans' ellipsoid-method lecture](https://ocw.mit.edu/courses/6-854j-advanced-algorithms-fall-2008/bc621c481eecc9cb9c645eb44538a7f3_lect9_26.pdf).

The elimination and unrestricted-variable Farkas proofs adapt
[Jyotirmoy Bhattacharya's `farkas_lean`](https://github.com/jmoy/farkas_lean)
at revision `30c319dd52ca89cfa82a68352b1f39f4f3026fc2`. The adaptation exposes
the real elimination step in the proof network and instantiates the same
elimination construction over the rationals. Adapted sources retain the
original MIT license; see [the attribution and license](THIRD_PARTY_LICENSES.md).

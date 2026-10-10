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
| Polynomial-size rational certificates | Bound the encoding of the exact solver's output | Exact polynomial-time solver; polynomial RAM output size |
| Certified polynomial-time optimization | Reuse the solver's output and apply soundness | Exact polynomial-time solver; rational certificate soundness |

The real LP duality and certificate-soundness chain is now fully proved:
the elimination proof closes Farkas' lemma, and Farkas' lemma closes primal
attainment and optimal dual multipliers, hence strong duality.
All three rational certificate outcomes also have a proved existence theorem
independent of the solver. Its proof supplies no polynomial encoding-size bound.

The exact polynomial-time solver is the remaining open foundation. The
polynomial-size certificate result and certified optimization have conditional
proofs depending on this solver. These statements remain unproved in the
network until the solver is proved. The certificate-size proof is a corollary
of polynomial output size; it is not an independent determinant-bound proof.

Finishing the solver requires a formal polynomial-time LP algorithm, exact
rational arithmetic and rounding bounds, exact certificate recovery, and
execution and runtime proofs for the registered RAM (or a proved reduction
through an equivalent computational model). Fourier–Motzkin elimination
supplies no polynomial runtime bound. No new algorithmic axiom has been
added to discharge this obligation.

Internal progress toward an ellipsoid implementation is included in
`proofs/Lax109476Proofs/EllipsoidStep.lean` and
`proofs/Lax109476Proofs/RationalRounding.lean`,
`proofs/Lax109476Proofs/EllipsoidRounding.lean`, and
`proofs/Lax109476Proofs/EllipsoidBounds.lean`. The first proves the normalized
central-cut matrix's positive definiteness, inverse, containment, and determinant
factor in dimensions at least two. It bounds the square root of that determinant
factor, allows a small uniform enlargement, and proves an iterated contraction
bound. The second defines computable rational grid rounding and an
integer-square-root approximation, proves their real error bounds, and bounds
their encodings using the registered binary-word encoding. A magnitude-based
encoding bound controls a rounded value independently of its original denominator.
The rounding module proves quadratic-form error bounds, inverse-form
antitonicity, and preservation of positive definiteness and containment after
entrywise rounding with a diagonal allowance. It also quantifies the enlargement
needed for a displaced center. The bounds module defines the rational update
for a general positive definite shape, proves its inverse, containment, determinant
factor, and conditioning bounds, and connects the update to shape rounding.
It gives an iterated conditioning bound and a dyadic precision schedule whose
denominator bit length is linear in the conditioning exponent and dimension.
These internal lemmas are not connected to a solver proof and do not make the
solver node proved. A complete rational center update and its precision schedule,
termination and feasibility bounds, exact recovery of certificates, and uniform
RAM execution remain to be formalized. The conditioning induction assumes the
per-step bounds; it does not yet verify a complete rounded iteration.

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

The mathematical statements follow Alexander Schrijver's *Theory of
Linear and Integer Programming* (1986), particularly the duality and
rational-polyhedron results. The polynomial-time solvability claim is the
classical rational LP theorem originating with
[Khachiyan (1979)](https://www.mathnet.ru/eng/dan42319), with exact outcome
certificates. The central-cut calculations follow
[Goemans' ellipsoid-method lecture](https://ocw.mit.edu/courses/6-854j-advanced-algorithms-fall-2008/bc621c481eecc9cb9c645eb44538a7f3_lect9_26.pdf).
The implementation is incomplete as described above.

The elimination and unrestricted-variable Farkas proofs adapt
[Jyotirmoy Bhattacharya's `farkas_lean`](https://github.com/jmoy/farkas_lean)
at revision `30c319dd52ca89cfa82a68352b1f39f4f3026fc2`. The adaptation
uses the Farkas induction over ordered fields, exposes the real elimination
step in the Lax proof network, and updates the proof to the pinned toolchain.
The rational instance uses the same proved elimination construction directly.
Each adapted source retains the original MIT license; see
[the attribution and license](THIRD_PARTY_LICENSES.md).

This submission supplies generic LP foundations. A multicommodity-flow
submission still needs to express its own LP, establish the correspondence
between LP points and graph flows or metrics, account for the size of the
LP representation, and connect constructive rounding to RAM computation.
The potentially exponential path formulation alone does not establish a
polynomial-time flow algorithm; it must be replaced by a polynomial-size
formulation or paired with a proved separation/reduction argument.

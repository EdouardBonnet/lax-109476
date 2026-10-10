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
| Certified polynomial-time optimization | Reuse the solver's output and apply soundness | Exact polynomial-time solver; rational certificate soundness |

The real LP duality and certificate-soundness chain is now fully proved:
the elimination proof closes Farkas' lemma, and Farkas' lemma closes primal
attainment and optimal dual multipliers, hence strong duality.
All three rational certificate outcomes have proved existence and polynomial
encoding-size bounds independent of the solver. The explicit bound is
`512 * (L + 1)^3`, where `L` is the registered binary input size.

The exact polynomial-time solver is the remaining open foundation. Certified
optimization has a conditional proof depending on this solver and remains
unproved in the network until the solver is proved.

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
solver node proved.

The additional `EllipsoidCenter`, `EllipsoidPrecision`, `EllipsoidDeterminant`,
`EllipsoidIteration`, and `EllipsoidSequence` proof modules define and verify the
complete stored rational center and shape update. A dyadic denominator handles
both center errors and the relative shape error. Relative quadratic-form bounds
imply determinant bounds, so the same rounded update both preserves the cut
portion and contracts the square-root determinant. The actual recursive shape
sequence starts at the identity and remains positive definite with lower form
bound `2^(-2k)` and upper form bound `4^k`. The center sequence preserves points
retained by the supplied cuts. At iteration `k`, the grid denominator has
`2k + 3n + 10` bits. After `4(n+1)(Bn+1)` cuts, the square-root determinant is
below the threshold `2^(-Bn)`.

The `Relaxation`, `EllipsoidBall`, `EllipsoidTermination`, `RationalSeparation`,
`EllipsoidSearch`, `NormalizedFeasibility`, `IntegerFeasibilityDecision`,
`FeasibilityPadding`, `IterationBudget`, and `RationalFeasibilityDecision`
modules connect these updates to a computable exact feasibility decision.
The separation routine scans integer rows with rational comparisons; every
nonzero selected row meets the required normal-length bound. Bounded Farkas
multipliers give a relaxation gap, and bounded feasible witnesses give a ball
inside the normalized relaxed LP. Ball containment supplies the determinant
lower bound needed for finite termination. Two dummy variables handle all
input dimensions. The cut budget is at most `640000 * (L + 1)^4`.

The `RationalReconstruction` module supplies a computable continued-fraction
scan with a proved exact interval-reconstruction guarantee. Two successive
tails halve the denominator, so the scan examines only twice the approximation's
denominator bit length. Distinct rationals with denominator at most `B` are
separated by at least `1/B²`.

The `EllipsoidStateSize` module bounds each stored shape entry by `4^k` and
each center coordinate by `2^(k+2)`. The shape and center grid representations
then bound each rational entry's registered encoding size by `60 + 6k + 14n`.
`BinaryOptimization` and `CoordinateOptimization` combine logarithmically many
threshold queries with reconstruction to recover an attained coordinate minimum
exactly, given a denominator bound. `LexicographicSupport` proves that successive
coordinate minima in standard form have independent support; `RationalMinima`
proves rational attainment of each coordinate minimum. `LexicographicMinima`
and `LexicographicBounds` give one determinant cap from the original system for
every coordinate of the selected point. `PointRecovery`, `IntegerPointRecovery`,
and `IndexedPointRecovery` implement exact point recovery, including slack
variables and explicit finite-index equivalences.

`CertificateSystems`, `CertificateSearch`, `WordDecoding`, and `WordSolver`
complete the executable recovery pipeline. The total word-list function decodes
the registered input, clears denominators, recovers primal–dual, Farkas, or
recession witnesses, checks them exactly, and encodes the resulting certificate.
Its functional correctness is proved for all dimensions and all rational inputs.
Oversized malformed dimensions are rejected before vector allocation. Search
stops at a feasible center and at the first valid certificate, without allocating
the full cut budget or evaluating later certificate systems.
The scan stores each updated matrix and center in vectors and advances the
stored state once per failed separation test.

`RationalArithmeticBounds` proves numerator and denominator bounds for exact
addition, multiplication, inversion, and finite sums, together with their
encoding bounds. `BinaryOptimizationBounds` bounds dyadic search thresholds and
reconstructed coordinates for arbitrary query answers, including unsuccessful
certificate branches. `RamArithmetic` supplies verified GCD and fraction
reduction programs, and `RamSquareRoot` supplies verified integer square root;
their costs are linear in bit length. `RamRational` verifies signed addition,
multiplication, and inversion with reduced numerators and denominators.
`RamComparison` verifies exact order comparisons, including either sign of
zero, and `RamBitLength` verifies a linear-time bit-counting loop.
`RamRounding` connects grid flooring and upper square-root approximation to
verified integer division, GCD, and square-root instructions. `RamEncoding`
verifies canonical rational output, including clearing the sign of zero.
`RamPrimitiveBounds` gives uniform costs linear in the operands' bit-length
cap, and `RamRationalArrays` verifies bounds-checked rational loads and
canonical stores using three arrays for signs, numerators, and denominators.
`RamDotProduct` verifies the full rational dot-product loop, including empty
vectors, preservation of the input arrays, and an instruction bound polynomial
in vector length and operand bit length. `RamMatrixRows` verifies row-major
slices, bounded row addresses, and matrix-row dot products. `RamSeparation`
verifies a complete scan whose numeric result is the same first violated
inequality as mathematical separation, with a polynomial instruction bound.
`RamZeroArray` verifies rational-array initialization, and `RamMatrixVector`
verifies the complete matrix-vector product used by ellipsoid updates, including
output storage reuse and a polynomial instruction bound. `RamEllipsoidForm`
verifies the stored quadratic form and its polynomial instruction bound.
`RamEllipsoidScalars` verifies the dimension factor, rational inflation factor,
the quadratic-form factors, and the dyadic precision schedule.
`RamMatrixStorage` connects flat array entries to matrix rows, and
`RamFractionInterface` exposes checked arithmetic and signed subtraction
through rational-value specifications. `RamCenterCoordinate` and
`RamCenterUpdate` verify the complete rounded center-update loop, its relation
to the mathematical ellipsoid center, and a polynomial instruction bound.
`RamShapeCoordinate` and `RamShapeUpdate` verify the full rounded shape-update
loop, including diagonal correction and inflation, its equality with the
mathematical update, and a polynomial instruction bound.
`RamEllipsoidCoefficients` verifies initialization and storage of all five
step coefficients, derives their rational height bounds, and bounds the
instruction count by a polynomial.
`RamEllipsoidUpdate` composes the center and shape loops.
`RamEllipsoidWordBounds` provides one sufficient word-capacity bound for
the whole cut, and `RamEllipsoidPrecision` verifies the precision schedule
while preserving the stored quadratic form. `RamEllipsoidStep` verifies
the complete cut body against the mathematical rounded step and proves a
polynomial instruction bound.
`RamCopy` verifies copying canonical rational arrays in linear time, preserving
the source. `RamCommitState` installs the next center and shape for the following
iteration and restores the logical dimension after copying the flattened matrix.
`RamEllipsoidStoredBounds` bounds the rational entries produced by a cut,
and `RamAdvanceState` verifies the complete cut, state installation, and
counter increment with one uniform RAM command and an explicit cost bound.
`RamEllipsoidBitBounds` gives a sufficient polynomial word width from the
dimension, coefficient bit length, and iteration number, including every larger
word width. `RamInitialState` verifies initialization of the identity shape,
zero center, and iteration counter, including empty dimensions.
`RamRowCopy` copies a selected matrix row into the normal vector with a
linear instruction bound while preserving the source matrix.
`RamTrajectoryBounds` connects the RAM update to the actual ellipsoid
trajectory and derives one word bound for every cut up to a fixed budget
from the proved global center and shape bounds.
`RamNonzero` verifies a linear scan for a nonzero rational coordinate.
`RamNormalSelection` verifies extraction of the first violated integer row
and replacement of a zero row by the fixed nonzero normal used by the trajectory.
`RecoveryArithmeticBounds` and `SolverOutputBounds` bound the coordinates
actually produced by recovery and prove the cubic size bound for the returned
certificate. `DecodingSizeBounds` proves that decoding noncanonical input
fractions cannot increase canonical input size. `WordSolverSize` gives the
cubic output-size bound on every word list and a sufficient polynomial word
width for the physical input and returned output.
`RamTransfer` proves the bridge from
bounded structured execution through Lax's verified compiler to the registered
uniform polynomial-time RAM predicate. Bounds for complete intermediate
computations and execution and runtime proofs for the
registered RAM remain to be formalized. The functional-correctness proof does
not discharge the public polynomial-time solver theorem.

The `StandardForm`, `DeterminantBounds`, `SmallFeasiblePoint`,
`RationalSizeBounds`, `EncodingSize`, `IntegerEncoding`, `IntegerCertificates`,
and `SmallCertificates` modules prove the independent certificate-size bound.
Minimal-support conic representations have independent columns, and Cramer's
rule on their integer Gram matrix bounds every reduced coordinate. Clearing
denominators uses their total encoded size. Optimality witnesses are compressed
together with equality of objectives; Farkas and recession witnesses first
normalize the strict inequality. This argument permits zero dimensions and
lower-dimensional feasible sets. Its public dependency is certificate existence.

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
| Lax808846Proofs | https://github.com/lax-archive/lax-submissions | `9394e531cc51cb67a0214bca3f9264dfe97ba5c7` | `word-ram/proofs` |
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

This submission treats finite real linear programs in the form
$\max\{c^T x:Ax\le b,\ x\ge0\}$ and their nonnegative-multiplier duals.
The mathematical concepts include weak and strong duality, complementary
slackness, primal attainment, Farkas' alternative, and certificates of
unboundedness. Exact rational certificates cover optimality, infeasibility,
and unboundedness of rational programs optimized over real variables.
The elimination and Farkas proofs adapt Jyotirmoy Bhattacharya's
MIT-licensed [farkas_lean](https://github.com/jmoy/farkas_lean) formalization.

The algorithmic scope is one uniform exact polynomial-time solver, measured
in the binary size of the rational input and using the registered word-RAM
model of [lax-808846](https://laxarchive.org/lax-808846/) through the
polynomial-time predicate of [lax-759944](https://laxarchive.org/lax-759944/).
The solver returns the encoding of the certificate that validates its answer.
Polynomial-size certificate existence is proved independently. The solver
uses the rational ellipsoid method and exact certificate recovery.

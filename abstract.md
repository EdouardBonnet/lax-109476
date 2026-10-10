This submission provides linear-programming foundations for algorithmic
submissions, including the multicommodity-flow duality and optimization
steps used by Leighton and Rao. It treats finite real programs in the form
$\max\{c^T x:Ax\le b,\ x\ge0\}$ and their nonnegative-multiplier duals.

The mathematical concepts include weak and strong duality, complementary
slackness, primal attainment, Farkas' alternative, and certificates of
unboundedness. Exact rational certificates cover optimality, infeasibility,
and unboundedness of rational programs optimized over real variables.

The algorithmic scope is one uniform exact polynomial-time solver, measured
in the binary size of the rational input and using the registered word-RAM
model of lax-808846 through the polynomial-time predicate of lax-759944.
The solver returns the encoding of the certificate that validates its answer.
Polynomial-size certificate existence is stated separately. Ellipsoid-method
internals are outside this submission's scope.

The supplied Lean proofs establish weak duality, complementary slackness,
soundness of infeasibility and unboundedness certificates, and soundness of
all rational certificate forms. Further proofs derive Farkas' alternative
from certificate existence and soundness, construct optimal dual multipliers
from Farkas' lemma and weak duality, derive strong duality from primal
attainment and optimal dual multipliers, and combine the exact solver with
certificate soundness. Farkas certificate existence, primal attainment,
polynomial-size rational certificate existence, and exact polynomial-time
solvability remain open proof obligations. The proof network records these
assumptions explicitly.

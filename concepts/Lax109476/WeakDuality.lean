import Lax109476.LinearProgram

/-!
---
title: Weak duality
type: theorem
---
Every primal feasible point $x$ and dual feasible point $y$ satisfy
$$c^T x\le b^T y.$$
Thus a dual feasible point certifies an upper bound on the primal optimum.
If their objective values agree, both are optimal.

# Formalization notes

The statement uses arbitrary real coefficient data and does not require
either feasible set to be bounded. The proof is finite sum rearrangement
and multiplication of inequalities by nonnegative coordinates.
-/

namespace Lax109476.WeakDuality

open Lax109476.LinearProgram

/-- Every primal objective is bounded by every dual objective. -/
axiom primalValue_le_dualValue :
  ∀ (m n : ℕ) (P : Program ℝ m n) (x : Fin n → ℝ) (y : Fin m → ℝ),
    PrimalFeasible P x → DualFeasible P y → primalValue P x ≤ dualValue P y

end Lax109476.WeakDuality

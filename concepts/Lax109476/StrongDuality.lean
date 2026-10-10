import Lax109476.LinearProgram

/-!
---
title: Strong duality
type: theorem
---
If a real primal linear program is feasible and bounded above, there are
primal and dual feasible points $x,y$ with equal objective values:
$$c^T x=b^T y.$$
By weak duality, these points are optimal for their respective programs.

# Formalization notes

The statement includes attainment on both sides and requires no strict
feasibility or interior-point hypothesis. The proof network separates
primal attainment from the construction of optimal dual multipliers by
Farkas' lemma.
-/

namespace Lax109476.StrongDuality

open Lax109476.LinearProgram

/-- A feasible bounded real program has matching primal and dual optimizers. -/
axiom exists_matching_optimizers :
  ∀ (m n : ℕ) (P : Program ℝ m n), IsFeasible P → IsBoundedAbove P →
    ∃ (x : Fin n → ℝ) (y : Fin m → ℝ),
      PrimalFeasible P x ∧ DualFeasible P y ∧ primalValue P x = dualValue P y

end Lax109476.StrongDuality

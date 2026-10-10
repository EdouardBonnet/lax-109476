import Lax109476.LinearProgram

/-!
---
title: Optimal dual multipliers
type: theorem
---
Every optimal primal point $x$ of a real linear program has dual feasible
multipliers $y$ whose objective equals $c^T x$.

# Formalization notes

This is the multiplier step in strong duality. Farkas' lemma is applied to
the system $y\ge0$, $A^T y\ge c$, $b^T y\le c^T x$. If that system
were infeasible, its certificate would produce either a better primal
point or a direction improving the objective, contradicting optimality.
Weak duality turns the final upper-bound inequality into equality.
-/

namespace Lax109476.OptimalDualMultipliers

open Lax109476.LinearProgram

/-- An attained primal optimum has a matching feasible dual certificate. -/
axiom exists_matching_dual :
  ∀ (m n : ℕ) (P : Program ℝ m n) (x : Fin n → ℝ), IsPrimalOptimal P x →
    ∃ y : Fin m → ℝ, DualFeasible P y ∧ primalValue P x = dualValue P y

end Lax109476.OptimalDualMultipliers

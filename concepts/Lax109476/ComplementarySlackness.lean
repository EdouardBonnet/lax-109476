import Lax109476.LinearProgram

/-!
---
title: Complementary slackness
type: theorem
---
For a primal feasible point $x$ and a dual feasible point $y$, the objective
values agree if and only if
$$y_i(b_i-(Ax)_i)=0\quad\text{for every }i,$$
$$x_j((A^T y)_j-c_j)=0\quad\text{for every }j.$$
Thus matching feasible certificates can equivalently be checked by these
complementarity conditions.

# Formalization notes

Feasibility makes every displayed product nonnegative. The difference of
the objectives is the sum of all these products, so it vanishes exactly
when each product vanishes. This identity requires no existence theorem.
-/

namespace Lax109476.ComplementarySlackness

open Lax109476.LinearProgram

/-- Matching feasible objectives are equivalent to coordinatewise complementarity. -/
axiom matching_iff_slackness :
  ∀ (m n : ℕ) (P : Program ℝ m n) (x : Fin n → ℝ) (y : Fin m → ℝ),
    PrimalFeasible P x → DualFeasible P y →
      (primalValue P x = dualValue P y ↔
        (∀ i, y i * (P.b i - rowValue P x i) = 0) ∧
        (∀ j, x j * (columnValue P y j - P.c j) = 0))

end Lax109476.ComplementarySlackness

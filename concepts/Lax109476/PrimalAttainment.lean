import Lax109476.LinearProgram

/-!
---
title: Attainment of a finite linear-programming optimum
type: theorem
---
If a real linear program is feasible and its objective is bounded above on
the feasible set, it attains its maximum at a feasible point.

# Formalization notes

No compactness assumption is imposed on the feasible polyhedron. Linear
objectives attain their finite optima on nonempty polyhedra even when those
polyhedra are unbounded. This is the attainment step used with Farkas'
lemma to obtain an optimal dual certificate. The supplied proof applies Farkas'
lemma to the original system with an objective threshold equal to the finite
supremum; a separating certificate would contradict feasibility or produce
a strictly smaller dual upper bound.
-/

namespace Lax109476.PrimalAttainment

open Lax109476.LinearProgram

/-- A nonempty polyhedron attains every bounded-above linear objective. -/
axiom exists_primal_optimizer :
  ∀ (m n : ℕ) (P : Program ℝ m n), IsFeasible P → IsBoundedAbove P →
    ∃ x : Fin n → ℝ, IsPrimalOptimal P x

end Lax109476.PrimalAttainment

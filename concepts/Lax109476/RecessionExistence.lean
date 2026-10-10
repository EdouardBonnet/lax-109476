import Lax109476.RecessionDirection
import Lax109476.FarkasLemma
import Lax109476.WeakDuality

/-!
---
title: Unbounded linear programs have improving recession directions
type: theorem
---
If the feasible objective values are unbounded above, there is a nonnegative
direction $d$ satisfying $Ad\le0$ and $c^Td>0$. Thus unboundedness has a
geometric witness, in addition to the soundness of such witnesses.

# Formalization notes

The coefficients and direction are real. This theorem does not give rational
encoding bounds or an algorithm for recovering the direction. Empty dimensions
are included.
-/

namespace Lax109476.RecessionExistence

open Lax109476.LinearProgram Lax109476.RecessionDirection

/-- Unbounded feasible objective values force an improving recession direction. -/
axiom exists_improving_direction :
  ∀ (m n : ℕ) (P : Program ℝ m n), ¬ IsBoundedAbove P →
    ∃ d : Fin n → ℝ, IsImprovingDirection P d

end Lax109476.RecessionExistence

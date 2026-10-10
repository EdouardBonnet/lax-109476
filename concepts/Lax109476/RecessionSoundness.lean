import Lax109476.RecessionDirection

/-!
---
title: Improving directions certify unboundedness
type: theorem
---
A feasible point $x$ and an improving recession direction $d$ certify that
the objective is unbounded above. For every $t\ge0$, the point $x+td$ is
feasible and has objective $c^T x+t c^T d$, which tends to infinity.

# Formalization notes

The feasible base point is essential: an improving direction by itself
does not imply that the program has any feasible points. This is certificate
soundness and does not assert existence of a rational recession certificate.
-/

namespace Lax109476.RecessionSoundness

open Lax109476.LinearProgram Lax109476.RecessionDirection

/-- A feasible base point and an improving direction rule out any objective bound. -/
axiom direction_not_bounded :
  ∀ (m n : ℕ) (P : Program ℝ m n) (x d : Fin n → ℝ),
    PrimalFeasible P x → IsImprovingDirection P d → ¬ IsBoundedAbove P

end Lax109476.RecessionSoundness

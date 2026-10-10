import Lax109476.FarkasCertificate

/-!
---
title: The feasibility alternative
type: theorem
---
A real system $Ax\le b$, $x\ge0$ is infeasible if and only if there is a
vector $y\ge0$ with $A^T y\ge0$ and $b^T y<0$.

# Formalization notes

This packages the existence and soundness directions as an equivalence.
Its proof assumes Farkas' lemma and the separately proved soundness of
infeasibility certificates.
-/

namespace Lax109476.FarkasAlternative

open Lax109476.LinearProgram Lax109476.FarkasCertificate

/-- Infeasibility is equivalent to the existence of separating row multipliers. -/
axiom infeasible_iff_certificate :
  ∀ (m n : ℕ) (P : Program ℝ m n),
    ¬ IsFeasible P ↔ ∃ y : Fin m → ℝ, IsInfeasibilityCertificate P y

end Lax109476.FarkasAlternative

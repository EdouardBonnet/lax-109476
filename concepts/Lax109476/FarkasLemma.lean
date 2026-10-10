import Lax109476.FarkasCertificate

/-!
---
title: Farkas' lemma
type: theorem
---
If $Ax\le b$, $x\ge0$ has no solution, there is a certificate
$$y\ge0,\qquad A^T y\ge0,\qquad b^T y<0.$$
Together with certificate soundness, this is the alternative between
feasibility and a certificate of infeasibility.

# Formalization notes

This is the inequality form of Farkas' lemma. We state the existence
direction separately from the elementary soundness argument. Coefficients
and witnesses are real; exact rational certificates are treated downstream.
-/

namespace Lax109476.FarkasLemma

open Lax109476.LinearProgram Lax109476.FarkasCertificate

/-- Every infeasible real system has nonnegative separating multipliers. -/
axiom exists_infeasibility_certificate :
  ∀ (m n : ℕ) (P : Program ℝ m n), ¬ IsFeasible P →
    ∃ y : Fin m → ℝ, IsInfeasibilityCertificate P y

end Lax109476.FarkasLemma

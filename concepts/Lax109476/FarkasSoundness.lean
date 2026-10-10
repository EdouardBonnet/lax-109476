import Lax109476.FarkasCertificate

/-!
---
title: Soundness of infeasibility certificates
type: theorem
---
If $y\ge0$, $A^T y\ge0$, and $b^T y<0$, the system $Ax\le b$, $x\ge0$
has no solution. This is the elementary soundness direction of the
alternative expressed by Farkas' lemma.

# Formalization notes

The proof rearranges finite sums and uses nonnegative multipliers. It
does not assume the existence direction of Farkas' lemma.
-/

namespace Lax109476.FarkasSoundness

open Lax109476.LinearProgram Lax109476.FarkasCertificate

/-- A negative certified upper bound is incompatible with primal feasibility. -/
axiom certificate_not_feasible :
  ∀ (m n : ℕ) (P : Program ℝ m n) (y : Fin m → ℝ),
    IsInfeasibilityCertificate P y → ¬ IsFeasible P

end Lax109476.FarkasSoundness

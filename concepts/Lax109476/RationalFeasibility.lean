import Lax109476.RationalCertificates
import Lax109476.FarkasSoundness

/-!
---
title: Real feasibility of rational linear programs has a rational witness
type: theorem
---
A finite linear system with rational coefficients has a nonnegative real
feasible point if and only if it has a nonnegative rational feasible point.
The direction requiring a rational witness follows from elimination over
the rationals and the soundness of rational infeasibility certificates over
the reals.

# Formalization notes

The statement imposes no full-dimension or interior-point condition. It
does not bound the size of the rational point or the time needed to find it.
-/

namespace Lax109476.RationalFeasibility

open Lax109476.LinearProgram Lax109476.RationalCertificates

/-- Real feasibility of rational coefficient data has an exact rational witness. -/
axiom exists_rational_feasible_point :
  ∀ (m n : ℕ) (P : Program ℚ m n), IsFeasible (toReal P) →
    ∃ x : Fin n → ℚ, PrimalFeasible P x

end Lax109476.RationalFeasibility

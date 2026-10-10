import Lax109476.LinearProgram

/-!
---
title: Certificates of infeasibility
type: definition
---
For the system $Ax\le b$, $x\ge0$, an infeasibility certificate is a vector
$y$ satisfying
$$y\ge0,\qquad A^T y\ge0,\qquad b^T y<0.$$
Such a vector is incompatible with primal feasibility: multiplying the
constraints by $y$ would give $0\le y^T Ax\le y^T b<0$.

# Formalization notes

The certificate is defined over the same coefficient field as the program,
so rational certificates can be checked exactly. The objective coefficients
are irrelevant to this certificate. Existence of a certificate for every
infeasible real system is the separate Farkas theorem.
-/

namespace Lax109476.FarkasCertificate

open Lax109476.LinearProgram

/-- Nonnegative row multipliers certify an impossible negative upper bound. -/
def IsInfeasibilityCertificate {K : Type} [Ring K] [PartialOrder K] {m n : ℕ}
    (P : Program K m n) (y : Fin m → K) : Prop :=
  (∀ i, 0 ≤ y i) ∧ (∀ j, 0 ≤ columnValue P y j) ∧ dualValue P y < 0

end Lax109476.FarkasCertificate

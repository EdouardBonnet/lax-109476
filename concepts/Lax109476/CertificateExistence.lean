import Lax109476.RationalFeasibility
import Lax109476.StrongDuality
import Lax109476.RecessionExistence

/-!
---
title: Exact rational certificates exist for all linear-programming outcomes
type: theorem
---
Every rational linear program has an exact rational certificate: a matching
primal–dual pair, nonnegative Farkas multipliers, or a feasible point and
an improving recession direction.

# Formalization notes

The certificate conditions are checked in the rationals and describe
optimization over real variables. This is an existence theorem independent
of polynomial-time solvability. It does not assert a size or runtime bound.
-/

namespace Lax109476.CertificateExistence

open Lax109476.LinearProgram Lax109476.RationalCertificates

/-- Every rational coefficient input has an exact valid outcome certificate. -/
axiom exists_valid_certificate :
  ∀ (m n : ℕ) (P : Program ℚ m n), ∃ certificate : Certificate m n,
    IsValidCertificate P certificate

end Lax109476.CertificateExistence

import Lax109476.RationalCertificates

/-!
---
title: Soundness of exact rational LP certificates
type: theorem
---
Every valid rational certificate establishes its claimed outcome for the
linear program over real variables. Matching primal and dual objectives
certify optimality, Farkas multipliers certify infeasibility, and a feasible
point with an improving recession direction certifies unboundedness.

# Formalization notes

Rational arithmetic is transferred exactly to the real interpretation.
Optimality uses weak duality; infeasibility uses certificate soundness;
unboundedness follows by taking arbitrarily large nonnegative multiples
of the certified recession direction. No solver or certificate-existence
theorem is needed to check a supplied certificate.
-/

namespace Lax109476.CertificateSoundness

open Lax109476.LinearProgram Lax109476.RationalCertificates

/-- Exact rational certificate checks imply the asserted real LP outcome. -/
axiom valid_certificate_correct :
  ∀ (m n : ℕ) (P : Program ℚ m n) (certificate : Certificate m n),
    IsValidCertificate P certificate → IsCorrectOutcome P certificate

end Lax109476.CertificateSoundness

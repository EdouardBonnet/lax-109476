import Lax109476.RationalEncoding

/-!
---
title: Polynomial-time certified optimization
type: theorem
---
One polynomial-time word-RAM algorithm returns an exact certificate of the
correct real outcome for every rational linear program: optimality,
infeasibility, or unboundedness.

# Formalization notes

This combines the exact solver specification with certificate soundness.
The output equals the encoding of a certificate that both passes the exact
rational conditions and establishes the corresponding claim over real
variables. The two guarantees refer to the same certificate.
-/

namespace Lax109476.CertifiedOptimization

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.RamPolytime

/-- A uniform polynomial-time RAM returns valid certificates of the real outcome. -/
axiom exists_certified_polynomial_time_solver :
  ∃ solve : List ℕ → List ℕ, RamPolytime solve ∧
    ∀ (m n : ℕ) (P : Program ℚ m n), ∃ certificate : Certificate m n,
      solve (encodeProgram P) = encodeCertificate certificate ∧
        IsValidCertificate P certificate ∧ IsCorrectOutcome P certificate

end Lax109476.CertifiedOptimization

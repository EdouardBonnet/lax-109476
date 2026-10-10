import Lax109476.RationalEncoding

/-!
---
title: Polynomial-size rational LP certificates
type: theorem
---
Every rational linear program has a valid outcome certificate whose total
binary encoding size is polynomial in the binary encoding size of the input.
The polynomial is universal over all dimensions and coefficient values.

# Formalization notes

The statement includes all three outcomes, and thus also asserts the
existence of exact rational witnesses. The size counts signs, numerators,
denominators, and outcome data in the fixed word-list encoding. It concerns
certificate existence, independently of the algorithm that finds a certificate.
Such bounds follow from the standard determinant bounds for rational
polyhedra and their primal, dual, and recession systems.
-/

namespace Lax109476.SmallCertificates

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding

/-- All rational LP outcomes have certificates of uniformly polynomial bit size. -/
axiom exists_polynomial_size_certificate :
  ∃ C k : ℕ, 0 < C ∧ ∀ (m n : ℕ) (P : Program ℚ m n),
    ∃ certificate : Certificate m n, IsValidCertificate P certificate ∧
      bitSize (encodeCertificate certificate) ≤ C * (bitSize (encodeProgram P) + 1) ^ k

end Lax109476.SmallCertificates

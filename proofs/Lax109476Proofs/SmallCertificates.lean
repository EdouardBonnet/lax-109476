import Lax109476Proofs.IntegerCertificates
import Lax109476.SmallCertificates
import Lax109476.CertificateExistence

open scoped BigOperators

namespace Lax109476Proofs.SmallCertificates

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open IntegerEncoding IntegerCertificates EncodingSize RationalSizeBounds

/--
---
conclusion: Lax109476.SmallCertificates.exists_polynomial_size_certificate
---
Start with a valid rational certificate. Clear all input denominators with
one positive multiplier, preserving certificate validity. Encode each outcome
as a nonnegative integer inequality system, normalizing strict separation or
improvement to magnitude at least one. Minimal-support conic representations
have independent columns; Cramer's rule on their Gram matrix bounds all
reduced coordinates. The actual input encoding bounds both the dimension and
the sum of denominator sizes. The resulting certificate encoding is at most
512 times the cube of input size plus one. No solver theorem is assumed.
-/
theorem polynomial_size_certificates :
    ∃ C k : ℕ, 0 < C ∧ ∀ (m n : ℕ) (P : Program ℚ m n),
      ∃ certificate : Certificate m n, IsValidCertificate P certificate ∧
        bitSize (encodeCertificate certificate) ≤ C * (bitSize (encodeProgram P) + 1) ^ k := by
  refine ⟨512, 3, by decide, ?_⟩
  intro m n P
  let L := bitSize (encodeProgram P)
  let H := 2 ^ (2 * L)
  have hH : 1 ≤ H := by
    have hp : 0 < H := by dsimp [H]; positivity
    omega
  have hs : 0 < (programDenominator P : ℚ) := by
    exact_mod_cast commonDenominator_pos (programData P)
  obtain ⟨certificate, hv⟩ := Lax109476.CertificateExistence.exists_valid_certificate m n P
  have hvint : IsValidCertificate (rationalProgram (integerProgram P)) certificate := by
    rw [integerProgram_eq_scaled]
    exact (certificate_scaled P _ hs certificate).mpr hv
  obtain ⟨hA, hb, hc⟩ := integerProgram_bounds P
  obtain ⟨small, hvalid, hbounded⟩ := compress_integer_certificate (integerProgram P) H hH
    hA hb hc certificate hvint
  have hvsmall : IsValidCertificate P small := by
    apply (certificate_scaled P _ hs small).mp
    rwa [integerProgram_eq_scaled] at hvalid
  have hdim : m + n ≤ L := dimension_bound P
  have hcap : Nat.size (coordinateCap m n H) ≤ 32 * (L + 1) ^ 2 :=
    certificate_cap_size (2 * (m + n) + 2) L (by omega)
  have houtput := bounded_certificate_encoding (coordinateCap m n H) small hbounded
  have hcoords : 2 * n + m ≤ 2 * L := by omega
  have hcost : 4 + 2 * Nat.size (coordinateCap m n H) ≤ 4 + 64 * (L + 1) ^ 2 := by omega
  have hproduct := Nat.mul_le_mul hcoords hcost
  refine ⟨small, hvsmall, ?_⟩
  change bitSize (encodeCertificate small) ≤ 512 * (L + 1) ^ 3
  nlinarith

end Lax109476Proofs.SmallCertificates

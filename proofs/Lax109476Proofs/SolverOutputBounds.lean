import Lax109476Proofs.CertificateSearch
import Lax109476Proofs.RecoveryArithmeticBounds

namespace Lax109476Proofs.SolverOutputBounds

open Lax109476.LinearProgram Lax109476.RationalCertificates
open CertificateSearch IntegerCertificates RecoveryArithmeticBounds RationalArithmeticBounds
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding
open EncodingSize RationalSizeBounds

def outputCap (m n H : ℕ) : ℕ := (IntegerCertificates.coordinateCap m n H) ^ 2 + 1

theorem pointCap_le (m n H r t : ℕ) (hr : r ≤ 2 * (m + n) + 2)
    (ht : t ≤ 2 * (m + n) + 2) :
    LexicographicBounds.coordinateCap r t H ≤ IntegerCertificates.coordinateCap m n H := by
  unfold LexicographicBounds.coordinateCap IntegerCertificates.coordinateCap
  apply Nat.mul_le_mul (Nat.factorial_le ht)
  exact (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.mul_le_mul_right (H ^ 2) hr) 1) t).trans
    (Nat.pow_le_pow_right (by omega) ht)

theorem pointHeight_le {m n H r t : ℕ} {q : ℚ}
    (hq : Height q ((LexicographicBounds.coordinateCap r t H) ^ 2 + 1))
    (hr : r ≤ 2 * (m + n) + 2) (ht : t ≤ 2 * (m + n) + 2) :
    Height q (outputCap m n H) :=
  height_mono q hq (Nat.add_le_add_right (Nat.pow_le_pow_left (pointCap_le m n H r t hr ht) 2) 1)

theorem optimalCandidate_bounded {m n : ℕ} (P : Program ℤ m n) (H : ℕ)
    (cert : Certificate m n) (h : optimalCandidate P H = some cert) :
    BoundedCertificate (outputCap m n H) cert := by
  obtain ⟨z, hz, he⟩ := Option.map_eq_some_iff.mp h
  subst cert
  have hx := indexedPoint_height _ _ _ _ H z hz
  exact ⟨fun j => pointHeight_le (hx (.inl j)) (by omega) (by omega),
    fun i => pointHeight_le (hx (.inr i)) (by omega) (by omega)⟩

theorem infeasibleCandidate_bounded {m n : ℕ} (P : Program ℤ m n) (H : ℕ)
    (cert : Certificate m n) (h : infeasibleCandidate P H = some cert) :
    BoundedCertificate (outputCap m n H) cert := by
  obtain ⟨z, hz, he⟩ := Option.map_eq_some_iff.mp h
  subst cert
  have hx := indexedPoint_height _ _ _ _ H z hz
  exact fun i => pointHeight_le (hx i) (by omega) (by omega)

theorem unboundedCandidate_bounded {m n : ℕ} (P : Program ℤ m n) (H : ℕ)
    (cert : Certificate m n) (h : unboundedCandidate P H = some cert) :
    BoundedCertificate (outputCap m n H) cert := by
  obtain ⟨z, hz, he⟩ := Option.map_eq_some_iff.mp h
  subst cert
  have hx := indexedPoint_height _ _ _ _ H z hz
  exact ⟨fun j => pointHeight_le (hx (.inl j)) (by omega) (by omega),
    fun j => pointHeight_le (hx (.inr j)) (by omega) (by omega)⟩

theorem solveInteger_bounded {m n : ℕ} (P : Program ℤ m n) (H : ℕ)
    (cert : Certificate m n) (h : solveInteger P H = some cert) :
    BoundedCertificate (outputCap m n H) cert := by
  rw [solveInteger_eq_find] at h
  have hm := List.mem_of_find?_eq_some h
  simp only [candidates, List.mem_append, Option.mem_toList] at hm
  rcases hm with (ho | hi) | hu
  · exact optimalCandidate_bounded P H cert ho
  · exact infeasibleCandidate_bounded P H cert hi
  · exact unboundedCandidate_bounded P H cert hu

theorem solve_bounded {m n : ℕ} (P : Program ℚ m n) (cert : Certificate m n)
    (h : CertificateSearch.solve P = some cert) :
    BoundedCertificate (outputCap m n (2 ^ (2 * bitSize (encodeProgram P)))) cert :=
  solveInteger_bounded _ _ cert h

/-- The returned certificate itself, rather than an existentially chosen
alternative certificate, has a cubic encoding bound. -/
theorem solve_encoding_size {m n : ℕ} (P : Program ℚ m n) (cert : Certificate m n)
    (h : CertificateSearch.solve P = some cert) :
    bitSize (encodeCertificate cert) ≤ 512 * (bitSize (encodeProgram P) + 1) ^ 3 := by
  let L := bitSize (encodeProgram P)
  let H := 2 ^ (2 * L)
  have hdim : m + n ≤ L := dimension_bound P
  have hcap : (IntegerCertificates.coordinateCap m n H).size ≤ 32 * (L + 1) ^ 2 :=
    certificate_cap_size (2 * (m + n) + 2) L (by omega)
  have hpow := size_pow_le (IntegerCertificates.coordinateCap m n H) 2
  have hadd := size_add_one_le ((IntegerCertificates.coordinateCap m n H) ^ 2)
  have hcost : 4 + 2 * (outputCap m n H).size ≤ 8 + 128 * (L + 1) ^ 2 := by
    unfold outputCap
    omega
  have houtput := bounded_certificate_encoding (outputCap m n H) cert (solve_bounded P cert h)
  have hcoords : 2 * n + m ≤ 2 * L := by omega
  have hproduct := Nat.mul_le_mul hcoords hcost
  change bitSize (encodeCertificate cert) ≤ 512 * (L + 1) ^ 3
  nlinarith

end Lax109476Proofs.SolverOutputBounds

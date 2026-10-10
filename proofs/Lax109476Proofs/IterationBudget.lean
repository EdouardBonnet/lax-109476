import Lax109476Proofs.NormalizedFeasibility

namespace Lax109476Proofs.IterationBudget

open RationalSizeBounds IntegerCertificates NormalizedFeasibility EllipsoidSequence

/-- All precision and bounding-ball factors have polynomial bit size in the
dimension and coefficient-size parameter. -/
theorem ballExponent_polynomial (m n S : ℕ) (hdim : m + n ≤ S) :
    ballExponent m n (2 ^ (2 * S)) ≤ 128 * (S + 1) ^ 2 := by
  let H := 2 ^ (2 * S)
  let B := coordinateCap m n H
  let G := m * B + n * m * H * B
  let D := 2 * (G + 1)
  let R := 4 * (n + 1) * (B + 1)
  have hsH : Nat.size H = 2 * S + 1 := Nat.size_pow
  have hsB : Nat.size B ≤ 32 * (S + 1) ^ 2 :=
    certificate_cap_size (2 * (m + n) + 2) S (by omega)
  have hm := size_le_self m
  have hn := size_le_self n
  have hmb := size_mul_le m B
  have hnmhb := size_mul_le (n * m * H) B
  have hnmh := size_mul_le (n * m) H
  have hnm := size_mul_le n m
  have hG := size_add_le (m * B) (n * m * H * B)
  have hGp := size_add_one_le G
  have hD := size_mul_le 2 (G + 1)
  have hNH := size_add_one_le (n * H)
  have hnH := size_mul_le n H
  have hR := size_mul_le (4 * (n + 1)) (B + 1)
  have hRn := size_mul_le 4 (n + 1)
  have hn1 := size_add_one_le n
  have hB1 := size_add_one_le B
  have hN := size_mul_le (D * (n * H + 1)) R
  have hND := size_mul_le D (n * H + 1)
  have hs2 : Nat.size 2 = 2 := rfl
  have hs4 : Nat.size 4 = 3 := rfl
  have hbound : Nat.size (D * (n * H + 1) * R) ≤ 3 * Nat.size B + 7 * S + 12 := by
    dsimp only [D, G, R] at *
    omega
  change Nat.size (D * (n * H + 1) * R) ≤ _
  nlinarith

/-- The verified rounded search uses a polynomial number of central cuts.
Arithmetic bit complexity and machine execution are separate obligations. -/
theorem thresholdSteps_polynomial (m n S : ℕ) (hdim : m + n ≤ S) :
    thresholdSteps n (ballExponent m n (2 ^ (2 * S))) ≤ 1024 * (S + 1) ^ 4 := by
  have hE := ballExponent_polynomial m n S hdim
  have hn : n ≤ S := by omega
  have hEn := Nat.mul_le_mul hE hn
  have hstep := Nat.mul_le_mul (by omega : 4 * (n + 1) ≤ 4 * (S + 1))
    (Nat.add_le_add_right hEn 1)
  unfold thresholdSteps
  nlinarith

end Lax109476Proofs.IterationBudget

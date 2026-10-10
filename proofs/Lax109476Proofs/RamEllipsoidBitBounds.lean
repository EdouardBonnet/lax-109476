import Lax109476Proofs.RamAdvanceState

namespace Lax109476Proofs.RamEllipsoidBitBounds

open RamDotProduct RamEllipsoidForm RamEllipsoidStep RamEllipsoidCoefficients
open RamShapeCoordinate RamShapeUpdate RationalSizeBounds

def formExponent (n h : ℕ) : ℕ := (2 * ((2 * h + 1) * (n + 1)) + 1) * (n + 1)

/-- A polynomial exponent bounds the full quadratic form and both precision denominators. -/
def magnitudeExponent (n h k : ℕ) : ℕ := formExponent n h + n * n + 2 * k + 5 * n + 13

def wordWidth (n h k : ℕ) : ℕ := 64 * magnitudeExponent n h k + 224

theorem cap_two_pow (n h : ℕ) : cap n (2 ^ h) = 2 ^ ((2 * h + 1) * (n + 1)) := by
  simp only [cap, ← pow_two]
  change (2 ^ 1 * (2 ^ h) ^ 2) ^ (n + 1) = _
  rw [← pow_mul, ← pow_add, ← pow_mul]
  congr 1
  ring

theorem formHeight_two_pow (n h : ℕ) : formHeight n (2 ^ h) = 2 ^ formExponent n h := by
  simp only [formHeight, cap_two_pow, formExponent]

theorem guard_size (M : ℕ) :
    (2 * (shapeCap (coefficientCap M)) ^ 2 + 3).size ≤ 64 * M.size + 160 := by
  have hc := coefficientCap_size M
  have hs := shapeCap_size (coefficientCap M)
  have hp := size_pow_le (shapeCap (coefficientCap M)) 2
  have hm := size_mul_le 2 ((shapeCap (coefficientCap M)) ^ 2)
  have ha := size_add_le (2 * (shapeCap (coefficientCap M)) ^ 2) 3
  have htwo : Nat.size 2 = 2 := by decide
  have hthree : Nat.size 3 = 2 := by decide
  omega

theorem magnitude_parameters (n h k : ℕ) :
    n * n ≤ 2 ^ magnitudeExponent n h k ∧
      formHeight n (2 ^ h) ≤ 2 ^ magnitudeExponent n h k ∧
      2 ^ (2 * k + 3 * n + 9) ≤ 2 ^ magnitudeExponent n h k ∧
      2 ^ (2 * n + 4) ≤ 2 ^ magnitudeExponent n h k := by
  have hn : n * n < 2 ^ (n * n) := Nat.lt_two_pow_self
  have hexp : n * n ≤ magnitudeExponent n h k := by unfold magnitudeExponent; omega
  refine ⟨hn.le.trans (Nat.pow_le_pow_right (by decide) hexp), ?_, ?_, ?_⟩
  · rw [formHeight_two_pow]
    apply Nat.pow_le_pow_right (by decide)
    unfold magnitudeExponent
    omega
  · apply Nat.pow_le_pow_right (by decide)
    unfold magnitudeExponent
    omega
  · apply Nat.pow_le_pow_right (by decide)
    unfold magnitudeExponent
    omega

/-- Every larger word width also supports the complete registered RAM cut. -/
theorem wordWidth_sufficient (n h k w : ℕ) (hw : wordWidth n h k ≤ w) :
    2 * (shapeCap (coefficientCap (2 ^ magnitudeExponent n h k))) ^ 2 + 3 < 2 ^ w := by
  have hg := guard_size (2 ^ magnitudeExponent n h k)
  rw [Nat.size_pow] at hg
  have hp := Nat.lt_size_self (2 * (shapeCap (coefficientCap (2 ^ magnitudeExponent n h k))) ^ 2 + 3)
  apply hp.trans_le
  apply Nat.pow_le_pow_right (by decide)
  unfold wordWidth at hw
  omega

theorem wordWidth_monotone {n h k n' h' k' : ℕ} (hn : n ≤ n') (hh : h ≤ h') (hk : k ≤ k') :
    wordWidth n h k ≤ wordWidth n' h' k' := by
  have hi : (2 * h + 1) * (n + 1) ≤ (2 * h' + 1) * (n' + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hf : formExponent n h ≤ formExponent n' h' :=
    Nat.mul_le_mul (by omega) (by omega)
  have hnn := Nat.mul_le_mul hn hn
  unfold wordWidth magnitudeExponent
  omega

end Lax109476Proofs.RamEllipsoidBitBounds

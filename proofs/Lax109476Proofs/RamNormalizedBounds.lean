import Lax109476Proofs.RamFeasibilityScaleBounds
import Lax109476Proofs.RamSearchBounds

namespace Lax109476Proofs.RamNormalizedBounds

open Lax109476.LinearProgram
open IntegerCertificates NormalizedFeasibility RationalArithmeticBounds

theorem factors_le_ball (m n H : ℕ) :
    precisionDenominator m n H ≤ ballDenominator m n H ∧
      outerScale n (coordinateCap m n H) ≤ ballDenominator m n H := by
  have hD := precisionDenominator_pos m n H
  have hR := outerScale_pos n (coordinateCap m n H)
  have hN : 0 < n * H + 1 := by omega
  unfold ballDenominator
  exact ⟨(Nat.le_mul_of_pos_right _ hN).trans (Nat.le_mul_of_pos_right _ hR),
    Nat.le_mul_of_pos_left _ (Nat.mul_pos hD hN)⟩

def coefficientBits (S : ℕ) : ℕ := 128 * (S + 1) ^ 2 + 2 * S + 2

theorem normalized_bounds (m n S : ℕ) (P : Program ℤ m n) (hdim : m + n ≤ S)
    (hA : ∀ i j, (P.A i j).natAbs ≤ 2 ^ (2 * S))
    (hb : ∀ i, (P.b i).natAbs ≤ 2 ^ (2 * S)) :
    (∀ i j, (normalizedMatrix P (outerScale n (coordinateCap m n (2 ^ (2 * S)))) i j).natAbs ≤
      2 ^ coefficientBits S) ∧
    (∀ i, Height (normalizedBound P (1 / (precisionDenominator m n (2 ^ (2 * S)) : ℚ)) i)
      (2 ^ coefficientBits S)) := by
  let H := 2 ^ (2 * S)
  let D := precisionDenominator m n H
  let R := outerScale n (coordinateCap m n H)
  let E := 128 * (S + 1) ^ 2
  have hH : 1 ≤ H := Nat.one_le_pow _ _ (by decide)
  have hD : 1 ≤ D := precisionDenominator_pos _ _ _
  have hsmall := IterationBudget.ballExponent_polynomial m n S hdim
  have hZ : ballDenominator m n H ≤ 2 ^ E := (Nat.lt_size_self _).le.trans
    (Nat.pow_le_pow_right (by decide) hsmall)
  have hf := factors_le_ball m n H
  have hDb : D ≤ 2 ^ E := hf.1.trans hZ
  have hRb : R ≤ 2 ^ E := hf.2.trans hZ
  have hmul : R * H ≤ 2 ^ (E + 2 * S) := by
    rw [pow_add]
    exact Nat.mul_le_mul hRb le_rfl
  have hmulB : R * H ≤ 2 ^ coefficientBits S := hmul.trans
    (Nat.pow_le_pow_right (by decide) (by dsimp [coefficientBits, E]; omega))
  have hRBound : R ≤ 2 ^ coefficientBits S :=
    (Nat.le_mul_of_pos_right _ (by omega : 0 < H)).trans hmulB
  have hadd : 2 * H * D ≤ 2 ^ coefficientBits S := by
    have hp := Nat.mul_le_mul_left (2 * H) hDb
    have he : 2 * H * 2 ^ E = 2 ^ (1 + 2 * S + E) := by
      dsimp [H]
      rw [← pow_succ', ← pow_add]
      congr 1
      omega
    rw [he] at hp
    exact hp.trans (Nat.pow_le_pow_right (by decide) (by dsimp [coefficientBits, E]; omega))
  have hε : Height (1 / (D : ℚ)) D := by
    simpa only [one_div] using height_inv (D : ℚ) D (height_nat D D le_rfl hD)
  have hεB : Height (1 / (D : ℚ)) (2 ^ coefficientBits S) :=
    height_mono _ hε (hDb.trans (Nat.pow_le_pow_right (by decide)
      (by dsimp [coefficientBits, E]; omega)))
  constructor
  · intro i j
    refine Fin.addCases ?_ ?_ i
    · intro i
      simpa [normalizedMatrix, Int.natAbs_mul] using (Nat.mul_le_mul_left R (hA i j)).trans hmulB
    · intro k
      simp only [normalizedMatrix, Fin.addCases_right]
      split_ifs
      · simpa only [Int.natAbs_neg, Int.natAbs_natCast] using hRBound
      · simp
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      have hbi : Height (P.b i : ℚ) H := by simpa [Height] using And.intro (hb i) hH
      simpa only [normalizedBound, Fin.addCases_left] using
        height_mono _ (height_add (P.b i : ℚ) (1 / (D : ℚ)) H D hbi hε) hadd
    · intro i
      simpa only [normalizedBound, Fin.addCases_right] using hεB

end Lax109476Proofs.RamNormalizedBounds

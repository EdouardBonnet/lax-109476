import Lax109476Proofs.EllipsoidPrecision
import Lax109476Proofs.EllipsoidDeterminant

/-! Conditioning and determinant shrinkage of the same rational stored update. -/

namespace Lax109476Proofs.EllipsoidIteration

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter EllipsoidPrecision
open EllipsoidDeterminant Lax109476.RationalCertificates

/-- The per-step enlargement used by the uniform precision schedule. -/
def stepAccuracy (n : ℕ) : ℚ := 1 / (2 : ℚ) ^ (2 * n + 4)

theorem stepAccuracy_pos (n : ℕ) : 0 < stepAccuracy n := by
  unfold stepAccuracy
  positivity

/-- The chosen accuracy leaves enough determinant contraction for rounding. -/
theorem stepAccuracy_small (n : ℕ) (hn : 2 ≤ n) :
    (stepAccuracy n : ℝ) ≤ 1 / (8 * (n : ℝ) * ((n : ℝ) + 1)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < 8 * (n : ℝ) * ((n : ℝ) + 1) := by positivity
  have h₁ : (n : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have h₂ : (n : ℝ) + 1 ≤ (2 : ℝ) ^ (n + 1) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := n + 1)).le
  have hprod := mul_le_mul h₁ h₂ (by positivity) (by positivity)
  have he : (2 : ℝ) ^ (2 * n + 4) = 8 * ((2 : ℝ) ^ n * (2 : ℝ) ^ (n + 1)) := by
    rw [← pow_add, show 2 * n + 4 = (n + (n + 1)) + 3 by omega, pow_add]
    norm_num
    ring
  have hb : 8 * (n : ℝ) * ((n : ℝ) + 1) ≤ (2 : ℝ) ^ (2 * n + 4) := by
    rw [he]
    nlinarith only [hprod]
  simp only [stepAccuracy, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat]
  exact div_le_div_of_nonneg_left (by norm_num) hp hb

/-- Containment's enlargement also has a relative quadratic-form bound. -/
theorem storedShape_relative_bound (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ)
    (a : Fin n → ℚ) (D : ℕ) (hD : 0 < D) (η : ℚ) (hη : 0 ≤ η)
    (lowerBound : ℝ)
    (hlower : ∀ x : Fin n → ℝ, lowerBound * (x ⬝ᵥ x) ≤
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x))
    (hprecision : 2 * (n : ℝ) / D ≤ (η : ℝ) * lowerBound)
    (x : Fin n → ℝ) :
    x ⬝ᵥ (realShape (roundedStepShape n A a D η) *ᵥ x) ≤
      (1 + (η : ℝ)) ^ 3 * (x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x)) := by
  have hp : (0 : ℝ) ≤ η := by exact_mod_cast hη
  have h := roundedShape_relative_bound (cutShape n A a) D hD lowerBound η hp hlower hprecision x
  rw [realShape_roundedStepShape]
  simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  calc
    _ ≤ (1 + (η : ℝ)) ^ 2 *
        ((1 + (η : ℝ)) * (x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x))) :=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = _ := by ring

/-- The stored update contracts the square-root determinant despite both roundings. -/
theorem storedStep_shrink (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : (realShape A).PosDef)
    (a : Fin n → ℚ) (ha : realVector a ≠ 0) (D : ℕ) (hD : 0 < D)
    (η : ℚ) (hη : 0 < η)
    (hsmall : (η : ℝ) ≤ 1 / (8 * (n : ℝ) * ((n : ℝ) + 1)))
    (lowerBound : ℝ)
    (hlower : ∀ x : Fin n → ℝ, lowerBound * (x ⬝ᵥ x) ≤
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x))
    (hprecision : 2 * (n : ℝ) / D ≤ (η : ℝ) * lowerBound) :
    Real.sqrt (realShape (roundedStepShape n A a D η)).det ≤
      Real.exp (-1 / (4 * ((n : ℝ) + 1))) * Real.sqrt (realShape A).det := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < η := by exact_mod_cast hη
  have hη₁ : (η : ℝ) ≤ 1 := by
    have hh : 1 / (8 * (n : ℝ) * ((n : ℝ) + 1)) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by nlinarith)
    exact hsmall.trans hh
  have hscalar : (1 + (η : ℝ)) ^ 3 ≤ (1 + 2 * (η : ℝ)) ^ 2 := by
    have hsq : (η : ℝ) ^ 2 ≤ η := by nlinarith
    have hcube := mul_le_mul_of_nonneg_left hsq (le_of_lt hp)
    nlinarith only [hcube, hp, sq_nonneg (η : ℝ)]
  have hC : (realShape (cutShape n A a)).PosDef := by
    rw [realShape_cutShape]
    exact realCutShape_posDef n hn (realShape A) hA (realVector a) ha
  have hP := roundedStepShape_posDef n hn A hA a ha D hD η hη
  have hrelative : ∀ x, x ⬝ᵥ (realShape (roundedStepShape n A a D η) *ᵥ x) ≤
      (1 + 2 * (η : ℝ)) ^ 2 * (x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x)) := by
    intro x
    have hnonneg : 0 ≤ x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x) := by
      simpa using hC.posSemidef.dotProduct_mulVec_nonneg x
    exact (storedShape_relative_bound n A a D hD η (le_of_lt hη) lowerBound hlower hprecision x).trans
      (mul_le_mul_of_nonneg_right hscalar hnonneg)
  have hdet := det_le_relative_pow hC hP ((1 + 2 * (η : ℝ)) ^ 2) hrelative
  rw [Fintype.card_fin] at hdet
  have hpow : ((1 + 2 * (η : ℝ)) ^ 2) ^ n = ((1 + 2 * (η : ℝ)) ^ n) ^ 2 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hsqrt : Real.sqrt (realShape (roundedStepShape n A a D η)).det ≤
      (1 + 2 * (η : ℝ)) ^ n * Real.sqrt (realShape (cutShape n A a)).det := by
    have h := Real.sqrt_le_sqrt hdet
    rw [hpow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (by positivity)] at h
    exact h
  have hδ : 2 * (η : ℝ) ≤ 1 / (4 * (n : ℝ) * ((n : ℝ) + 1)) := by
    calc
      _ ≤ 2 * (1 / (8 * (n : ℝ) * ((n : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hsmall (by norm_num)
      _ = _ := by
        simp only [div_eq_mul_inv, _root_.mul_inv_rev]
        norm_num
        ring
  have hshrink := EllipsoidStep.enlarged_shrink_bound n hn (2 * (η : ℝ))
    (by positivity) hδ
  rw [realShape_cutShape] at hsqrt
  change Real.sqrt (realShape (roundedStepShape n A a D η)).det ≤
    (1 + 2 * (η : ℝ)) ^ n * Real.sqrt (realCutShape n (realShape A) (realVector a)).det at hsqrt
  rw [det_realCutShape n hn (realShape A) hA (realVector a) ha] at hsqrt
  rw [Real.sqrt_mul (le_of_lt hA.det_pos)] at hsqrt
  calc
    _ ≤ ((1 + 2 * (η : ℝ)) ^ n * Real.sqrt (EllipsoidStep.determinantFactor n)) *
        Real.sqrt (realShape A).det := by nlinarith only [hsqrt]
    _ ≤ _ := mul_le_mul_of_nonneg_right hshrink (Real.sqrt_nonneg _)

/-- The uniform schedule gives contraction without additional precision hypotheses. -/
theorem uniform_storedStep_shrink (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : (realShape A).PosDef)
    (a : Fin n → ℚ) (hanorm : 1 ≤ realVector a ⬝ᵥ realVector a)
    (l : ℕ) (hbound : ∀ x : Fin n → ℝ,
      ((2 : ℝ) ^ l)⁻¹ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (realShape A *ᵥ x)) :
    Real.sqrt (realShape (roundedStepShape n A a
      (gridDenominator (l + 2) (2 * n + 4) n) (stepAccuracy n))).det ≤
      Real.exp (-1 / (4 * ((n : ℝ) + 1))) * Real.sqrt (realShape A).det := by
  have ha : realVector a ≠ 0 := by
    intro h
    rw [h, dotProduct_zero] at hanorm
    norm_num at hanorm
  have hprec := grid_shape_precision (l + 2) (2 * n + 4) n
  have hcast : (stepAccuracy n : ℝ) = ((2 : ℝ) ^ (2 * n + 4))⁻¹ := by
    simp [stepAccuracy]
  apply storedStep_shrink n hn A hA a ha _ (gridDenominator_pos _ _ _)
    (stepAccuracy n) (stepAccuracy_pos n) (stepAccuracy_small n hn)
    (((2 : ℝ) ^ (l + 2))⁻¹) (exactCut_lower_bound n hn A hA a ha l hbound)
  simpa only [hcast] using hprec

/-- The uniform stored update satisfies the conditioning bounds needed by the next step. -/
theorem uniform_storedStep_bounds (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : (realShape A).PosDef)
    (a : Fin n → ℚ) (hanorm : 1 ≤ realVector a ⬝ᵥ realVector a)
    (l : ℕ) (hbound : ∀ x : Fin n → ℝ,
      ((2 : ℝ) ^ l)⁻¹ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (realShape A *ᵥ x)) (x : Fin n → ℝ) :
    let P := realShape (roundedStepShape n A a
      (gridDenominator (l + 2) (2 * n + 4) n) (stepAccuracy n))
    (1 / 4 : ℝ) * (x ⬝ᵥ (realShape A *ᵥ x)) ≤ x ⬝ᵥ (P *ᵥ x) ∧
      x ⬝ᵥ (P *ᵥ x) ≤ 4 * (x ⬝ᵥ (realShape A *ᵥ x)) := by
  let D := gridDenominator (l + 2) (2 * n + 4) n
  let η := stepAccuracy n
  have hD : 0 < D := gridDenominator_pos _ _ _
  have hp : (0 : ℝ) < η := by exact_mod_cast stepAccuracy_pos n
  have ha : realVector a ≠ 0 := by
    intro h
    rw [h, dotProduct_zero] at hanorm
    norm_num at hanorm
  have hη : (η : ℝ) ≤ 1 / 8 := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    apply (stepAccuracy_small n hn).trans
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  have hC : (realShape (cutShape n A a)).PosDef := by
    rw [realShape_cutShape]
    exact realCutShape_posDef n hn (realShape A) hA (realVector a) ha
  have hR := roundedCutShape_posDef n hn A hA a ha D hD
  have hnonneg : 0 ≤ x ⬝ᵥ (realShape (roundedShape (cutShape n A a) D) *ᵥ x) := by
    simpa using hR.posSemidef.dotProduct_mulVec_nonneg x
  have hcutnonneg : 0 ≤ x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x) := by
    simpa using hC.posSemidef.dotProduct_mulVec_nonneg x
  have hfactor : 1 ≤ (1 + (η : ℝ)) ^ 2 := by nlinarith
  have hfactorUpper : (1 + (η : ℝ)) ^ 3 ≤ 2 := by
    calc
      _ ≤ (9 / 8 : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
      _ ≤ _ := by norm_num
  have hprec : 2 * (n : ℝ) / D ≤ (η : ℝ) * ((2 : ℝ) ^ (l + 2))⁻¹ := by
    simpa [η, stepAccuracy] using grid_shape_precision (l + 2) (2 * n + 4) n
  have hrelative := storedShape_relative_bound n A a D hD η (le_of_lt (stepAccuracy_pos n))
    _ (exactCut_lower_bound n hn A hA a ha l hbound) hprec x
  have hcoarse := realCutShape_coarse_bounds n hn (realShape A) hA (realVector a) x ha
  have hcoarse' : (1 / 4 : ℝ) * (x ⬝ᵥ (realShape A *ᵥ x)) ≤
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x) ∧
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x) ≤ 2 * (x ⬝ᵥ (realShape A *ᵥ x)) := by
    rw [realShape_cutShape]
    exact hcoarse
  dsimp only
  constructor
  · apply hcoarse'.1.trans
    apply (roundedShape_sandwich (cutShape n A a) D hD x).1.trans
    rw [realShape_roundedStepShape]
    simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact le_mul_of_one_le_left hnonneg hfactor
  · apply hrelative.trans
    have h := mul_le_mul_of_nonneg_right hfactorUpper hcutnonneg
    nlinarith only [h, hcoarse'.2]

end Lax109476Proofs.EllipsoidIteration

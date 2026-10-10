import Lax109476Proofs.EllipsoidIteration

/-!
A concrete sequence of rational stored ellipsoids. The cut normals are supplied
externally; no LP separation, stopping rule, certificate recovery, or RAM execution
is asserted here.
-/

namespace Lax109476Proofs.EllipsoidSequence

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter EllipsoidPrecision EllipsoidIteration
open Lax109476.RationalCertificates

/-- The shape sequence uses the precision justified by the previous iteration's lower bound. -/
def shapes (n : ℕ) (a : ℕ → Fin n → ℚ) : ℕ → Matrix (Fin n) (Fin n) ℚ
  | 0 => 1
  | k + 1 => roundedStepShape n (shapes n a k) (a k)
      (gridDenominator (2 * k + 2) (2 * n + 4) n) (stepAccuracy n)

/-- The center sequence performs the matching computable rational update. -/
def centers (n : ℕ) (a : ℕ → Fin n → ℚ) (c₀ : Fin n → ℚ) : ℕ → Fin n → ℚ
  | 0 => c₀
  | k + 1 => roundedCenter n (shapes n a k) (a k) (centers n a c₀ k)
      (gridDenominator (2 * k + 2) (2 * n + 4) n)

/-- The actual stored iterates remain positive definite and uniformly conditioned. -/
theorem shapes_invariant (n : ℕ) (hn : 2 ≤ n) (a : ℕ → Fin n → ℚ)
    (ha : ∀ k, 1 ≤ realVector (a k) ⬝ᵥ realVector (a k)) (k : ℕ) :
    (realShape (shapes n a k)).PosDef ∧
    ∀ x : Fin n → ℝ,
      ((2 : ℝ) ^ (2 * k))⁻¹ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (realShape (shapes n a k) *ᵥ x) ∧
        x ⬝ᵥ (realShape (shapes n a k) *ᵥ x) ≤ (4 : ℝ) ^ k * (x ⬝ᵥ x) := by
  induction k with
  | zero =>
      have hid : realShape (shapes n a 0) = 1 := by
        ext i j
        simp [shapes, realShape, Matrix.one_apply, apply_ite]
      rw [hid]
      exact ⟨Matrix.PosDef.one, by simp⟩
  | succ k ih =>
      have hne : realVector (a k) ≠ 0 := by
        intro h
        have hh := ha k
        rw [h, dotProduct_zero] at hh
        norm_num at hh
      constructor
      · exact roundedStepShape_posDef n hn _ ih.1 _ hne _
          (gridDenominator_pos _ _ _) _ (stepAccuracy_pos n)
      · intro x
        have hs := uniform_storedStep_bounds n hn (shapes n a k) ih.1 (a k) (ha k)
          (2 * k) (fun y => (ih.2 y).1) x
        have he : ((2 : ℝ) ^ (2 * (k + 1)))⁻¹ = (1 / 4 : ℝ) * ((2 : ℝ) ^ (2 * k))⁻¹ := by
          rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
          norm_num
        constructor
        · rw [he]
          have hh := mul_le_mul_of_nonneg_left (ih.2 x).1 (show (0 : ℝ) ≤ 1 / 4 by norm_num)
          change _ ≤ x ⬝ᵥ (realShape (roundedStepShape n (shapes n a k) (a k)
            (gridDenominator (2 * k + 2) (2 * n + 4) n) (stepAccuracy n)) *ᵥ x)
          nlinarith only [hh, hs.1]
        · change x ⬝ᵥ (realShape (roundedStepShape n (shapes n a k) (a k)
            (gridDenominator (2 * k + 2) (2 * n + 4) n) (stepAccuracy n)) *ᵥ x) ≤ _
          rw [pow_succ]
          have hh := mul_le_mul_of_nonneg_left (ih.2 x).2 (show (0 : ℝ) ≤ 4 by norm_num)
          nlinarith only [hh, hs.2]

/-- The determinant-shrink estimate holds for the actual recursive rational sequence. -/
theorem shapes_shrink (n : ℕ) (hn : 2 ≤ n) (a : ℕ → Fin n → ℚ)
    (ha : ∀ k, 1 ≤ realVector (a k) ⬝ᵥ realVector (a k)) (k : ℕ) :
    Real.sqrt (realShape (shapes n a k)).det ≤
      Real.exp (-(k : ℝ) / (4 * ((n : ℝ) + 1))) := by
  let v := fun j => Real.sqrt (realShape (shapes n a j)).det
  have hstep : ∀ j, v (j + 1) ≤ Real.exp (-1 / (4 * ((n : ℝ) + 1))) * v j := by
    intro j
    have hi := shapes_invariant n hn a ha j
    exact uniform_storedStep_shrink n hn (shapes n a j) hi.1 (a j) (ha j)
      (2 * j) (fun x => (hi.2 x).1)
  have h := EllipsoidStep.iterated_shrink_bound n v hstep k
  have hid : realShape (shapes n a 0) = 1 := by
    ext i j
    simp [shapes, realShape, Matrix.one_apply, apply_ite]
  simpa only [v, hid, Matrix.det_one, Real.sqrt_one, mul_one] using h

/-- Every point retained by all supplied central cuts stays inside the stored ellipsoids. -/
theorem preserves_points (n : ℕ) (hn : 2 ≤ n) (a : ℕ → Fin n → ℚ)
    (ha : ∀ k, 1 ≤ realVector (a k) ⬝ᵥ realVector (a k)) (c₀ : Fin n → ℚ)
    (x : Fin n → ℝ) (hx : (x - realVector c₀) ⬝ᵥ (x - realVector c₀) ≤ 1)
    (hcut : ∀ k, realVector (a k) ⬝ᵥ (x - realVector (centers n a c₀ k)) ≤ 0)
    (k : ℕ) :
    (x - realVector (centers n a c₀ k)) ⬝ᵥ
      ((realShape (shapes n a k))⁻¹ *ᵥ (x - realVector (centers n a c₀ k))) ≤ 1 := by
  induction k with
  | zero =>
      have hid : realShape (shapes n a 0) = 1 := by
        ext i j
        simp [shapes, realShape, Matrix.one_apply, apply_ite]
      simpa only [centers, hid, inv_one, Matrix.one_mulVec] using hx
  | succ k ih =>
      have hi := shapes_invariant n hn a ha k
      exact uniform_roundedStep_contains n hn (shapes n a k) hi.1 (a k) (centers n a c₀ k)
        (ha k) (2 * k) (2 * n + 4) (fun y => (hi.2 y).1) x ih (hcut k)

/-- The chosen grid denominator has a linear bit length in iteration and dimension. -/
theorem sequence_grid_size (n k : ℕ) :
    Nat.size (gridDenominator (2 * k + 2) (2 * n + 4) n) = 2 * k + 3 * n + 10 := by
  rw [gridDenominator_size]
  omega

/-- A polynomial number of steps suffices for a prescribed dyadic determinant threshold. -/
def thresholdSteps (n B : ℕ) : ℕ := 4 * (n + 1) * (B * n + 1)

/-- The actual stored sequence crosses a dyadic threshold after the explicit step budget.
An LP termination theorem still needs to connect this threshold to feasibility. -/
theorem shapes_below_threshold (n : ℕ) (hn : 2 ≤ n) (a : ℕ → Fin n → ℚ)
    (ha : ∀ k, 1 ≤ realVector (a k) ⬝ᵥ realVector (a k)) (B : ℕ) :
    Real.sqrt (realShape (shapes n a (thresholdSteps n B))).det <
      (((2 : ℝ) ^ B)⁻¹) ^ n := by
  have htarget : 0 < (((2 : ℝ) ^ B)⁻¹) ^ n := by positivity
  have hlog : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hlogtarget : Real.log ((((2 : ℝ) ^ B)⁻¹) ^ n) =
      -((B * n : ℕ) : ℝ) * Real.log 2 := by
    rw [Real.log_pow, Real.log_inv, Real.log_pow]
    push_cast
    ring
  have he : -(thresholdSteps n B : ℝ) / (4 * ((n : ℝ) + 1)) =
      -(((B * n : ℕ) : ℝ) + 1) := by
    have hp : (n : ℝ) + 1 ≠ 0 := by positivity
    unfold thresholdSteps
    push_cast
    field_simp
  have hlt : -(((B * n : ℕ) : ℝ) + 1) < -((B * n : ℕ) : ℝ) * Real.log 2 := by
    have h := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (B * n))
    linarith
  have h := shapes_shrink n hn a ha (thresholdSteps n B)
  rw [he] at h
  apply h.trans_lt
  rw [← Real.exp_log htarget, hlogtarget]
  exact Real.exp_lt_exp.mpr hlt

end Lax109476Proofs.EllipsoidSequence

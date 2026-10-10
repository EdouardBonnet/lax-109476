import Lax109476Proofs.EllipsoidBounds

/-! Computable center updates and their error in the new ellipsoid's metric. -/

namespace Lax109476Proofs.EllipsoidCenter

open Matrix EllipsoidRounding EllipsoidBounds
open Lax109476.RationalCertificates

/-- The inverse-form length of the direction in which the center is moved. -/
theorem cut_direction_form (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (a : Fin n → ℝ)
    (ha : a ≠ 0) :
    (A *ᵥ a) ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ (A *ᵥ a)) =
      (((n : ℝ) + 1) ^ 2 / (n : ℝ) ^ 2) * (a ⬝ᵥ (A *ᵥ a)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnz : (n : ℝ) ≠ 0 := by linarith
  have hnm : (n : ℝ) - 1 ≠ 0 := by linarith
  have hq : a ⬝ᵥ (A *ᵥ a) ≠ 0 := by
    have hp : 0 < a ⬝ᵥ (A *ᵥ a) := by simpa using hA.dotProduct_mulVec_pos ha
    exact ne_of_gt hp
  have hc : A⁻¹ *ᵥ (A *ᵥ a) = a := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit), Matrix.one_mulVec]
  rw [realCutShape_inverse n hn A hA a ha]
  simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.vecMulVec_mulVec,
    hc, dotProduct_smul, dotProduct_add, smul_eq_mul,
    op_smul_eq_smul, dotProduct_comm (A *ᵥ a) a]
  field_simp
  ring

/-- The exact error caused by replacing the square root in the center update. -/
theorem center_approximation_form (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (a : Fin n → ℝ)
    (ha : a ≠ 0) (r : ℝ) (hr : 0 < r) :
    let q := a ⬝ᵥ (A *ᵥ a)
    let e := (1 / (((n : ℝ) + 1) * r) -
      1 / (((n : ℝ) + 1) * Real.sqrt q)) • (A *ᵥ a)
    e ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ e) =
      ((r - Real.sqrt q) / ((n : ℝ) * r)) ^ 2 := by
  let q := a ⬝ᵥ (A *ᵥ a)
  have hq : 0 < q := by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnz : (n : ℝ) ≠ 0 := by linarith
  have hnp : (n : ℝ) + 1 ≠ 0 := by linarith
  have hrz : r ≠ 0 := ne_of_gt hr
  dsimp only
  simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [cut_direction_form n hn A hA a ha]
  change _ = ((r - Real.sqrt q) / ((n : ℝ) * r)) ^ 2
  generalize ht : Real.sqrt q = t
  have htpos : 0 < t := ht ▸ Real.sqrt_pos.mpr hq
  have htsq : t ^ 2 = q := by rw [← ht, Real.sq_sqrt (le_of_lt hq)]
  change (1 / (((n : ℝ) + 1) * r) - 1 / (((n : ℝ) + 1) * t)) *
    ((1 / (((n : ℝ) + 1) * r) - 1 / (((n : ℝ) + 1) * t)) *
      ((((n : ℝ) + 1) ^ 2 / (n : ℝ) ^ 2) * q)) = _
  rw [← htsq]
  have htz : t ≠ 0 := ne_of_gt htpos
  field_simp
  ring

/-- Before grid rounding, the new center uses a rational upper square root. -/
def approximateCenter (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ)
    (a c : Fin n → ℚ) (D : ℕ) : Fin n → ℚ :=
  c - (1 / (((n : ℚ) + 1) * RationalRounding.sqrtUpper (a ⬝ᵥ (A *ᵥ a)) D)) •
    (A *ᵥ a)

/-- The stored center is rounded onto the same rational grid as the shape. -/
def roundedCenter (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ)
    (a c : Fin n → ℚ) (D : ℕ) : Fin n → ℚ :=
  fun i => RationalRounding.roundDown (approximateCenter n A a c D i) D

/-- The scalar square-root approximation bounds the inverse-form center error. -/
theorem center_approximation_error (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (a : Fin n → ℝ)
    (ha : a ≠ 0) (r ε : ℝ)
    (hr : Real.sqrt (a ⬝ᵥ (A *ᵥ a)) ≤ r)
    (herr : r - Real.sqrt (a ⬝ᵥ (A *ᵥ a)) ≤ ε) :
    let q := a ⬝ᵥ (A *ᵥ a)
    let e := (1 / (((n : ℝ) + 1) * r) -
      1 / (((n : ℝ) + 1) * Real.sqrt q)) • (A *ᵥ a)
    e ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ e) ≤ ε ^ 2 / ((n : ℝ) ^ 2 * q) := by
  let q := a ⬝ᵥ (A *ᵥ a)
  have hq : 0 < q := by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hrp : 0 < r := hs.trans_le hr
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have ht : 0 ≤ r - Real.sqrt q := by linarith
  have hε : 0 ≤ ε := ht.trans herr
  have hsquare : q ≤ r ^ 2 := by nlinarith [Real.sq_sqrt (le_of_lt hq)]
  dsimp only
  rw [center_approximation_form n hn A hA a ha r hrp, div_pow, mul_pow]
  change (r - Real.sqrt q) ^ 2 / ((n : ℝ) ^ 2 * r ^ 2) ≤ _
  calc
    _ ≤ ε ^ 2 / ((n : ℝ) ^ 2 * r ^ 2) :=
      div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    _ ≤ ε ^ 2 / ((n : ℝ) ^ 2 * q) :=
      div_le_div_of_nonneg_left (sq_nonneg ε) (by positivity)
        (mul_le_mul_of_nonneg_left hsquare (sq_nonneg _))

/-- Two center errors can be combined without assuming their signs or directions. -/
theorem form_add_le_two {ι : Type} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℝ} (hB : B.PosDef) (u v : ι → ℝ) :
    (u + v) ⬝ᵥ (B *ᵥ (u + v)) ≤
      2 * (u ⬝ᵥ (B *ᵥ u)) + 2 * (v ⬝ᵥ (B *ᵥ v)) := by
  have h : 0 ≤ (u - v) ⬝ᵥ (B *ᵥ (u - v)) := by
    simpa using hB.posSemidef.dotProduct_mulVec_nonneg (u - v)
  simp only [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub,
    symmetric_form hB.1 v u] at h
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add,
    symmetric_form hB.1 v u]
  linarith

/-- The exact real center, used only in the correctness argument. -/
noncomputable def exactCenter (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ)
    (a c : Fin n → ℚ) : Fin n → ℝ :=
  realVector c -
    (1 / (((n : ℝ) + 1) * Real.sqrt (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))) •
      (realShape A *ᵥ realVector a)

/-- Casting the quadratic form commutes with exact rational arithmetic. -/
theorem cast_direction_form (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ)
    (a : Fin n → ℚ) :
    ((a ⬝ᵥ (A *ᵥ a) : ℚ) : ℝ) = realVector a ⬝ᵥ (realShape A *ᵥ realVector a) := by
  simp [dotProduct, Matrix.mulVec, realShape, realVector, Rat.cast_sum]

/-- The rational center update has exactly the square-root approximation error. -/
theorem approximateCenter_difference (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ)
    (a c : Fin n → ℚ) (D : ℕ) :
    exactCenter n A a c - realVector (approximateCenter n A a c D) =
      (1 / (((n : ℝ) + 1) * (RationalRounding.sqrtUpper (a ⬝ᵥ (A *ᵥ a)) D : ℝ)) -
        1 / (((n : ℝ) + 1) *
          Real.sqrt (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))) •
        (realShape A *ᵥ realVector a) := by
  ext i
  simp [exactCenter, approximateCenter, realVector, realShape, Matrix.mulVec,
    dotProduct, Rat.cast_sum, smul_eq_mul]
  ring

/-- Both sources of center error are bounded in the rounded shape's inverse metric.
The two explicit precision inequalities each allocate a quarter of the squared budget. -/
theorem roundedCenter_total_error (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : (realShape A).PosDef)
    (a c : Fin n → ℚ) (ha : realVector a ≠ 0) (D : ℕ) (hD : 0 < D)
    (lowerBound η : ℝ) (hl : 0 < lowerBound)
    (hlower : ∀ x : Fin n → ℝ, lowerBound * (x ⬝ᵥ x) ≤
      x ⬝ᵥ (realShape (roundedShape (cutShape n A a) D) *ᵥ x))
    (hsqrt : 4 / ((n : ℝ) ^ 2 * (D : ℝ) ^ 2 *
      (realVector a ⬝ᵥ (realShape A *ᵥ realVector a))) ≤ η ^ 2 / 4)
    (hgrid : lowerBound⁻¹ * ((n : ℝ) * (1 / D) ^ 2) ≤ η ^ 2 / 4) :
    let e := exactCenter n A a c - realVector (roundedCenter n A a c D)
    e ⬝ᵥ ((realShape (roundedShape (cutShape n A a) D))⁻¹ *ᵥ e) ≤ η ^ 2 := by
  let ar := realVector a
  let q := ar ⬝ᵥ (realShape A *ᵥ ar)
  let Q := realShape (roundedShape (cutShape n A a) D)
  let e₁ := exactCenter n A a c - realVector (approximateCenter n A a c D)
  let e₂ := realVector (approximateCenter n A a c D) - realVector (roundedCenter n A a c D)
  have hq : 0 < q := by simpa [q, ar] using hA.dotProduct_mulVec_pos ha
  have hqrat : 0 ≤ a ⬝ᵥ (A *ᵥ a) := by
    have hp : (0 : ℝ) ≤ ((a ⬝ᵥ (A *ᵥ a) : ℚ) : ℝ) := by
      rw [cast_direction_form]
      exact le_of_lt hq
    exact_mod_cast hp
  have hQ : Q.PosDef := roundedCutShape_posDef n hn A hA a ha D hD
  have hC : (realShape (cutShape n A a)).PosDef := by
    rw [realShape_cutShape]
    exact realCutShape_posDef n hn (realShape A) hA ar ha
  have horder : ∀ y, y ⬝ᵥ (realShape (cutShape n A a) *ᵥ y) ≤ y ⬝ᵥ (Q *ᵥ y) :=
    fun y => (roundedShape_sandwich (cutShape n A a) D hD y).1
  have h₁ : e₁ ⬝ᵥ (Q⁻¹ *ᵥ e₁) ≤ η ^ 2 / 4 := by
    apply (inverse_quadratic_antitone hC hQ horder e₁).trans
    rw [realShape_cutShape]
    obtain ⟨hr, herr⟩ := RationalRounding.sqrtUpper_bounds (a ⬝ᵥ (A *ᵥ a)) hqrat D hD
    rw [cast_direction_form] at hr herr
    have hb := center_approximation_error n hn (realShape A) hA ar ha
      (RationalRounding.sqrtUpper (a ⬝ᵥ (A *ᵥ a)) D : ℝ) (2 / D) hr (by linarith)
    change e₁ ⬝ᵥ ((realCutShape n (realShape A) ar)⁻¹ *ᵥ e₁) ≤ _
    have hid : (2 / (D : ℝ)) ^ 2 / ((n : ℝ) ^ 2 * q) =
        4 / ((n : ℝ) ^ 2 * (D : ℝ) ^ 2 * q) := by ring
    have hb' : e₁ ⬝ᵥ ((realCutShape n (realShape A) ar)⁻¹ *ᵥ e₁) ≤
        (2 / (D : ℝ)) ^ 2 / ((n : ℝ) ^ 2 * q) := by
      dsimp [e₁]
      rw [approximateCenter_difference]
      exact hb
    exact hb'.trans (hid ▸ hsqrt)
  have h₂ : e₂ ⬝ᵥ (Q⁻¹ *ᵥ e₂) ≤ η ^ 2 / 4 := by
    have h := roundedCenter_error hQ lowerBound hl hlower (approximateCenter n A a c D) D hD
    exact h.trans hgrid
  have he : exactCenter n A a c - realVector (roundedCenter n A a c D) = e₁ + e₂ := by
    dsimp [e₁, e₂]
    abel
  dsimp only
  rw [he]
  have h := form_add_le_two hQ.inv e₁ e₂
  linarith

/-- The stored rational shape also includes the allowance for center displacement. -/
def roundedStepShape (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ)
    (a : Fin n → ℚ) (D : ℕ) (η : ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  ((1 + η) ^ 2) • roundedShape (cutShape n A a) D

/-- Entrywise casting preserves scalar enlargement of the rounded shape. -/
theorem realShape_roundedStepShape (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ)
    (a : Fin n → ℚ) (D : ℕ) (η : ℚ) :
    realShape (roundedStepShape n A a D η) =
      ((1 + (η : ℝ)) ^ 2) • realShape (roundedShape (cutShape n A a) D) := by
  ext i j
  simp [realShape, roundedStepShape, Matrix.smul_apply, smul_eq_mul]

/-- The stored rounded shape is positive definite. -/
theorem roundedStepShape_posDef (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : (realShape A).PosDef)
    (a : Fin n → ℚ) (ha : realVector a ≠ 0) (D : ℕ) (hD : 0 < D)
    (η : ℚ) (hη : 0 < η) : (realShape (roundedStepShape n A a D η)).PosDef := by
  rw [realShape_roundedStepShape]
  apply (roundedCutShape_posDef n hn A hA a ha D hD).smul
  have hp : (0 : ℝ) < η := by exact_mod_cast hη
  positivity

/-- One completely rational stored update contains the cut portion of its predecessor. -/
theorem roundedStep_contains (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : (realShape A).PosDef)
    (a c : Fin n → ℚ) (ha : realVector a ≠ 0) (D : ℕ) (hD : 0 < D)
    (lowerBound : ℝ) (hl : 0 < lowerBound) (η : ℚ) (hη : 0 < η)
    (hlower : ∀ x : Fin n → ℝ, lowerBound * (x ⬝ᵥ x) ≤
      x ⬝ᵥ (realShape (roundedShape (cutShape n A a) D) *ᵥ x))
    (hsqrt : 4 / ((n : ℝ) ^ 2 * (D : ℝ) ^ 2 *
      (realVector a ⬝ᵥ (realShape A *ᵥ realVector a))) ≤ (η : ℝ) ^ 2 / 4)
    (hgrid : lowerBound⁻¹ * ((n : ℝ) * (1 / D) ^ 2) ≤ (η : ℝ) ^ 2 / 4)
    (x : Fin n → ℝ)
    (hx : (x - realVector c) ⬝ᵥ ((realShape A)⁻¹ *ᵥ (x - realVector c)) ≤ 1)
    (hcut : realVector a ⬝ᵥ (x - realVector c) ≤ 0) :
    (x - realVector (roundedCenter n A a c D)) ⬝ᵥ
      ((realShape (roundedStepShape n A a D η))⁻¹ *ᵥ
        (x - realVector (roundedCenter n A a c D))) ≤ 1 := by
  have hQ := roundedCutShape_posDef n hn A hA a ha D hD
  have he := roundedCenter_total_error n hn A hA a c ha D hD lowerBound η hl hlower hsqrt hgrid
  have hxe : (x - exactCenter n A a c) ⬝ᵥ
      ((realShape (roundedShape (cutShape n A a) D))⁻¹ *ᵥ
        (x - exactCenter n A a c)) ≤ 1 := by
    have h := roundedCutShape_contains n hn A hA a ha D hD (x - realVector c) hx hcut
    have hid : x - exactCenter n A a c = x - realVector c +
        (1 / (((n : ℝ) + 1) *
          Real.sqrt (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))) •
            (realShape A *ᵥ realVector a) := by
      unfold exactCenter
      abel
    rw [hid]
    exact h
  have hp : (0 : ℝ) < η := by exact_mod_cast hη
  have h := enlargedShape_contains_displaced hQ η hp
    (x - exactCenter n A a c)
    (exactCenter n A a c - realVector (roundedCenter n A a c D)) hxe he
  rw [realShape_roundedStepShape]
  simpa only [sub_add_sub_cancel] using h

end Lax109476Proofs.EllipsoidCenter

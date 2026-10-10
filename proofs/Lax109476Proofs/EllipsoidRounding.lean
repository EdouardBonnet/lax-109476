import Lax109476Proofs.EllipsoidStep
import Lax109476Proofs.RationalRounding

/-!
Internal shape-rounding lemmas. Entrywise rounding needs a diagonal enlargement:
entrywise inequalities alone do not imply containment of ellipsoids.
-/

namespace Lax109476Proofs.EllipsoidRounding

open Matrix

/-- Symmetry permits exchanging the arguments of the associated bilinear form. -/
theorem symmetric_form {ι : Type} [Fintype ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (u v : ι → ℝ) :
    u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
  have ht : Aᵀ = A := (Matrix.isHermitian_iff_isSymm.mp hA).eq
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, ht, dotProduct_comm]

/-- Uniform entrywise error controls the error in every quadratic form. -/
theorem quadratic_error_bound {n : ℕ} (E : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (hE : ∀ i j, |E i j| ≤ ε) (x : Fin n → ℝ) :
    |x ⬝ᵥ (E *ᵥ x)| ≤ (n : ℝ) * ε * (x ⬝ᵥ x) := by
  have hcs : (∑ i, |x i|) ^ 2 ≤ (n : ℝ) * (x ⬝ᵥ x) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin n => (1 : ℝ)) (fun i => |x i|)
    simpa [dotProduct, sq_abs, pow_two] using h
  calc
    _ = |∑ i, ∑ j, x i * E i j * x j| := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    _ ≤ ∑ i, ∑ j, |x i * E i j * x j| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, ε * |x i| * |x j| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [abs_mul]
      calc
        _ ≤ |x i| * ε * |x j| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hE i j) (abs_nonneg _)) (abs_nonneg _)
        _ = _ := by ring
    _ = ε * (∑ i, |x i|) ^ 2 := by
      simp only [Finset.mul_sum, Finset.sum_mul, pow_two]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ε * ((n : ℝ) * (x ⬝ᵥ x)) := mul_le_mul_of_nonneg_left hcs hε
    _ = _ := by ring

/-- Quadratic-form domination preserves positive definiteness. -/
theorem posDef_of_quadratic_le {ι : Type} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.IsHermitian)
    (hAB : ∀ x, x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x)) : B.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hB
  intro x hx
  have hpos : 0 < x ⬝ᵥ (A *ᵥ x) := by
    simpa using hA.dotProduct_mulVec_pos hx
  simpa using hpos.trans_le (hAB x)

/-- Completing the square gives a variational upper bound for the inverse form. -/
theorem inverse_variational_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosDef) (x y : ι → ℝ) :
    2 * (x ⬝ᵥ y) - y ⬝ᵥ (A *ᵥ y) ≤ x ⬝ᵥ (A⁻¹ *ᵥ x) := by
  have hcancel : A *ᵥ (A⁻¹ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit), Matrix.one_mulVec]
  have hnonneg : 0 ≤ (y - A⁻¹ *ᵥ x) ⬝ᵥ (A *ᵥ (y - A⁻¹ *ᵥ x)) := by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg (y - A⁻¹ *ᵥ x)
  rw [Matrix.mulVec_sub, hcancel, sub_dotProduct, dotProduct_sub,
    dotProduct_sub, symmetric_form hA.1 (A⁻¹ *ᵥ x) y, hcancel,
    dotProduct_comm y x, dotProduct_comm (A⁻¹ *ᵥ x) x] at hnonneg
  linarith

/-- Enlarging a positive definite shape decreases its inverse quadratic form. -/
theorem inverse_quadratic_antitone {ι : Type} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    (hAB : ∀ y, y ⬝ᵥ (A *ᵥ y) ≤ y ⬝ᵥ (B *ᵥ y)) (x : ι → ℝ) :
    x ⬝ᵥ (B⁻¹ *ᵥ x) ≤ x ⬝ᵥ (A⁻¹ *ᵥ x) := by
  have hcancel : B *ᵥ (B⁻¹ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B
      ((Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit), Matrix.one_mulVec]
  have hvar := inverse_variational_bound hA x (B⁻¹ *ᵥ x)
  have hle := hAB (B⁻¹ *ᵥ x)
  rw [hcancel, dotProduct_comm (B⁻¹ *ᵥ x) x] at hle
  linarith

/-- Round every rational entry down, then add a diagonal error allowance. -/
def roundedShape {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (D : ℕ) :
    Matrix (Fin n) (Fin n) ℚ :=
  (of fun i j => RationalRounding.roundDown (A i j) D) + ((n : ℚ) / D) • 1

/-- Cast a rational shape entrywise to the real numbers. -/
def realShape {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => (A i j : ℝ)

/-- The diagonal allowance dominates all entrywise rounding errors. -/
theorem enlargement_sandwich {n : ℕ} (A R : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (herr : ∀ i j, |R i j - A i j| ≤ ε)
    (x : Fin n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ ((R + ((n : ℝ) * ε) • 1) *ᵥ x) ∧
      x ⬝ᵥ ((R + ((n : ℝ) * ε) • 1) *ᵥ x) ≤
        x ⬝ᵥ (A *ᵥ x) + 2 * (n : ℝ) * ε * (x ⬝ᵥ x) := by
  have h := quadratic_error_bound (R - A) ε hε herr x
  rw [Matrix.sub_mulVec, dotProduct_sub] at h
  have hh := abs_le.mp h
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add, dotProduct_smul, smul_eq_mul]
  constructor <;> linarith [hh.1, hh.2]

/-- Entrywise rational rounding with a diagonal allowance bounds every form. -/
theorem roundedShape_sandwich {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (D : ℕ) (hD : 0 < D) (x : Fin n → ℝ) :
    x ⬝ᵥ (realShape A *ᵥ x) ≤ x ⬝ᵥ (realShape (roundedShape A D) *ᵥ x) ∧
      x ⬝ᵥ (realShape (roundedShape A D) *ᵥ x) ≤
        x ⬝ᵥ (realShape A *ᵥ x) + (2 * (n : ℝ) / D) * (x ⬝ᵥ x) := by
  let R : Matrix (Fin n) (Fin n) ℝ :=
    fun i j => (RationalRounding.roundDown (A i j) D : ℝ)
  have herr : ∀ i j, |R i j - realShape A i j| ≤ 1 / (D : ℝ) := by
    intro i j
    have h := RationalRounding.roundDown_error (A i j) D hD
    dsimp [R, realShape]
    rw [abs_of_nonpos (by linarith [h.1])]
    linarith [h.2]
  have hid : realShape (roundedShape A D) = R + ((n : ℝ) * (1 / D)) • 1 := by
    ext i j
    change ((RationalRounding.roundDown (A i j) D +
      ((n : ℚ) / D) * (if i = j then 1 else 0) : ℚ) : ℝ) =
      (RationalRounding.roundDown (A i j) D : ℝ) +
        ((n : ℝ) * (1 / D)) * (if i = j then 1 else 0)
    split_ifs <;> simp [div_eq_mul_inv]
  rw [hid]
  simpa only [mul_one_div] using
    enlargement_sandwich (realShape A) R (1 / D) (by positivity) herr x

/-- Rounding a symmetric rational matrix preserves symmetry. -/
theorem roundedShape_isHermitian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : A.IsSymm) (D : ℕ) : (realShape (roundedShape A D)).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm, Matrix.IsSymm.ext_iff]
  intro i j
  simp [realShape, roundedShape, hA.apply i j, Matrix.one_apply, eq_comm]

/-- The enlarged rounded shape remains positive definite. -/
theorem roundedShape_posDef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (realShape A).PosDef) (D : ℕ) (hD : 0 < D) :
    (realShape (roundedShape A D)).PosDef := by
  have hsym : A.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    have h := (Matrix.isHermitian_iff_isSymm.mp hA.1).apply i j
    dsimp [realShape] at h
    exact_mod_cast h
  exact posDef_of_quadratic_le hA (roundedShape_isHermitian A hsym D)
    (fun x => (roundedShape_sandwich A D hD x).1)

/-- Every point of the original ellipsoid stays in the enlarged rounded one. -/
theorem roundedShape_contains {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (realShape A).PosDef) (D : ℕ) (hD : 0 < D) (x : Fin n → ℝ)
    (hx : x ⬝ᵥ ((realShape A)⁻¹ *ᵥ x) ≤ 1) :
    x ⬝ᵥ ((realShape (roundedShape A D))⁻¹ *ᵥ x) ≤ 1 :=
  (inverse_quadratic_antitone hA (roundedShape_posDef A hA D hD)
    (fun y => (roundedShape_sandwich A D hD y).1) x).trans hx

/-- A known lower eigenvalue bound turns the additive error into relative error. -/
theorem roundedShape_relative_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (D : ℕ) (hD : 0 < D) (lowerBound η : ℝ) (hη : 0 ≤ η)
    (hlower : ∀ x : Fin n → ℝ, lowerBound * (x ⬝ᵥ x) ≤ x ⬝ᵥ (realShape A *ᵥ x))
    (hprecision : 2 * (n : ℝ) / D ≤ η * lowerBound) (x : Fin n → ℝ) :
    x ⬝ᵥ (realShape (roundedShape A D) *ᵥ x) ≤
      (1 + η) * (x ⬝ᵥ (realShape A *ᵥ x)) := by
  have hxx : 0 ≤ x ⬝ᵥ x := by
    simpa using dotProduct_star_self_nonneg x
  have herror := mul_le_mul_of_nonneg_right hprecision hxx
  have hrelative := mul_le_mul_of_nonneg_left (hlower x) hη
  have hround := (roundedShape_sandwich A D hD x).2
  nlinarith only [herror, hrelative, hround]

/-- The inverse of a nonzero scalar enlargement is the reciprocal enlargement. -/
theorem inverse_smul {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosDef) (k : ℝ) (hk : k ≠ 0) :
    (k • A)⁻¹ = k⁻¹ • A⁻¹ := by
  apply Matrix.inv_eq_right_inv
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit),
    inv_mul_cancel₀ hk, one_smul]

/-- A lower shape bound supplies an upper bound for its inverse quadratic form. -/
theorem inverse_form_upper_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosDef) (lowerBound : ℝ) (hl : 0 < lowerBound)
    (hbound : ∀ x, lowerBound * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x)) (x : ι → ℝ) :
    x ⬝ᵥ (A⁻¹ *ᵥ x) ≤ lowerBound⁻¹ * (x ⬝ᵥ x) := by
  have hI : (1 : Matrix ι ι ℝ).PosDef := Matrix.PosDef.one
  have hlI : (lowerBound • (1 : Matrix ι ι ℝ)).PosDef := hI.smul hl
  have horder : ∀ y, y ⬝ᵥ ((lowerBound • (1 : Matrix ι ι ℝ)) *ᵥ y) ≤
      y ⬝ᵥ (A *ᵥ y) := by
    intro y
    simpa only [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      smul_eq_mul] using hbound y
  have h := inverse_quadratic_antitone hlI hA horder x
  rw [inverse_smul hI lowerBound (ne_of_gt hl)] at h
  simpa only [inv_one, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul] using h

/-- A small center displacement can be absorbed by a scalar shape enlargement. -/
theorem center_displacement_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosDef) (η : ℝ) (hη : 0 < η)
    (x e : ι → ℝ) (hx : x ⬝ᵥ (A *ᵥ x) ≤ 1)
    (he : e ⬝ᵥ (A *ᵥ e) ≤ η ^ 2) :
    (x + e) ⬝ᵥ (A *ᵥ (x + e)) ≤ (1 + η) ^ 2 := by
  have hnonneg : 0 ≤ (η • x - e) ⬝ᵥ (A *ᵥ (η • x - e)) := by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg (η • x - e)
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
    dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    symmetric_form hA.1 e x] at hnonneg
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add,
    symmetric_form hA.1 e x]
  have hb₁ := mul_le_mul_of_nonneg_left hx (show 0 ≤ η ^ 2 + η by positivity)
  have hb₂ := mul_le_mul_of_nonneg_left he (show 0 ≤ 1 + η by positivity)
  nlinarith only [hnonneg, hb₁, hb₂, hη]

/-- A rounded center preserves containment after the quantified enlargement. -/
theorem enlargedShape_contains_displaced {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosDef) (η : ℝ) (hη : 0 < η)
    (x e : ι → ℝ) (hx : x ⬝ᵥ (A⁻¹ *ᵥ x) ≤ 1)
    (he : e ⬝ᵥ (A⁻¹ *ᵥ e) ≤ η ^ 2) :
    (x + e) ⬝ᵥ ((((1 + η) ^ 2) • A)⁻¹ *ᵥ (x + e)) ≤ 1 := by
  have hk : 0 < (1 + η) ^ 2 := by positivity
  rw [inverse_smul hA _ (ne_of_gt hk), Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul]
  calc
    _ ≤ ((1 + η) ^ 2)⁻¹ * (1 + η) ^ 2 :=
      mul_le_mul_of_nonneg_left (center_displacement_bound hA.inv η hη x e hx he)
        (inv_nonneg.mpr (le_of_lt hk))
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hk)

/-- Grid rounding of the center is small in the inverse-shape metric. -/
theorem roundedCenter_error {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (lowerBound : ℝ) (hl : 0 < lowerBound)
    (hbound : ∀ x, lowerBound * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x))
    (c : Fin n → ℚ) (D : ℕ) (hD : 0 < D) :
    let e : Fin n → ℝ := fun i => (c i : ℝ) - RationalRounding.roundDown (c i) D
    e ⬝ᵥ (A⁻¹ *ᵥ e) ≤ lowerBound⁻¹ * ((n : ℝ) * (1 / D) ^ 2) := by
  dsimp only
  apply (inverse_form_upper_bound hA lowerBound hl hbound _).trans
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt hl))
  simpa only [dotProduct, ← pow_two] using
    RationalRounding.roundDown_vector_error n c D hD

end Lax109476Proofs.EllipsoidRounding

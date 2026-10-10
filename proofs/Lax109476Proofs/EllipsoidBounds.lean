import Lax109476Proofs.EllipsoidRounding

/-! Internal conditioning and precision bounds for general central-cut shapes. -/

namespace Lax109476Proofs.EllipsoidBounds

open Matrix EllipsoidRounding

/-- Cauchy–Schwarz for the bilinear form of a positive definite real matrix. -/
theorem form_cauchy_schwarz {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosDef) (a x : ι → ℝ) (ha : a ≠ 0) :
    (x ⬝ᵥ (A *ᵥ a)) ^ 2 ≤ (a ⬝ᵥ (A *ᵥ a)) * (x ⬝ᵥ (A *ᵥ x)) := by
  let q := a ⬝ᵥ (A *ᵥ a)
  let t := x ⬝ᵥ (A *ᵥ a)
  have hq : 0 < q := by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hnonneg : 0 ≤ (q • x - t • a) ⬝ᵥ (A *ᵥ (q • x - t • a)) := by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg (q • x - t • a)
  have hid : (q • x - t • a) ⬝ᵥ (A *ᵥ (q • x - t • a)) =
      q * (q * (x ⬝ᵥ (A *ᵥ x)) - t ^ 2) := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
      dotProduct_sub, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      symmetric_form hA.1 a x]
    dsimp [q, t]
    ring
  rw [hid] at hnonneg
  have h := nonneg_of_mul_nonneg_right hnonneg hq
  change t ^ 2 ≤ q * (x ⬝ᵥ (A *ᵥ x))
  linarith

/-- The general central-cut shape uses only rational operations on its data. -/
def cutShape (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (a : Fin n → ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  ((n : ℚ) ^ 2 / ((n : ℚ) ^ 2 - 1)) •
    (A - (2 / (((n : ℚ) + 1) * (a ⬝ᵥ (A *ᵥ a)))) •
      Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a))

/-- The corresponding real-valued update, used for the conditioning proof. -/
noncomputable def realCutShape (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
    (A - (2 / (((n : ℝ) + 1) * (a ⬝ᵥ (A *ᵥ a)))) •
      Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a))

/-- Casting commutes with the rational shape update. -/
theorem realShape_cutShape (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ)
    (a : Fin n → ℚ) :
    realShape (cutShape n A a) = realCutShape n (realShape A) (fun i => (a i : ℝ)) := by
  ext i j
  simp [realShape, cutShape, realCutShape, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.vecMulVec, Matrix.mulVec, dotProduct, Rat.cast_sum, smul_eq_mul]

/-- A central cut changes every shape eigenvalue by controlled multiplicative factors. -/
theorem realCutShape_sandwich (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (a x : Fin n → ℝ)
    (ha : a ≠ 0) :
    ((n : ℝ) / ((n : ℝ) + 1)) ^ 2 * (x ⬝ᵥ (A *ᵥ x)) ≤
      x ⬝ᵥ (realCutShape n A a *ᵥ x) ∧
    x ⬝ᵥ (realCutShape n A a *ᵥ x) ≤
      ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) * (x ⬝ᵥ (A *ᵥ x)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  let q := a ⬝ᵥ (A *ᵥ a)
  let t := x ⬝ᵥ (A *ᵥ a)
  let α := (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)
  let β := 2 / ((n : ℝ) + 1)
  have hq : 0 < q := by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hα : 0 < α := by dsimp [α]; apply div_pos <;> nlinarith
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hcs : t ^ 2 ≤ q * (x ⬝ᵥ (A *ᵥ x)) := form_cauchy_schwarz hA a x ha
  have hcs' : t ^ 2 / q ≤ x ⬝ᵥ (A *ᵥ x) := (div_le_iff₀ hq).mpr (by nlinarith)
  have hterm : 0 ≤ β * (t ^ 2 / q) := by positivity
  have htermUpper := mul_le_mul_of_nonneg_left hcs' hβ
  have hid : x ⬝ᵥ (realCutShape n A a *ᵥ x) =
      α * ((x ⬝ᵥ (A *ᵥ x)) - β * (t ^ 2 / q)) := by
    simp only [realCutShape, Matrix.smul_mulVec, Matrix.sub_mulVec,
      Matrix.vecMulVec_mulVec, dotProduct_smul, dotProduct_sub,
      smul_eq_mul]
    dsimp [α, β, q, t]
    simp only [dotProduct_comm (A *ᵥ a) x, div_eq_mul_inv, _root_.mul_inv_rev]
    ring
  have hfactor : α * (1 - β) = ((n : ℝ) / ((n : ℝ) + 1)) ^ 2 := by
    dsimp [α, β]
    have hp : (n : ℝ) + 1 ≠ 0 := by linarith
    have hd : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp
    ring
  rw [hid, ← hfactor]
  constructor
  · have h := mul_le_mul_of_nonneg_left htermUpper (le_of_lt hα)
    nlinarith only [h]
  · have h := mul_nonneg (le_of_lt hα) hterm
    nlinarith only [h]

/-- Every general central-cut shape remains positive definite. -/
theorem realCutShape_posDef (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (a : Fin n → ℝ)
    (ha : a ≠ 0) : (realCutShape n A a).PosDef := by
  have hsym : (realCutShape n A a).IsHermitian := by
    rw [Matrix.isHermitian_iff_isSymm, Matrix.IsSymm.ext_iff]
    intro i j
    have h := (Matrix.isHermitian_iff_isSymm.mp hA.1).apply i j
    simp [realCutShape, Matrix.smul_apply, Matrix.sub_apply, Matrix.vecMulVec,
      smul_eq_mul, h, mul_comm]
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hsym
  intro x hx
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < ((n : ℝ) / ((n : ℝ) + 1)) ^ 2 := by positivity
  have hxx : 0 < x ⬝ᵥ (A *ᵥ x) := by simpa using hA.dotProduct_mulVec_pos hx
  simpa using (mul_pos hp hxx).trans_le (realCutShape_sandwich n hn A hA a x ha).1

/-- The general shape update has an explicit inverse, without a matrix square root. -/
theorem realCutShape_inverse (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (a : Fin n → ℝ)
    (ha : a ≠ 0) :
    (realCutShape n A a)⁻¹ =
      (((n : ℝ) ^ 2 - 1) / (n : ℝ) ^ 2) •
        (A⁻¹ + (2 / (((n : ℝ) - 1) * (a ⬝ᵥ (A *ᵥ a)))) •
          Matrix.vecMulVec a a) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnzero : (n : ℝ) ≠ 0 := by linarith
  have hminus : (n : ℝ) - 1 ≠ 0 := by linarith
  have hplus : (n : ℝ) + 1 ≠ 0 := by linarith
  have hdiff : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hq : a ⬝ᵥ (A *ᵥ a) ≠ 0 := by
    have hp : 0 < a ⬝ᵥ (A *ᵥ a) := by simpa using hA.dotProduct_mulVec_pos ha
    exact ne_of_gt hp
  have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A
    ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
  have hrow : (A *ᵥ a) ᵥ* A⁻¹ = a := by
    rw [Matrix.vecMul_mulVec, (Matrix.isHermitian_iff_isSymm.mp hA.1).eq,
      hAA, Matrix.vecMul_one]
  have hcross : Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a) * Matrix.vecMulVec a a =
      (a ⬝ᵥ (A *ᵥ a)) • Matrix.vecMulVec (A *ᵥ a) a := by
    rw [Matrix.vecMulVec_mul_vecMulVec, dotProduct_comm]
    ext i j
    simp [Matrix.vecMulVec, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
  apply Matrix.inv_eq_right_inv
  unfold realCutShape
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hc : (((n : ℝ) ^ 2 - 1) / (n : ℝ) ^ 2) *
      ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) = 1 := by field_simp
  rw [hc, one_smul]
  simp only [mul_add, sub_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hAA, hcross, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hrow]
  simp only [smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- The general update has the same determinant factor as the normalized update. -/
theorem det_realCutShape (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (a : Fin n → ℝ)
    (ha : a ≠ 0) :
    (realCutShape n A a).det = A.det * EllipsoidStep.determinantFactor n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  let q := a ⬝ᵥ (A *ᵥ a)
  let α := (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)
  let β := 2 / ((n : ℝ) + 1)
  have hq : q ≠ 0 := by
    have hp : 0 < q := by simpa [q] using hA.dotProduct_mulVec_pos ha
    exact ne_of_gt hp
  have hfactor : A - (β / q) • Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a) =
      A * (1 - (β / q) • Matrix.vecMulVec a (A *ᵥ a)) := by
    rw [mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_vecMulVec]
  have hdet : (1 - (β / q) • Matrix.vecMulVec a (A *ᵥ a)).det = 1 - β := by
    have h := Matrix.det_one_add_replicateCol_mul_replicateRow
      (ι := Unit) a (-(β / q) • (A *ᵥ a))
    have hd : a ⬝ᵥ (-(β / q) • (A *ᵥ a)) = -β := by
      rw [dotProduct_smul]
      change -(β / q) * q = -β
      field_simp
    have hd' : (-(β / q) • (A *ᵥ a)) ⬝ᵥ a = -β := by
      rw [dotProduct_comm]
      exact hd
    rw [hd'] at h
    simpa [← Matrix.vecMulVec_eq Unit, sub_eq_add_neg, neg_smul] using h
  have hform : realCutShape n A a =
      α • (A - (β / q) • Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a)) := by
    dsimp [realCutShape, α, β, q]
    congr 2
    congr 1
    simp only [div_eq_mul_inv, _root_.mul_inv_rev]
    ring
  rw [hform, Matrix.det_smul, Fintype.card_fin, hfactor, Matrix.det_mul, hdet]
  have hαβ : α * (1 - β) = ((n : ℝ) / ((n : ℝ) + 1)) ^ 2 := by
    dsimp [α, β]
    have hp : (n : ℝ) + 1 ≠ 0 := by linarith
    have hd : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp
    ring
  unfold EllipsoidStep.determinantFactor
  calc
    _ = A.det * (α ^ (n - 1) * (α * (1 - β))) := by
      nth_rewrite 1 [show n = (n - 1) + 1 by omega]
      rw [pow_succ]
      ring
    _ = _ := by rw [hαβ]

/-- The exact center displacement puts the inverse form in normalized coordinates. -/
theorem realCutShape_quadratic (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (a x : Fin n → ℝ)
    (ha : a ≠ 0) :
    let q := a ⬝ᵥ (A *ᵥ a)
    let z := x + (1 / (((n : ℝ) + 1) * Real.sqrt q)) • (A *ᵥ a)
    z ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ z) =
      EllipsoidStep.centralCutForm n (x ⬝ᵥ (A⁻¹ *ᵥ x))
        ((a ⬝ᵥ x) / Real.sqrt q) := by
  let q := a ⬝ᵥ (A *ᵥ a)
  let s := 1 / (((n : ℝ) + 1) * Real.sqrt q)
  let z := x + s • (A *ᵥ a)
  have hq : 0 < q := by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hc : A⁻¹ *ᵥ (A *ᵥ a) = a := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit), Matrix.one_mulVec]
  have hzz : z ⬝ᵥ (A⁻¹ *ᵥ z) =
      x ⬝ᵥ (A⁻¹ *ᵥ x) + 2 * s * (a ⬝ᵥ x) + s ^ 2 * q := by
    dsimp [z]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hc, add_dotProduct,
      dotProduct_add, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      symmetric_form hA.inv.1 (A *ᵥ a) x, dotProduct_comm x a,
      dotProduct_comm (A *ᵥ a) a]
    dsimp [q]
    ring
  have haz : a ⬝ᵥ z = a ⬝ᵥ x + s * q := by
    simp [z, q, dotProduct_add, dotProduct_smul]
  change z ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ z) = _
  rw [realCutShape_inverse n hn A hA a ha]
  simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.vecMulVec_mulVec,
    dotProduct_smul, dotProduct_add, smul_eq_mul, dotProduct_comm z a]
  rw [hzz, haz]
  simp only [op_smul_eq_smul, smul_eq_mul]
  change (((n : ℝ) ^ 2 - 1) / (n : ℝ) ^ 2) *
    ((x ⬝ᵥ (A⁻¹ *ᵥ x) + 2 * s * (a ⬝ᵥ x) + s ^ 2 * q) +
      (2 / (((n : ℝ) - 1) * q)) * (((a ⬝ᵥ x) + s * q) * ((a ⬝ᵥ x) + s * q))) = _
  dsimp [s, EllipsoidStep.centralCutForm]
  generalize ht : Real.sqrt q = t
  have htpos : 0 < t := ht ▸ Real.sqrt_pos.mpr hq
  have htsq : t ^ 2 = q := by rw [← ht, Real.sq_sqrt (le_of_lt hq)]
  rw [← htsq]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnz : (n : ℝ) ≠ 0 := by linarith
  have hnp : (n : ℝ) + 1 ≠ 0 := by linarith
  have hnm : (n : ℝ) - 1 ≠ 0 := by linarith
  have htz : t ≠ 0 := ne_of_gt htpos
  field_simp
  ring

/-- Containment for a central cut of an arbitrary positive definite ellipsoid. -/
theorem realCutShape_contains (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (a x : Fin n → ℝ)
    (ha : a ≠ 0) (hx : x ⬝ᵥ (A⁻¹ *ᵥ x) ≤ 1) (hcut : a ⬝ᵥ x ≤ 0) :
    let q := a ⬝ᵥ (A *ᵥ a)
    let z := x + (1 / (((n : ℝ) + 1) * Real.sqrt q)) • (A *ᵥ a)
    z ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ z) ≤ 1 := by
  dsimp only
  rw [realCutShape_quadratic n hn A hA a x ha]
  let q := a ⬝ᵥ (A *ᵥ a)
  have hq : 0 < q := by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hc : A⁻¹ *ᵥ (A *ᵥ a) = a := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit), Matrix.one_mulVec]
  have hav : A *ᵥ a ≠ 0 := by
    intro h
    have h' := hc
    rw [h, Matrix.mulVec_zero] at h'
    exact ha h'.symm
  have hcs := form_cauchy_schwarz hA.inv (A *ᵥ a) x hav
  rw [hc, dotProduct_comm x a, dotProduct_comm (A *ᵥ a) a] at hcs
  have hcs' : ((a ⬝ᵥ x) / Real.sqrt q) ^ 2 ≤ x ⬝ᵥ (A⁻¹ *ᵥ x) := by
    rw [div_pow, Real.sq_sqrt (le_of_lt hq)]
    apply (div_le_iff₀ hq).mpr
    simpa [q, mul_comm] using hcs
  have ht : -1 ≤ (a ⬝ᵥ x) / Real.sqrt q := by nlinarith
  exact EllipsoidStep.centralCutForm_le_one n _ _ (by exact_mod_cast hn)
    hx ht (div_nonpos_of_nonpos_of_nonneg hcut (le_of_lt hs))

/-- The computable rational shape update followed by grid rounding is positive definite. -/
theorem roundedCutShape_posDef (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : (realShape A).PosDef)
    (a : Fin n → ℚ) (ha : (fun i => (a i : ℝ)) ≠ 0) (D : ℕ) (hD : 0 < D) :
    (realShape (roundedShape (cutShape n A a) D)).PosDef := by
  apply roundedShape_posDef _ _ D hD
  rw [realShape_cutShape]
  exact realCutShape_posDef n hn (realShape A) hA _ ha

/-- Shape rounding after a central cut preserves containment, at the exact new center.
Approximating that center requires the separate displacement bound. -/
theorem roundedCutShape_contains (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : (realShape A).PosDef)
    (a : Fin n → ℚ) (ha : (fun i => (a i : ℝ)) ≠ 0) (D : ℕ) (hD : 0 < D)
    (x : Fin n → ℝ) (hx : x ⬝ᵥ ((realShape A)⁻¹ *ᵥ x) ≤ 1)
    (hcut : (fun i => (a i : ℝ)) ⬝ᵥ x ≤ 0) :
    let ar : Fin n → ℝ := fun i => (a i : ℝ)
    let q := ar ⬝ᵥ (realShape A *ᵥ ar)
    let z := x + (1 / (((n : ℝ) + 1) * Real.sqrt q)) • (realShape A *ᵥ ar)
    z ⬝ᵥ ((realShape (roundedShape (cutShape n A a) D))⁻¹ *ᵥ z) ≤ 1 := by
  have hQ : (realShape (cutShape n A a)).PosDef := by
    rw [realShape_cutShape]
    exact realCutShape_posDef n hn (realShape A) hA _ ha
  apply roundedShape_contains _ hQ D hD
  rw [realShape_cutShape]
  exact realCutShape_contains n hn (realShape A) hA _ x ha hx hcut

/-- Coarse conditioning bounds, convenient for a uniform precision schedule. -/
theorem realCutShape_coarse_bounds (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (a x : Fin n → ℝ)
    (ha : a ≠ 0) :
    (1 / 4 : ℝ) * (x ⬝ᵥ (A *ᵥ x)) ≤ x ⬝ᵥ (realCutShape n A a *ᵥ x) ∧
      x ⬝ᵥ (realCutShape n A a *ᵥ x) ≤ 2 * (x ⬝ᵥ (A *ᵥ x)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hxx : 0 ≤ x ⬝ᵥ (A *ᵥ x) := by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg x
  have hp : 0 < (n : ℝ) + 1 := by linarith
  have hd : 0 < (n : ℝ) ^ 2 - 1 := by nlinarith
  have hratio : (1 / 2 : ℝ) ≤ (n : ℝ) / ((n : ℝ) + 1) :=
    (le_div_iff₀ hp).mpr (by linarith)
  have hlo : (1 / 4 : ℝ) ≤ ((n : ℝ) / ((n : ℝ) + 1)) ^ 2 := by
    nlinarith
  have hhi : (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) ≤ 2 :=
    (div_le_iff₀ hd).mpr (by nlinarith)
  have h := realCutShape_sandwich n hn A hA a x ha
  exact ⟨(mul_le_mul_of_nonneg_right hlo hxx).trans h.1,
    h.2.trans (mul_le_mul_of_nonneg_right hhi hxx)⟩

/-- Lower and upper shape bounds propagate through any sequence of rounded updates.
The hypotheses describe the actual form bounds that each update must establish. -/
theorem iterated_conditioning {ι : Type} [Fintype ι]
    (Q : ℕ → Matrix ι ι ℝ) (r R : ℝ)
    (hinit : ∀ x, r * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Q 0 *ᵥ x) ∧
      x ⬝ᵥ (Q 0 *ᵥ x) ≤ R * (x ⬝ᵥ x))
    (hstep : ∀ k x, (1 / 4 : ℝ) * (x ⬝ᵥ (Q k *ᵥ x)) ≤
      x ⬝ᵥ (Q (k + 1) *ᵥ x) ∧
      x ⬝ᵥ (Q (k + 1) *ᵥ x) ≤ 4 * (x ⬝ᵥ (Q k *ᵥ x)))
    (k : ℕ) (x : ι → ℝ) :
    (r * (1 / 4 : ℝ) ^ k) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Q k *ᵥ x) ∧
      x ⬝ᵥ (Q k *ᵥ x) ≤ (R * 4 ^ k) * (x ⬝ᵥ x) := by
  induction k with
  | zero => simpa using hinit x
  | succ k ih =>
      have hs := hstep k x
      constructor
      · calc
          _ = (1 / 4 : ℝ) * ((r * (1 / 4 : ℝ) ^ k) * (x ⬝ᵥ x)) := by
            rw [pow_succ]; ring
          _ ≤ (1 / 4 : ℝ) * (x ⬝ᵥ (Q k *ᵥ x)) :=
            mul_le_mul_of_nonneg_left ih.1 (by norm_num)
          _ ≤ _ := hs.1
      · calc
          _ ≤ 4 * (x ⬝ᵥ (Q k *ᵥ x)) := hs.2
          _ ≤ 4 * ((R * 4 ^ k) * (x ⬝ᵥ x)) :=
            mul_le_mul_of_nonneg_left ih.2 (by norm_num)
          _ = _ := by rw [pow_succ]; ring

/-- An exponentially fine dyadic grid has a linearly sized denominator. -/
theorem dyadic_precision_size (lowerExponent errorExponent n : ℕ) :
    Nat.size (2 ^ (lowerExponent + errorExponent + n + 1)) =
      lowerExponent + errorExponent + n + 2 := by
  rw [Nat.size_pow]

/-- A concrete dyadic denominator suffices for relative shape error.
The required bit precision is linear in the conditioning exponent and dimension. -/
theorem dyadic_shape_precision (l s n : ℕ) :
    2 * (n : ℝ) / (2 : ℝ) ^ (l + s + n + 1) ≤
      ((2 : ℝ) ^ s)⁻¹ * ((2 : ℝ) ^ l)⁻¹ := by
  have hn : (n : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have hpow : (0 : ℝ) < 2 ^ (l + s + n + 1) := by positivity
  apply (div_le_iff₀ hpow).mpr
  simp only [pow_add, pow_one]
  have hl : (2 : ℝ) ^ l ≠ 0 := by positivity
  have hs : (2 : ℝ) ^ s ≠ 0 := by positivity
  field_simp
  nlinarith

end Lax109476Proofs.EllipsoidBounds

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

/-!
Internal lemmas for the ellipsoid algorithm. These establish the normalized
central-cut matrix update, containment, and determinant shrink factor. They do not yet
establish a rounded rational algorithm or a RAM runtime bound.
-/

namespace Lax109476Proofs.EllipsoidStep

/-- The updated ellipsoid's quadratic form in coordinates parallel and
perpendicular to a unit cut normal. -/
noncomputable def centralCutForm (n r t : ℝ) : ℝ :=
  (n + 1) ^ 2 / n ^ 2 * (t + 1 / (n + 1)) ^ 2 +
    (n ^ 2 - 1) / n ^ 2 * (r - t ^ 2)

/-- The updated ellipsoid contains the cut half of the original unit ball. -/
theorem centralCutForm_le_one (n r t : ℝ) (hn : 2 ≤ n)
    (hr : r ≤ 1) (ht₁ : -1 ≤ t) (ht₂ : t ≤ 0) :
    centralCutForm n r t ≤ 1 := by
  have hnpos : 0 < n := by linarith
  have hnzero : n ≠ 0 := ne_of_gt hnpos
  have hnplus : n + 1 ≠ 0 := by linarith
  have hid : centralCutForm n r t =
      ((n ^ 2 - 1) * r + 2 * (n + 1) * t * (t + 1) + 1) / n ^ 2 := by
    unfold centralCutForm
    field_simp
    ring
  rw [hid]
  apply (div_le_one (sq_pos_of_pos hnpos)).mpr
  have hcoeff : 0 ≤ n ^ 2 - 1 := by nlinarith
  have hrad := mul_le_mul_of_nonneg_left hr hcoeff
  have htprod : t * (t + 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg ht₂ (by linarith)
  have hterm : 2 * (n + 1) * (t * (t + 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) htprod
  nlinarith

/-- Coordinate-free containment, using the Cauchy–Schwarz inequality. -/
theorem centralCut_contains_half_ball {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (n : ℝ) (hn : 2 ≤ n) (u x : E)
    (hu : inner ℝ u u = 1) (hx : inner ℝ x x ≤ 1)
    (hcut : inner ℝ u x ≤ 0) :
    centralCutForm n (inner ℝ x x) (inner ℝ u x) ≤ 1 := by
  have hcs := real_inner_mul_inner_self_le u x
  rw [hu, one_mul] at hcs
  have ht : -1 ≤ inner ℝ u x := by nlinarith
  exact centralCutForm_le_one n _ _ hn hx ht hcut

/-- The determinant factor for the normalized central-cut shape update. -/
noncomputable def determinantFactor (n : ℕ) : ℝ :=
  ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ (n - 1) *
    ((n : ℝ) / ((n : ℝ) + 1)) ^ 2

/-- A positive determinant shrink factor in dimension at least two. -/
theorem determinantFactor_pos (n : ℕ) (hn : 2 ≤ n) : 0 < determinantFactor n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold determinantFactor
  apply mul_pos
  · apply pow_pos
    apply div_pos <;> nlinarith
  · apply sq_pos_of_pos
    apply div_pos <;> linarith

/-- One central cut decreases log determinant by at least `1 / (n + 1)`. -/
theorem log_determinantFactor_le (n : ℕ) (hn : 2 ≤ n) :
    Real.log (determinantFactor n) ≤ -1 / ((n : ℝ) + 1) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : 0 < (n : ℝ) := by linarith
  have hplus : 0 < (n : ℝ) + 1 := by linarith
  have hdiff : 0 < (n : ℝ) ^ 2 - 1 := by nlinarith
  let a := (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)
  let b := (n : ℝ) / ((n : ℝ) + 1)
  have ha : 0 < a := div_pos (sq_pos_of_pos hnp) hdiff
  have hb : 0 < b := div_pos hnp hplus
  have hlogA := Real.log_le_sub_one_of_pos ha
  have hlogB := Real.log_le_sub_one_of_pos hb
  have hk : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have heqA : ((n - 1 : ℕ) : ℝ) * (a - 1) = 1 / ((n : ℝ) + 1) := by
    rw [hk]
    dsimp [a]
    field_simp
    ring
  have heqB : 2 * (b - 1) = -2 / ((n : ℝ) + 1) := by
    dsimp [b]
    field_simp
    ring
  have hA := mul_le_mul_of_nonneg_left hlogA (Nat.cast_nonneg (n - 1))
  have hB := mul_le_mul_of_nonneg_left hlogB (show (0 : ℝ) ≤ 2 by norm_num)
  rw [heqA] at hA
  rw [heqB] at hB
  change Real.log (a ^ (n - 1) * b ^ 2) ≤ _
  rw [Real.log_mul (ne_of_gt (pow_pos ha _)) (ne_of_gt (sq_pos_of_pos hb)),
    Real.log_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  calc
    _ ≤ 1 / ((n : ℝ) + 1) + -2 / ((n : ℝ) + 1) := add_le_add hA hB
    _ = -1 / ((n : ℝ) + 1) := by ring

/-- The square root of the determinant factor has an exponential upper bound. -/
theorem sqrt_determinantFactor_le (n : ℕ) (hn : 2 ≤ n) :
    Real.sqrt (determinantFactor n) ≤ Real.exp (-1 / (2 * ((n : ℝ) + 1))) := by
  have hp := determinantFactor_pos n hn
  have hlog := log_determinantFactor_le n hn
  have hsqrt := Real.sqrt_pos.mpr hp
  have hbound : Real.log (Real.sqrt (determinantFactor n)) ≤
      -1 / (2 * ((n : ℝ) + 1)) := by
    rw [Real.log_sqrt (le_of_lt hp)]
    calc
      _ ≤ (-1 / ((n : ℝ) + 1)) / 2 :=
        div_le_div_of_nonneg_right hlog (by norm_num)
      _ = -1 / (2 * ((n : ℝ) + 1)) := by
        field_simp
  simpa only [Real.exp_log hsqrt] using Real.exp_le_exp.mpr hbound

open Matrix

/-- A rank-one contraction of the identity stays positive definite below unit weight. -/
theorem rankOneCut_posDef {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (hu : u ⬝ᵥ u = 1) (β : ℝ) (hβ : 0 ≤ β) (hβ₁ : β < 1) :
    (1 - β • Matrix.vecMulVec u u).PosDef := by
  have hsym : (1 - β • Matrix.vecMulVec u u).IsHermitian := by
    rw [Matrix.isHermitian_iff_isSymm, Matrix.IsSymm.ext_iff]
    intro i j
    simp [Matrix.vecMulVec, Matrix.one_apply, eq_comm, mul_comm]
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hsym
  intro x hx
  have hxx : 0 < x ⬝ᵥ x := by
    simpa using (dotProduct_star_self_pos_iff (v := x)).mpr hx
  have hcs : (u ⬝ᵥ x) ^ 2 ≤ x ⬝ᵥ x := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u x
    have h' : (u ⬝ᵥ x) ^ 2 ≤ (u ⬝ᵥ u) * (x ⬝ᵥ x) := by
      simpa only [dotProduct, pow_two] using h
    simpa only [hu, one_mul] using h'
  have heq : star x ⬝ᵥ ((1 - β • Matrix.vecMulVec u u) *ᵥ x) =
      x ⬝ᵥ x - β * (u ⬝ᵥ x) ^ 2 := by
    simp [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
      dotProduct_sub, dotProduct_smul, dotProduct_comm, pow_two]
  rw [heq]
  have hle := mul_le_mul_of_nonneg_left hcs hβ
  have hstrict := mul_lt_mul_of_pos_right hβ₁ hxx
  nlinarith

/-- The shape matrix for a central cut of the unit ball with normal `u`. -/
noncomputable def centralCutShape (n : ℕ) (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
    (1 - (2 / ((n : ℝ) + 1)) • Matrix.vecMulVec u u)

/-- The normalized central-cut update is a valid positive definite shape matrix. -/
theorem centralCutShape_posDef (n : ℕ) (hn : 2 ≤ n) (u : Fin n → ℝ)
    (hu : u ⬝ᵥ u = 1) : (centralCutShape n u).PosDef := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hplus : 0 < (n : ℝ) + 1 := by linarith
  have hβ : 0 ≤ 2 / ((n : ℝ) + 1) := by positivity
  have hβ₁ : 2 / ((n : ℝ) + 1) < 1 := (div_lt_one hplus).mpr (by linarith)
  apply (rankOneCut_posDef u hu _ hβ hβ₁).smul
  apply div_pos <;> nlinarith

/-- Explicit inverse of the normalized central-cut shape matrix. -/
theorem centralCutShape_inv (n : ℕ) (hn : 2 ≤ n) (u : Fin n → ℝ)
    (hu : u ⬝ᵥ u = 1) :
    (centralCutShape n u)⁻¹ =
      (((n : ℝ) ^ 2 - 1) / (n : ℝ) ^ 2) •
        (1 + (2 / ((n : ℝ) - 1)) • Matrix.vecMulVec u u) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnzero : (n : ℝ) ≠ 0 := by linarith
  have hminus : (n : ℝ) - 1 ≠ 0 := by linarith
  have hplus : (n : ℝ) + 1 ≠ 0 := by linarith
  have hdiff : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hUU : Matrix.vecMulVec u u * Matrix.vecMulVec u u = Matrix.vecMulVec u u := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hu, one_smul]
  apply Matrix.inv_eq_right_inv
  unfold centralCutShape
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hc : (((n : ℝ) ^ 2 - 1) / (n : ℝ) ^ 2) *
      ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) = 1 := by
    field_simp
  rw [hc, one_smul]
  simp only [mul_add, sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, hUU]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- The inverse-matrix test agrees with the parallel/perpendicular calculation. -/
theorem centralCutShape_quadratic (n : ℕ) (hn : 2 ≤ n) (u x : Fin n → ℝ)
    (hu : u ⬝ᵥ u = 1) :
    let z := x + (1 / ((n : ℝ) + 1)) • u
    z ⬝ᵥ ((centralCutShape n u)⁻¹ *ᵥ z) =
      centralCutForm n (x ⬝ᵥ x) (u ⬝ᵥ x) := by
  let s := 1 / ((n : ℝ) + 1)
  let z := x + s • u
  have hzz : z ⬝ᵥ z = x ⬝ᵥ x + 2 * s * (u ⬝ᵥ x) + s ^ 2 := by
    dsimp [z]
    simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct,
      hu, smul_eq_mul, dotProduct_comm x u]
    ring
  have huz : u ⬝ᵥ z = u ⬝ᵥ x + s := by
    simp [z, dotProduct_add, dotProduct_smul, hu]
  change z ⬝ᵥ ((centralCutShape n u)⁻¹ *ᵥ z) = _
  rw [centralCutShape_inv n hn u hu]
  simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec, dotProduct_smul, dotProduct_add,
    op_smul_eq_smul, smul_eq_mul, dotProduct_comm z u]
  rw [hzz, huz]
  dsimp [centralCutForm, s]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnzero : (n : ℝ) ≠ 0 := by linarith
  have hminus : (n : ℝ) - 1 ≠ 0 := by linarith
  have hplus : (n : ℝ) + 1 ≠ 0 := by linarith
  field_simp
  ring

/-- Matrix-form containment for every point in the cut half of the unit ball. -/
theorem centralCutShape_contains (n : ℕ) (hn : 2 ≤ n) (u x : Fin n → ℝ)
    (hu : u ⬝ᵥ u = 1) (hx : x ⬝ᵥ x ≤ 1) (hcut : u ⬝ᵥ x ≤ 0) :
    let z := x + (1 / ((n : ℝ) + 1)) • u
    z ⬝ᵥ ((centralCutShape n u)⁻¹ *ᵥ z) ≤ 1 := by
  dsimp only
  rw [centralCutShape_quadratic n hn u x hu]
  have hcs : (u ⬝ᵥ x) ^ 2 ≤ x ⬝ᵥ x := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u x
    have h' : (u ⬝ᵥ x) ^ 2 ≤ (u ⬝ᵥ u) * (x ⬝ᵥ x) := by
      simpa only [dotProduct, pow_two] using h
    simpa only [hu, one_mul] using h'
  apply centralCutForm_le_one n _ _ (by exact_mod_cast hn) hx _ hcut
  nlinarith

/-- The determinant lemma identifies the scalar factor with the actual update. -/
theorem det_centralCutShape (n : ℕ) (hn : 2 ≤ n) (u : Fin n → ℝ)
    (hu : u ⬝ᵥ u = 1) : (centralCutShape n u).det = determinantFactor n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  let a := (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)
  let β := 2 / ((n : ℝ) + 1)
  have hd : (1 - β • Matrix.vecMulVec u u).det = 1 - β := by
    have h := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Unit) u (-β • u)
    simpa [← Matrix.vecMulVec_eq Unit, dotProduct_smul, hu, sub_eq_add_neg,
      neg_smul] using h
  change (a • (1 - β • Matrix.vecMulVec u u)).det = _
  rw [Matrix.det_smul, Fintype.card_fin, hd]
  have hfactor : a * (1 - β) = ((n : ℝ) / ((n : ℝ) + 1)) ^ 2 := by
    dsimp [a, β]
    have hplus : (n : ℝ) + 1 ≠ 0 := by linarith
    have hdiff : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp
    ring
  unfold determinantFactor
  calc
    _ = a ^ (n - 1) * (a * (1 - β)) := by
      nth_rewrite 1 [show n = (n - 1) + 1 by omega]
      rw [pow_succ]
      ring
    _ = _ := by rw [hfactor]

/-- A small uniform enlargement preserves a quantitative determinant shrink bound.
This is the margin available to a subsequent rational-rounding construction. -/
theorem enlarged_shrink_bound (n : ℕ) (hn : 2 ≤ n) (δ : ℝ) (hδ : 0 ≤ δ)
    (hδsmall : δ ≤ 1 / (4 * (n : ℝ) * ((n : ℝ) + 1))) :
    (1 + δ) ^ n * Real.sqrt (determinantFactor n) ≤
      Real.exp (-1 / (4 * ((n : ℝ) + 1))) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : 0 < (n : ℝ) := by linarith
  have hplus : 0 < (n : ℝ) + 1 := by linarith
  have hbase : 0 < 1 + δ := by linarith
  have hsqrt := Real.sqrt_pos.mpr (determinantFactor_pos n hn)
  have hlogbase : Real.log (1 + δ) ≤ δ := by
    simpa using Real.log_le_sub_one_of_pos hbase
  have hlogshrink : Real.log (Real.sqrt (determinantFactor n)) ≤
      -1 / (2 * ((n : ℝ) + 1)) := by
    rw [Real.log_sqrt (le_of_lt (determinantFactor_pos n hn))]
    calc
      _ ≤ (-1 / ((n : ℝ) + 1)) / 2 :=
        div_le_div_of_nonneg_right (log_determinantFactor_le n hn) (by norm_num)
      _ = _ := by field_simp
  have hδmul : (n : ℝ) * δ ≤ 1 / (4 * ((n : ℝ) + 1)) := by
    calc
      _ ≤ (n : ℝ) * (1 / (4 * (n : ℝ) * ((n : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hδsmall (le_of_lt hnp)
      _ = _ := by field_simp
  have hlogbound : Real.log ((1 + δ) ^ n * Real.sqrt (determinantFactor n)) ≤
      -1 / (4 * ((n : ℝ) + 1)) := by
    rw [Real.log_mul (ne_of_gt (pow_pos hbase n)) (ne_of_gt hsqrt), Real.log_pow]
    calc
      _ ≤ (n : ℝ) * δ + -1 / (2 * ((n : ℝ) + 1)) :=
        add_le_add (mul_le_mul_of_nonneg_left hlogbase (le_of_lt hnp)) hlogshrink
      _ ≤ 1 / (4 * ((n : ℝ) + 1)) + -1 / (2 * ((n : ℝ) + 1)) :=
        add_le_add hδmul (le_refl _)
      _ = _ := by field_simp; ring
  simpa only [Real.exp_log (mul_pos (pow_pos hbase n) hsqrt)] using
    Real.exp_le_exp.mpr hlogbound

/-- Iterating the determinant bound gives geometric contraction. -/
theorem iterated_shrink_bound (n : ℕ) (v : ℕ → ℝ)
    (hstep : ∀ k, v (k + 1) ≤ Real.exp (-1 / (4 * ((n : ℝ) + 1))) * v k)
    (k : ℕ) :
    v k ≤ Real.exp (-(k : ℝ) / (4 * ((n : ℝ) + 1))) * v 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        _ ≤ Real.exp (-1 / (4 * ((n : ℝ) + 1))) * v k := hstep k
        _ ≤ Real.exp (-1 / (4 * ((n : ℝ) + 1))) *
            (Real.exp (-(k : ℝ) / (4 * ((n : ℝ) + 1))) * v 0) :=
          mul_le_mul_of_nonneg_left ih (le_of_lt (Real.exp_pos _))
        _ = _ := by
          rw [← mul_assoc, ← Real.exp_add]
          congr 2
          push_cast
          ring

end Lax109476Proofs.EllipsoidStep

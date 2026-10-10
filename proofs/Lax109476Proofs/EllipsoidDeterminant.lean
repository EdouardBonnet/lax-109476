import Lax109476Proofs.EllipsoidBounds
import Mathlib.Analysis.Matrix.Order

/-! Determinant bounds from quadratic-form comparison, used for rounded updates. -/

namespace Lax109476Proofs.EllipsoidDeterminant

open Matrix EllipsoidRounding

/-- A uniform form upper bound bounds each eigenvalue, without choosing coordinates. -/
theorem eigenvalue_le_of_form_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (k : ℝ)
    (hbound : ∀ x, x ⬝ᵥ (A *ᵥ x) ≤ k * (x ⬝ᵥ x)) (i : ι) :
    hA.eigenvalues i ≤ k := by
  let v : ι → ℝ := (hA.eigenvectorBasis i).ofLp
  have hv : v ≠ 0 := by
    intro h
    apply hA.eigenvectorBasis.toBasis.ne_zero i
    ext j
    exact congrFun h j
  have hxx : 0 < v ⬝ᵥ v := by
    simpa using (dotProduct_star_self_pos_iff (v := v)).mpr hv
  have he : A *ᵥ v = hA.eigenvalues i • v := hA.mulVec_eigenvectorBasis i
  have h := hbound v
  rw [he, dotProduct_smul, smul_eq_mul] at h
  exact (mul_le_mul_iff_of_pos_right hxx).mp h

/-- A positive semidefinite shape bounded by `k I` has determinant at most `kⁿ`. -/
theorem det_le_pow_of_form_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (k : ℝ)
    (hbound : ∀ x, x ⬝ᵥ (A *ᵥ x) ≤ k * (x ⬝ᵥ x)) :
    A.det ≤ k ^ Fintype.card ι := by
  rw [hA.1.det_eq_prod_eigenvalues]
  simpa [RCLike.ofReal_real_eq_id] using Finset.prod_le_prod
    (s := Finset.univ (α := ι)) (g := fun _ => k)
    (fun i _ => hA.eigenvalues_nonneg i)
    (fun i _ => eigenvalue_le_of_form_bound hA.1 k hbound i)

/-- Relative quadratic-form error bounds relative determinant error.
The real square root is a proof device, not part of the rational algorithm. -/
theorem det_le_relative_pow {ι : Type} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) (k : ℝ)
    (hbound : ∀ x, x ⬝ᵥ (B *ᵥ x) ≤ k * (x ⬝ᵥ (A *ᵥ x))) :
    B.det ≤ k ^ Fintype.card ι * A.det := by
  open scoped MatrixOrder in
  have hsqrt : ∃ R : Matrix ι ι ℝ, R.IsHermitian ∧ IsUnit R ∧ R * R = A := by
    let R := CFC.sqrt A
    have hRR : R * R = A := by
      simpa only [pow_two] using CFC.sq_sqrt A hA.posSemidef.nonneg
    have hu : IsUnit (R * R) := hRR.symm ▸ hA.isUnit
    exact ⟨R, (CFC.sqrt_nonneg A).posSemidef.1,
      isUnit_of_mul_isUnit_left hu, hRR⟩
  obtain ⟨R, hR, hu, hRR⟩ := hsqrt
  have hRinv : R⁻¹.IsHermitian := hR.inv
  have hRi : IsUnit R⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hu
  have hRRi : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R
    ((Matrix.isUnit_iff_isUnit_det R).mp hu)
  have hRiR : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R
    ((Matrix.isUnit_iff_isUnit_det R).mp hu)
  let C := R⁻¹ * B * R⁻¹
  have hC : C.PosDef := by
    simpa only [hRinv.eq] using hB.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit hRi)
  have hid : R⁻¹ * A * R⁻¹ = 1 := by
    rw [← hRR, ← Matrix.mul_assoc, hRiR, Matrix.one_mul, hRRi]
  have hform (M : Matrix ι ι ℝ) (x : ι → ℝ) :
      x ⬝ᵥ ((R⁻¹ * M * R⁻¹) *ᵥ x) =
        (R⁻¹ *ᵥ x) ⬝ᵥ (M *ᵥ (R⁻¹ *ᵥ x)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact (symmetric_form hRinv x (M *ᵥ (R⁻¹ *ᵥ x))).trans (dotProduct_comm _ _)
  have hb : ∀ x, x ⬝ᵥ (C *ᵥ x) ≤ k * (x ⬝ᵥ x) := by
    intro x
    have h := hbound (R⁻¹ *ᵥ x)
    rw [← hform B x, ← hform A x, hid, Matrix.one_mulVec] at h
    exact h
  have hc := det_le_pow_of_form_bound hC.posSemidef k hb
  have hdet : B.det = C.det * A.det := by
    dsimp [C]
    rw [Matrix.det_mul, Matrix.det_mul, ← hRR, Matrix.det_mul]
    have hd : R.det * (R⁻¹).det = 1 := by
      rw [← Matrix.det_mul, hRRi, Matrix.det_one]
    calc
      _ = B.det * (R.det * (R⁻¹).det) ^ 2 := by rw [hd]; ring
      _ = _ := by ring
  rw [hdet]
  exact mul_le_mul_of_nonneg_right hc (le_of_lt hA.det_pos)

end Lax109476Proofs.EllipsoidDeterminant

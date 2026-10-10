import Lax109476Proofs.EllipsoidDeterminant

open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidBall

open Matrix EllipsoidRounding EllipsoidDeterminant

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem quadratic_parallelogram (A : Matrix ι ι ℝ) (u v : ι → ℝ) :
    (u + v) ⬝ᵥ (A *ᵥ (u + v)) + (u - v) ⬝ᵥ (A *ᵥ (u - v)) =
      2 * (u ⬝ᵥ (A *ᵥ u)) + 2 * (v ⬝ᵥ (A *ᵥ v)) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, sub_dotProduct,
    dotProduct_add, dotProduct_sub]
  ring

/-- If a whole ball lies in an ellipsoid, its radius bounds the inverse shape
form. The ball and ellipsoid may have different centers. -/
theorem inverse_form_bound_of_ball {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (z c : ι → ℝ) (r : ℝ) (hr : 0 < r)
    (hball : ∀ e : ι → ℝ, e ⬝ᵥ e ≤ r ^ 2 →
      (z + e - c) ⬝ᵥ (A⁻¹ *ᵥ (z + e - c)) ≤ 1) :
    ∀ u : ι → ℝ, u ⬝ᵥ (A⁻¹ *ᵥ u) ≤ (r ^ 2)⁻¹ * (u ⬝ᵥ u) := by
  intro u
  by_cases hu : u = 0
  · simp [hu]
  have hnorm : 0 < u ⬝ᵥ u := by
    simpa using (dotProduct_star_self_pos_iff (v := u)).mpr hu
  let t := r / Real.sqrt (u ⬝ᵥ u)
  let e := t • u
  have ht : 0 < t := div_pos hr (Real.sqrt_pos.mpr hnorm)
  have hsq : (Real.sqrt (u ⬝ᵥ u)) ^ 2 = u ⬝ᵥ u := Real.sq_sqrt hnorm.le
  have he : e ⬝ᵥ e = r ^ 2 := by
    simp only [e, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    dsimp [t]
    field_simp
    nlinarith
  have hp := hball e he.le
  have hm := hball (-e) (by simpa using he.le)
  have hbase : 0 ≤ (z - c) ⬝ᵥ (A⁻¹ *ᵥ (z - c)) :=
    hA.inv.posSemidef.dotProduct_mulVec_nonneg _
  have hid := quadratic_parallelogram A⁻¹ (z - c) e
  have hp' : ((z - c) + e) ⬝ᵥ (A⁻¹ *ᵥ ((z - c) + e)) ≤ 1 := by
    have heq : (z - c) + e = z + e - c := by abel_nf
    rw [heq]
    exact hp
  have hm' : ((z - c) - e) ⬝ᵥ (A⁻¹ *ᵥ ((z - c) - e)) ≤ 1 := by
    have heq : (z - c) - e = z + -e - c := by abel_nf
    rw [heq]
    exact hm
  have hqe : e ⬝ᵥ (A⁻¹ *ᵥ e) ≤ 1 := by linarith
  have hqe' : t ^ 2 * (u ⬝ᵥ (A⁻¹ *ᵥ u)) ≤ 1 := by
    simpa only [e, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, ← mul_assoc, ← pow_two] using hqe
  have htform : t ^ 2 = r ^ 2 / (u ⬝ᵥ u) := by
    dsimp [t]
    rw [div_pow, hsq]
  rw [htform, div_mul_eq_mul_div] at hqe'
  have hscale : r ^ 2 * (u ⬝ᵥ (A⁻¹ *ᵥ u)) ≤ u ⬝ᵥ u :=
    (div_le_one hnorm).mp hqe'
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ (sq_pos_of_pos hr)).mpr (by simpa [mul_comm] using hscale)

/-- Containing a ball forces the determinant proxy used by the algorithm to
be at least the radius to the dimension. -/
theorem sqrt_det_lower_bound_of_ball {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (z c : ι → ℝ) (r : ℝ) (hr : 0 < r)
    (hball : ∀ e : ι → ℝ, e ⬝ᵥ e ≤ r ^ 2 →
      (z + e - c) ⬝ᵥ (A⁻¹ *ᵥ (z + e - c)) ≤ 1) :
    r ^ Fintype.card ι ≤ Real.sqrt A.det := by
  have hbound := inverse_form_bound_of_ball hA z c r hr hball
  have hdet := det_le_pow_of_form_bound hA.inv.posSemidef ((r ^ 2)⁻¹) hbound
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, inv_pow] at hdet
  have ha := hA.det_pos
  have hrpow : 0 < (r ^ 2) ^ Fintype.card ι := pow_pos (sq_pos_of_pos hr) _
  have hd : (r ^ 2) ^ Fintype.card ι ≤ A.det := (inv_le_inv₀ ha hrpow).mp hdet
  have hs := Real.sq_sqrt ha.le
  have hsr := Real.sqrt_nonneg A.det
  have hrr : (r ^ Fintype.card ι) ^ 2 = (r ^ 2) ^ Fintype.card ι := by ring
  nlinarith [pow_nonneg hr.le (Fintype.card ι)]

end Lax109476Proofs.EllipsoidBall

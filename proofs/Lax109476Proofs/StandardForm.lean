import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.WellFounded
import Mathlib.Tactic

/-! Independent supports and exact coordinate recovery for standard-form systems.
These lemmas do not assume a linear-programming solver. -/

open scoped BigOperators Matrix

namespace Lax109476Proofs.StandardForm

variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℚ E]

noncomputable def support (x : ι → ℚ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => x i ≠ 0)

theorem mem_support (x : ι → ℚ) (i : ι) : i ∈ support x ↔ x i ≠ 0 := by
  classical
  simp [support]

private theorem positive_relation (v : ι → E) (s : Finset ι)
    (h : ¬ LinearIndepOn ℚ v (s : Set ι)) :
    ∃ d : ι → ℚ, (∀ i, i ∉ s → d i = 0) ∧
      (∑ i, d i • v i) = 0 ∧ ∃ i ∈ s, 0 < d i := by
  classical
  obtain ⟨g, hg, i, hi, hgi⟩ := not_linearIndepOn_finset_iff.mp h
  let f : ι → ℚ := fun j => if j ∈ s then g j else 0
  have hf : (∑ j, f j • v j) = 0 := by
    simpa [f, ← Finset.sum_filter] using hg
  by_cases hp : 0 < g i
  · exact ⟨f, by intro j hj; simp [f, hj], hf, i, hi,
      by simpa [f, hi] using hp⟩
  · refine ⟨-f, ?_, ?_, i, hi, ?_⟩
    · intro j hj
      simp [f, hj]
    · simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hf, neg_zero]
    · simp only [Pi.neg_apply, f, if_pos hi]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) hgi)

/-- A nonnegative conic representation can be chosen with independent support.
The proof removes a column whenever a dependence permits movement to the
boundary of the nonnegative orthant. -/
theorem exists_independent_support (v : ι → E) (b : E)
    (h : ∃ x : ι → ℚ, (∀ i, 0 ≤ x i) ∧ ∑ i, x i • v i = b) :
    ∃ x : ι → ℚ, (∀ i, 0 ≤ x i) ∧ (∑ i, x i • v i) = b ∧
      LinearIndepOn ℚ v (support x : Set ι) := by
  classical
  let S : Set (ι → ℚ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i • v i = b}
  let x := Function.argminOn (fun x : ι → ℚ => (support x).card) S h
  have hx : x ∈ S := Function.argminOn_mem _ S h
  have hmin : ∀ y ∈ S, (support x).card ≤ (support y).card :=
    fun y hy => Function.argminOn_le (fun x : ι → ℚ => (support x).card) S hy
  refine ⟨x, hx.1, hx.2, ?_⟩
  by_contra hdep
  obtain ⟨d, hd, hsum, i₀, hi₀, hdi₀⟩ := positive_relation v (support x) hdep
  let s := (support x).filter (fun i => 0 < d i)
  obtain ⟨i, hi, hratio⟩ := s.exists_min_image (fun j => x j / d j)
    ⟨i₀, by simp [s, hi₀, hdi₀]⟩
  have his : i ∈ support x := (Finset.mem_filter.mp hi).1
  have hdi : 0 < d i := (Finset.mem_filter.mp hi).2
  let t := x i / d i
  have ht : 0 ≤ t := div_nonneg (hx.1 i) hdi.le
  let y : ι → ℚ := fun j => x j - t * d j
  have hypos : ∀ j, 0 ≤ y j := by
    intro j
    by_cases hj : 0 < d j
    · have hjs : j ∈ support x := by
        by_contra hn
        rw [hd j hn] at hj
        exact (lt_irrefl 0) hj
      have hr := hratio j (Finset.mem_filter.mpr ⟨hjs, hj⟩)
      exact sub_nonneg.mpr ((le_div_iff₀ hj).mp hr)
    · exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos ht
        (le_of_not_gt hj)).trans (hx.1 j))
  have hyb : (∑ j, y j • v j) = b := by
    simp only [y, sub_smul, mul_smul, Finset.sum_sub_distrib,
      ← Finset.smul_sum, hsum, smul_zero, sub_zero]
    exact hx.2
  have hyi : y i = 0 := by simp [y, t, ne_of_gt hdi]
  have hsub : support y ⊆ (support x).erase i := by
    intro j hj
    have hyj := (mem_support y j).mp hj
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · intro heq
      subst j
      exact hyj hyi
    · by_contra hn
      have hxj : x j = 0 := by simpa [mem_support] using hn
      exact hyj (by simp [y, hxj, hd j hn])
  have hc := (hmin y ⟨hypos, hyb⟩).trans (Finset.card_le_card hsub)
  have hlt := Finset.card_erase_lt_of_mem his
  omega

section Matrices

variable {κ : Type*} [Fintype κ] [DecidableEq ι]

/-- An independent rational column family has an invertible Gram matrix.
Only ordered-field arithmetic is used; no square root is computed. -/
theorem gram_det_ne_zero (C : Matrix κ ι ℚ)
    (hC : LinearIndependent ℚ C.col) : (Cᵀ * C).det ≠ 0 := by
  classical
  have hc := Matrix.mulVec_injective_iff.mpr hC
  have hg : Function.Injective (Cᵀ * C).mulVec := by
    intro x y hxy
    let z := x - y
    have hz : (Cᵀ * C) *ᵥ z = 0 := by
      simp only [z, Matrix.mulVec_sub, hxy, sub_self]
    have hnorm : dotProduct (C *ᵥ z) (C *ᵥ z) = 0 := by
      have heq : dotProduct z ((Cᵀ * C) *ᵥ z) =
          dotProduct (C *ᵥ z) (C *ᵥ z) := by
        rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      rw [← heq, hz, dotProduct_zero]
    have hcz : C *ᵥ z = 0 := by
      funext i
      exact (Finset.sum_mul_self_eq_zero_iff Finset.univ (C *ᵥ z)).mp hnorm i
        (Finset.mem_univ i)
    have hz0 : z = 0 := hc (by simpa using hcz)
    exact sub_eq_zero.mp hz0
  exact ((Cᵀ * C).isUnit_iff_isUnit_det.mp
    (Matrix.mulVec_injective_iff_isUnit.mp hg)).ne_zero

omit [DecidableEq ι] in
/-- An independent representation is uniquely recovered by a square rational
system, even when the original matrix is rectangular. -/
theorem gram_recovers (C : Matrix κ ι ℚ) (b : κ → ℚ) (x : ι → ℚ)
    (hx : C *ᵥ x = b) : (Cᵀ * C) *ᵥ x = Cᵀ *ᵥ b := by
  rw [← Matrix.mulVec_mulVec, hx]

end Matrices

end Lax109476Proofs.StandardForm

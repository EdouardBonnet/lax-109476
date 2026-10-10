import Lax109476Proofs.StandardForm
import Lax109476Proofs.DeterminantBounds

open scoped BigOperators Matrix

namespace Lax109476Proofs.SmallFeasiblePoint

open StandardForm DeterminantBounds

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

/-- Cramer's rule bounds reduced rational coordinates directly by integer
determinants, without assuming an algorithm for finding the solution. -/
theorem integer_system_coordinate_bound (A : Matrix ι ι ℤ) (b : ι → ℤ)
    (x : ι → ℚ) (H : ℕ) (hA : ∀ i j, (A i j).natAbs ≤ H)
    (hb : ∀ i, (b i).natAbs ≤ H) (hdet : A.det ≠ 0)
    (hx : (A.map (fun z => (z : ℚ))) *ᵥ x = fun i => (b i : ℚ)) :
    ∀ j, (x j).num.natAbs ≤ (Fintype.card ι).factorial * H ^ Fintype.card ι ∧
      (x j).den ≤ (Fintype.card ι).factorial * H ^ Fintype.card ι := by
  let Q : Matrix ι ι ℚ := A.map (fun z => (z : ℚ))
  let r : ι → ℚ := fun i => (b i : ℚ)
  have hxr : Q *ᵥ x = r := hx
  have hcr : Q.det • x = Q.cramer r := by
    rw [Matrix.cramer_eq_adjugate_mulVec, ← hxr, Matrix.mulVec_mulVec,
      Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hd : (A.det : ℚ) ≠ 0 := by exact_mod_cast hdet
  intro j
  have hupdate : Q.updateCol j r =
      (A.updateCol j b).map (fun z => (z : ℚ)) :=
    (Matrix.map_updateCol (M := A) (j := j) (c := b) (fun z => (z : ℚ))).symm
  have heq : (A.det : ℚ) * x j = ((A.updateCol j b).det : ℚ) := by
    have h := congrFun hcr j
    simpa only [Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply, hupdate,
      Q, ← Int.cast_det] using h
  have hxj : x j = ((A.updateCol j b).det : ℚ) / (A.det : ℚ) := by
    apply (eq_div_iff hd).mpr
    simpa only [mul_comm] using heq
  rw [hxj]
  obtain ⟨hn, hdn⟩ := integer_ratio_num_den_bound (A.updateCol j b).det A.det hdet
  refine ⟨hn.trans (determinant_bound _ H ?_),
    hdn.trans (determinant_bound A H hA)⟩
  intro i k
  simp only [Matrix.updateCol_apply]
  split_ifs <;> first | exact hb i | exact hA i k

/-- Gram entries and right-hand-side entries grow by at most the number of
original rows times the square of the original integer magnitude bound. -/
theorem integer_gram_entry_bound (C : Matrix κ ι ℤ) (b : κ → ℤ)
    (H : ℕ) (hC : ∀ i j, (C i j).natAbs ≤ H) (hb : ∀ i, (b i).natAbs ≤ H) :
    (∀ i j, ((Cᵀ * C) i j).natAbs ≤ Fintype.card κ * H ^ 2) ∧
      (∀ i, ((Cᵀ *ᵥ b) i).natAbs ≤ Fintype.card κ * H ^ 2) := by
  constructor
  · intro i j
    calc
      _ ≤ ∑ k, (C k i * C k j).natAbs := Int.natAbs_sum_le _ _
      _ ≤ ∑ _k : κ, H ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        rw [Int.natAbs_mul, pow_two]
        exact Nat.mul_le_mul (hC k i) (hC k j)
      _ = _ := by simp
  · intro i
    calc
      _ ≤ ∑ k, (C k i * b k).natAbs := Int.natAbs_sum_le _ _
      _ ≤ ∑ _k : κ, H ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        rw [Int.natAbs_mul, pow_two]
        exact Nat.mul_le_mul (hC k i) (hb k)
      _ = _ := by simp

/-- Bounds for an independent nonnegative solution of a rectangular integer
system follow from Cramer's rule applied to its Gram matrix. -/
theorem independent_integer_coordinate_bound (C : Matrix κ ι ℤ) (b : κ → ℤ)
    (x : ι → ℚ) (H : ℕ) (hC : ∀ i j, (C i j).natAbs ≤ H)
    (hb : ∀ i, (b i).natAbs ≤ H)
    (hind : LinearIndependent ℚ (C.map (fun z => (z : ℚ))).col)
    (hx : (C.map (fun z => (z : ℚ))) *ᵥ x = fun i => (b i : ℚ)) :
    ∀ j, (x j).num.natAbs ≤ (Fintype.card ι).factorial *
        (Fintype.card κ * H ^ 2) ^ Fintype.card ι ∧
      (x j).den ≤ (Fintype.card ι).factorial *
        (Fintype.card κ * H ^ 2) ^ Fintype.card ι := by
  let Q : Matrix κ ι ℚ := C.map (fun z => (z : ℚ))
  have hmap : (Cᵀ * C).map (fun z => (z : ℚ)) = Qᵀ * Q := by
    ext i j
    simp [Matrix.mul_apply, Q]
  have hright : (Qᵀ *ᵥ fun i => (b i : ℚ)) =
      fun i => ((Cᵀ *ᵥ b) i : ℚ) := by
    ext i
    simp [Matrix.mulVec, dotProduct, Q]
  have hdet : (Cᵀ * C).det ≠ 0 := by
    intro h
    have hz : ((Cᵀ * C).det : ℚ) = 0 := by simp [h]
    rw [Int.cast_det, hmap] at hz
    exact gram_det_ne_zero Q hind hz
  have hgram : ((Cᵀ * C).map (fun z => (z : ℚ))) *ᵥ x =
      fun i => ((Cᵀ *ᵥ b) i : ℚ) := by
    rw [hmap, gram_recovers Q _ x hx, hright]
  obtain ⟨hentries, hbound⟩ := integer_gram_entry_bound C b H hC hb
  exact integer_system_coordinate_bound (Cᵀ * C) (Cᵀ *ᵥ b) x
    (Fintype.card κ * H ^ 2) hentries hbound hdet hgram

/-- Every feasible standard-form integer system has a nonnegative rational
solution with uniformly bounded reduced numerators and denominators. -/
theorem exists_bounded_integer_point (A : Matrix κ ι ℤ) (b : κ → ℤ)
    (H : ℕ) (hA : ∀ i j, (A i j).natAbs ≤ H) (hb : ∀ i, (b i).natAbs ≤ H)
    (hf : ∃ x : ι → ℚ, (∀ j, 0 ≤ x j) ∧
      (A.map (fun z => (z : ℚ))) *ᵥ x = fun i => (b i : ℚ)) :
    ∃ x : ι → ℚ, (∀ j, 0 ≤ x j) ∧
      (A.map (fun z => (z : ℚ))) *ᵥ x = (fun i => (b i : ℚ)) ∧
      ∀ j, (x j).num.natAbs ≤ (Fintype.card ι).factorial *
          (Fintype.card κ * H ^ 2 + 1) ^ Fintype.card ι ∧
        (x j).den ≤ (Fintype.card ι).factorial *
          (Fintype.card κ * H ^ 2 + 1) ^ Fintype.card ι := by
  classical
  obtain ⟨x, hxpos, hxeq⟩ := hf
  have hrep : (∑ j, x j • (A.map (fun z => (z : ℚ))).col j) =
      fun i => (b i : ℚ) := by
    ext i
    simpa [Matrix.col, Matrix.mulVec, dotProduct, mul_comm] using congrFun hxeq i
  obtain ⟨z, hzpos, hzeq, hind⟩ := exists_independent_support
    (A.map (fun z => (z : ℚ))).col (fun i => (b i : ℚ)) ⟨x, hxpos, hrep⟩
  let s := support z
  let C : Matrix κ s ℤ := fun i j => A i j.1
  have hcpos : ∀ i j, (C i j).natAbs ≤ H := fun i j => hA i j.1
  have hcind : LinearIndependent ℚ (C.map (fun a => (a : ℚ))).col := hind
  have hzfull : (A.map (fun a => (a : ℚ))) *ᵥ z = fun i => (b i : ℚ) := by
    ext i
    simpa [Matrix.col, Matrix.mulVec, dotProduct, mul_comm] using congrFun hzeq i
  have hceq : (C.map (fun a => (a : ℚ))) *ᵥ (fun j : s => z j.1) =
      fun i => (b i : ℚ) := by
    ext i
    change (∑ j : s, (A i j.1 : ℚ) * z j.1) = (b i : ℚ)
    calc
      _ = ∑ j ∈ s, (A i j : ℚ) * z j := Finset.sum_coe_sort s _
      _ = ∑ j, (A i j : ℚ) * z j := by
        apply Finset.sum_subset (Finset.subset_univ s)
        intro j _ hj
        have hzj : z j = 0 := by simpa [s, mem_support] using hj
        simp [hzj]
      _ = _ := congrFun hzfull i
  have hbnd := independent_integer_coordinate_bound C b (fun j : s => z j.1)
    H hcpos hb hcind hceq
  have hk : Fintype.card s ≤ Fintype.card ι :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hbound : (Fintype.card s).factorial *
      (Fintype.card κ * H ^ 2) ^ Fintype.card s ≤
      (Fintype.card ι).factorial * (Fintype.card κ * H ^ 2 + 1) ^ Fintype.card ι := by
    apply Nat.mul_le_mul (Nat.factorial_le hk)
    exact (Nat.pow_le_pow_left (Nat.le_add_right _ _) _).trans
      (Nat.pow_le_pow_right (by omega) hk)
  have hbpos : 0 < (Fintype.card ι).factorial *
      (Fintype.card κ * H ^ 2 + 1) ^ Fintype.card ι := by positivity
  refine ⟨z, hzpos, hzfull, ?_⟩
  intro j
  by_cases hj : j ∈ s
  · exact ⟨(hbnd ⟨j, hj⟩).1.trans hbound, (hbnd ⟨j, hj⟩).2.trans hbound⟩
  · have hzj : z j = 0 := by simpa [s, mem_support] using hj
    simp only [hzj, Rat.num_zero, Rat.den_zero, Int.natAbs_zero]
    omega

/-- Slack variables turn inequalities into the standard-form system above.
The resulting coordinate bound also covers lower-dimensional feasible sets. -/
theorem exists_bounded_integer_inequality_point (A : Matrix κ ι ℤ) (b : κ → ℤ)
    (H : ℕ) (hH : 1 ≤ H) (hA : ∀ i j, (A i j).natAbs ≤ H)
    (hb : ∀ i, (b i).natAbs ≤ H)
    (hf : ∃ x : ι → ℚ, (∀ j, 0 ≤ x j) ∧
      ∀ i, (∑ j, (A i j : ℚ) * x j) ≤ (b i : ℚ)) :
    ∃ x : ι → ℚ, (∀ j, 0 ≤ x j) ∧
      (∀ i, (∑ j, (A i j : ℚ) * x j) ≤ (b i : ℚ)) ∧
      ∀ j, (x j).num.natAbs ≤ (Fintype.card ι + Fintype.card κ).factorial *
          (Fintype.card κ * H ^ 2 + 1) ^ (Fintype.card ι + Fintype.card κ) ∧
        (x j).den ≤ (Fintype.card ι + Fintype.card κ).factorial *
          (Fintype.card κ * H ^ 2 + 1) ^ (Fintype.card ι + Fintype.card κ) := by
  classical
  let C : Matrix κ (ι ⊕ κ) ℤ := fun i =>
    Sum.elim (A i) (fun k => if i = k then 1 else 0)
  have hC : ∀ i j, (C i j).natAbs ≤ H := by
    intro i j
    cases j with
    | inl j => exact hA i j
    | inr k => simp only [C, Sum.elim_inr]; split_ifs <;> simp_all
  obtain ⟨x, hxpos, hxrows⟩ := hf
  let z : (ι ⊕ κ) → ℚ := Sum.elim x (fun i => (b i : ℚ) - ∑ j, (A i j : ℚ) * x j)
  have hzpos : ∀ j, 0 ≤ z j := by
    intro j
    cases j with
    | inl j => exact hxpos j
    | inr i => exact sub_nonneg.mpr (hxrows i)
  have hzeq : (C.map (fun z => (z : ℚ))) *ᵥ z = fun i => (b i : ℚ) := by
    ext i
    simp [Matrix.mulVec, Matrix.map, dotProduct, C, z, Fintype.sum_sum_type]
  obtain ⟨w, hwpos, hweq, hwbnd⟩ := exists_bounded_integer_point C b H hC hb
    ⟨z, hzpos, hzeq⟩
  refine ⟨fun j => w (.inl j), fun j => hwpos _, ?_, ?_⟩
  · intro i
    have h := congrFun hweq i
    have heq : (∑ j, (A i j : ℚ) * w (.inl j)) + w (.inr i) = (b i : ℚ) := by
      simpa [Matrix.mulVec, Matrix.map, dotProduct, C, Fintype.sum_sum_type] using h
    linarith [hwpos (.inr i)]
  · intro j
    simpa only [Fintype.card_sum] using hwbnd (.inl j)

/-- A single dimension cap bounds all coordinates of an inequality witness. -/
theorem exists_capped_integer_inequality_point (A : Matrix κ ι ℤ) (b : κ → ℤ)
    (H K : ℕ) (hH : 1 ≤ H) (hK : Fintype.card ι + Fintype.card κ ≤ K)
    (hA : ∀ i j, (A i j).natAbs ≤ H) (hb : ∀ i, (b i).natAbs ≤ H)
    (hf : ∃ x : ι → ℚ, (∀ j, 0 ≤ x j) ∧
      ∀ i, (∑ j, (A i j : ℚ) * x j) ≤ (b i : ℚ)) :
    ∃ x : ι → ℚ, (∀ j, 0 ≤ x j) ∧
      (∀ i, (∑ j, (A i j : ℚ) * x j) ≤ (b i : ℚ)) ∧
      ∀ j, (x j).num.natAbs ≤ K.factorial * (K * H ^ 2 + 1) ^ K ∧
        (x j).den ≤ K.factorial * (K * H ^ 2 + 1) ^ K := by
  obtain ⟨x, hxpos, hxrows, hxbnd⟩ := exists_bounded_integer_inequality_point A b H hH hA hb hf
  have hr : Fintype.card κ ≤ K := by omega
  have hbound : (Fintype.card ι + Fintype.card κ).factorial *
      (Fintype.card κ * H ^ 2 + 1) ^ (Fintype.card ι + Fintype.card κ) ≤
      K.factorial * (K * H ^ 2 + 1) ^ K := by
    apply Nat.mul_le_mul (Nat.factorial_le hK)
    have hbase : Fintype.card κ * H ^ 2 + 1 ≤ K * H ^ 2 + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right (H ^ 2) hr) 1
    exact (Nat.pow_le_pow_left hbase _).trans
      (Nat.pow_le_pow_right (by omega) hK)
  exact ⟨x, hxpos, hxrows, fun j =>
    ⟨(hxbnd j).1.trans hbound, (hxbnd j).2.trans hbound⟩⟩

end Lax109476Proofs.SmallFeasiblePoint

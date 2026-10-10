import Lax109476Proofs.IntegerEncoding

open scoped BigOperators Matrix

namespace Lax109476Proofs.IntegerCertificates

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.FarkasCertificate Lax109476.RecessionDirection
open IntegerEncoding SmallFeasiblePoint

def coordinateCap (m n H : ℕ) : ℕ :=
  (2 * (m + n) + 2).factorial *
    ((2 * (m + n) + 2) * H ^ 2 + 1) ^ (2 * (m + n) + 2)

def BoundedVector {ι : Type*} (B : ℕ) (x : ι → ℚ) : Prop :=
  ∀ i, (x i).num.natAbs ≤ B ∧ (x i).den ≤ B

def BoundedCertificate {m n : ℕ} (B : ℕ) : Certificate m n → Prop
  | .optimal x y => BoundedVector B x ∧ BoundedVector B y
  | .infeasible y => BoundedVector B y
  | .unbounded x d => BoundedVector B x ∧ BoundedVector B d

def pairMatrix {m n : ℕ} (P : Program ℤ m n) :
    Matrix (Fin m ⊕ (Fin n ⊕ Bool)) (Fin n ⊕ Fin m) ℤ
  | .inl i => Sum.elim (P.A i) (fun _ => 0)
  | .inr (.inl j) => Sum.elim (fun _ => 0) (fun i => -P.A i j)
  | .inr (.inr false) => Sum.elim P.c (fun i => -P.b i)
  | .inr (.inr true) => Sum.elim (fun j => -P.c j) P.b

def pairBound {m n : ℕ} (P : Program ℤ m n) :
    (Fin m ⊕ (Fin n ⊕ Bool)) → ℤ
  | .inl i => P.b i
  | .inr (.inl j) => -P.c j
  | .inr (.inr _) => 0

/-- Compress both optimizers together so equality of objectives is preserved. -/
theorem small_matching_pair {m n : ℕ} (P : Program ℤ m n) (H : ℕ) (hH : 1 ≤ H)
    (hA : ∀ i j, (P.A i j).natAbs ≤ H) (hb : ∀ i, (P.b i).natAbs ≤ H)
    (hc : ∀ j, (P.c j).natAbs ≤ H) (x : Fin n → ℚ) (y : Fin m → ℚ)
    (hx : PrimalFeasible (rationalProgram P) x)
    (hy : DualFeasible (rationalProgram P) y)
    (heq : primalValue (rationalProgram P) x = dualValue (rationalProgram P) y) :
    ∃ xr : Fin n → ℚ, ∃ yr : Fin m → ℚ,
      IsValidCertificate (rationalProgram P) (.optimal xr yr) ∧
        BoundedCertificate (coordinateCap m n H) (.optimal xr yr) := by
  let z : (Fin n ⊕ Fin m) → ℚ := Sum.elim x y
  have hz : ∀ j, 0 ≤ z j := by
    intro j
    cases j with
    | inl j => exact hx.1 j
    | inr i => exact hy.1 i
  have hrows : ∀ i, (∑ j, (pairMatrix P i j : ℚ) * z j) ≤ (pairBound P i : ℚ) := by
    intro i
    cases i with
    | inl i => simpa [pairMatrix, pairBound, z, Fintype.sum_sum_type,
        rowValue, rationalProgram] using hx.2 i
    | inr i =>
      cases i with
      | inl j =>
        simpa [pairMatrix, pairBound, z, Fintype.sum_sum_type, columnValue,
          rationalProgram, Finset.sum_neg_distrib] using neg_le_neg (hy.2 j)
      | inr b =>
        cases b
        · have h : primalValue (rationalProgram P) x - dualValue (rationalProgram P) y ≤ 0 :=
            by rw [heq]; simp
          simpa [pairMatrix, pairBound, z, Fintype.sum_sum_type, primalValue,
            dualValue, rationalProgram, Finset.sum_neg_distrib, sub_eq_add_neg] using h
        · have h : -primalValue (rationalProgram P) x + dualValue (rationalProgram P) y ≤ 0 :=
            by rw [heq]; simp
          simpa [pairMatrix, pairBound, z, Fintype.sum_sum_type, primalValue,
            dualValue, rationalProgram, Finset.sum_neg_distrib] using h
  have hmat : ∀ i j, (pairMatrix P i j).natAbs ≤ H := by
    intro i j
    cases i with
    | inl i => cases j <;> simp [pairMatrix, hA]
    | inr i =>
      cases i with
      | inl k => cases j <;> simp [pairMatrix, hA]
      | inr b => cases b <;> cases j <;> simp [pairMatrix, hb, hc]
  have hbound : ∀ i, (pairBound P i).natAbs ≤ H := by
    intro i
    cases i with
    | inl i => exact hb i
    | inr i => cases i <;> simp [pairBound, hc]
  obtain ⟨w, hwpos, hwrows, hwsize⟩ := exists_capped_integer_inequality_point
    (pairMatrix P) (pairBound P) H (2 * (m + n) + 2) hH
    (by simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool]; omega)
    hmat hbound ⟨z, hz, hrows⟩
  let xr : Fin n → ℚ := fun j => w (.inl j)
  let yr : Fin m → ℚ := fun i => w (.inr i)
  refine ⟨xr, yr, ⟨⟨fun j => hwpos _, ?_⟩, ⟨fun i => hwpos _, ?_⟩, ?_⟩,
    (fun j => hwsize (.inl j)), (fun i => hwsize (.inr i))⟩
  · intro i
    simpa [pairMatrix, pairBound, Fintype.sum_sum_type, xr, rowValue,
      rationalProgram] using hwrows (.inl i)
  · intro j
    have h : -columnValue (rationalProgram P) yr j ≤ -(P.c j : ℚ) := by
      simpa [pairMatrix, pairBound, Fintype.sum_sum_type, yr, columnValue,
        rationalProgram, Finset.sum_neg_distrib] using hwrows (.inr (.inl j))
    exact neg_le_neg_iff.mp h
  · have h₁ : primalValue (rationalProgram P) xr - dualValue (rationalProgram P) yr ≤ 0 := by
      simpa [pairMatrix, pairBound, Fintype.sum_sum_type, xr, yr, primalValue,
        dualValue, rationalProgram, Finset.sum_neg_distrib, sub_eq_add_neg]
        using hwrows (.inr (.inr false))
    have h₂ : -primalValue (rationalProgram P) xr + dualValue (rationalProgram P) yr ≤ 0 := by
      simpa [pairMatrix, pairBound, Fintype.sum_sum_type, xr, yr, primalValue,
        dualValue, rationalProgram, Finset.sum_neg_distrib]
        using hwrows (.inr (.inr true))
    linarith

private theorem sum_scale {ι : Type*} [Fintype ι] (a x : ι → ℚ) (t : ℚ) :
    (∑ i, a i * (t * x i)) = t * ∑ i, a i * x i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Normalize the strict Farkas inequality before compressing its multipliers. -/
theorem normalized_small_infeasibility_certificate {m n : ℕ} (P : Program ℤ m n)
    (H : ℕ) (hH : 1 ≤ H) (hA : ∀ i j, (P.A i j).natAbs ≤ H)
    (hb : ∀ i, (P.b i).natAbs ≤ H) (y : Fin m → ℚ)
    (hy : IsInfeasibilityCertificate (rationalProgram P) y) :
    ∃ yr : Fin m → ℚ, IsValidCertificate (rationalProgram P) (.infeasible yr) ∧
      BoundedCertificate (n := n) (coordinateCap m n H) (.infeasible yr) ∧
        dualValue (rationalProgram P) yr ≤ -1 := by
  let A : Matrix (Fin n ⊕ Unit) (Fin m) ℤ :=
    Sum.elim (fun j i => -P.A i j) (fun _ => P.b)
  let b : (Fin n ⊕ Unit) → ℤ := Sum.elim (fun _ => 0) (fun _ => -1)
  let t := (-dualValue (rationalProgram P) y)⁻¹
  let z := fun i => t * y i
  have ht : 0 < t := inv_pos.mpr (neg_pos.mpr hy.2.2)
  have hzpos : ∀ i, 0 ≤ z i := fun i => mul_nonneg ht.le (hy.1 i)
  have hzrows : ∀ j, (∑ i, (A j i : ℚ) * z i) ≤ (b j : ℚ) := by
    intro j
    cases j with
    | inl j =>
      simp only [A, b, z, Sum.elim_inl, Int.cast_neg, Int.cast_zero]
      rw [sum_scale]
      simp only [neg_mul, Finset.sum_neg_distrib]
      exact mul_nonpos_of_nonneg_of_nonpos ht.le (neg_nonpos.mpr (hy.2.1 j))
    | inr _ =>
      simp only [A, b, z, Sum.elim_inr, Int.cast_neg, Int.cast_one]
      rw [sum_scale]
      change t * dualValue (rationalProgram P) y ≤ -1
      dsimp [t]
      rw [inv_neg, neg_mul, inv_mul_cancel₀ (ne_of_lt hy.2.2)]
  have hmat : ∀ j i, (A j i).natAbs ≤ H := by
    intro j i
    cases j with
    | inl j => simpa [A] using hA i j
    | inr _ => exact hb i
  have hbound : ∀ j, (b j).natAbs ≤ H := by
    intro j
    cases j <;> simp [b, hH]
  obtain ⟨w, hwpos, hwrows, hwsize⟩ := exists_capped_integer_inequality_point A b H
    (2 * (m + n) + 2) hH
    (by simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]; omega)
    hmat hbound ⟨z, hzpos, hzrows⟩
  refine ⟨w, ⟨hwpos, ?_, ?_⟩, hwsize, ?_⟩
  · intro j
    have h : -columnValue (rationalProgram P) w j ≤ 0 := by
      simpa [A, b, columnValue, rationalProgram, Finset.sum_neg_distrib] using hwrows (.inl j)
    linarith
  · have h : dualValue (rationalProgram P) w ≤ -1 := by
      simpa [A, b, dualValue, rationalProgram] using hwrows (.inr ())
    linarith
  · simpa [A, b, dualValue, rationalProgram] using hwrows (.inr ())

theorem small_infeasibility_certificate {m n : ℕ} (P : Program ℤ m n)
    (H : ℕ) (hH : 1 ≤ H) (hA : ∀ i j, (P.A i j).natAbs ≤ H)
    (hb : ∀ i, (P.b i).natAbs ≤ H) (y : Fin m → ℚ)
    (hy : IsInfeasibilityCertificate (rationalProgram P) y) :
    ∃ yr : Fin m → ℚ, IsValidCertificate (rationalProgram P) (.infeasible yr) ∧
      BoundedCertificate (n := n) (coordinateCap m n H) (.infeasible yr) := by
  obtain ⟨yr, hv, hs, _⟩ := normalized_small_infeasibility_certificate P H hH hA hb y hy
  exact ⟨yr, hv, hs⟩

def rayMatrix {m n : ℕ} (P : Program ℤ m n) :
    Matrix (Fin m ⊕ (Fin m ⊕ Unit)) (Fin n ⊕ Fin n) ℤ
  | .inl i => Sum.elim (P.A i) (fun _ => 0)
  | .inr (.inl i) => Sum.elim (fun _ => 0) (P.A i)
  | .inr (.inr _) => Sum.elim (fun _ => 0) (fun j => -P.c j)

def rayBound {m n : ℕ} (P : Program ℤ m n) :
    (Fin m ⊕ (Fin m ⊕ Unit)) → ℤ
  | .inl i => P.b i
  | .inr (.inl _) => 0
  | .inr (.inr _) => -1

/-- A base point and a normalized improving direction are compressed together. -/
theorem small_unbounded_certificate {m n : ℕ} (P : Program ℤ m n)
    (H : ℕ) (hH : 1 ≤ H) (hA : ∀ i j, (P.A i j).natAbs ≤ H)
    (hb : ∀ i, (P.b i).natAbs ≤ H) (hc : ∀ j, (P.c j).natAbs ≤ H)
    (x d : Fin n → ℚ) (hx : PrimalFeasible (rationalProgram P) x)
    (hd : IsImprovingDirection (rationalProgram P) d) :
    ∃ xr dr : Fin n → ℚ, IsValidCertificate (rationalProgram P) (.unbounded xr dr) ∧
      BoundedCertificate (m := m) (coordinateCap m n H) (.unbounded xr dr) := by
  let t := (primalValue (rationalProgram P) d)⁻¹
  let z : (Fin n ⊕ Fin n) → ℚ := Sum.elim x (fun j => t * d j)
  have ht : 0 < t := inv_pos.mpr hd.2.2
  have hzpos : ∀ j, 0 ≤ z j := by
    intro j
    cases j with
    | inl j => exact hx.1 j
    | inr j => exact mul_nonneg ht.le (hd.1 j)
  have hzrows : ∀ i, (∑ j, (rayMatrix P i j : ℚ) * z j) ≤ (rayBound P i : ℚ) := by
    intro i
    cases i with
    | inl i => simpa [rayMatrix, rayBound, z, Fintype.sum_sum_type, rowValue,
        rationalProgram] using hx.2 i
    | inr i =>
      cases i with
      | inl i =>
        simp only [rayMatrix, rayBound, z, Fintype.sum_sum_type, Sum.elim_inl,
          Sum.elim_inr, Int.cast_zero, zero_mul, Finset.sum_const_zero, zero_add]
        rw [sum_scale]
        exact mul_nonpos_of_nonneg_of_nonpos ht.le (hd.2.1 i)
      | inr _ =>
        simp only [rayMatrix, rayBound, z, Fintype.sum_sum_type, Sum.elim_inl,
          Sum.elim_inr, Int.cast_zero, Int.cast_neg, Int.cast_one, zero_mul,
          Finset.sum_const_zero, zero_add]
        rw [sum_scale]
        simp only [neg_mul, Finset.sum_neg_distrib]
        change t * -primalValue (rationalProgram P) d ≤ -1
        dsimp [t]
        rw [mul_neg, inv_mul_cancel₀ (ne_of_gt hd.2.2)]
  have hmat : ∀ i j, (rayMatrix P i j).natAbs ≤ H := by
    intro i j
    cases i with
    | inl i => cases j <;> simp [rayMatrix, hA]
    | inr i =>
      cases i with
      | inl i => cases j <;> simp [rayMatrix, hA]
      | inr _ => cases j <;> simp [rayMatrix, hc]
  have hbound : ∀ i, (rayBound P i).natAbs ≤ H := by
    intro i
    cases i with
    | inl i => exact hb i
    | inr i => cases i <;> simp [rayBound, hH]
  obtain ⟨w, hwpos, hwrows, hwsize⟩ := exists_capped_integer_inequality_point
    (rayMatrix P) (rayBound P) H (2 * (m + n) + 2) hH
    (by simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]; omega)
    hmat hbound ⟨z, hzpos, hzrows⟩
  let xr : Fin n → ℚ := fun j => w (.inl j)
  let dr : Fin n → ℚ := fun j => w (.inr j)
  refine ⟨xr, dr, ⟨⟨fun j => hwpos _, ?_⟩, fun j => hwpos _, ?_, ?_⟩,
    (fun j => hwsize (.inl j)), (fun j => hwsize (.inr j))⟩
  · intro i
    simpa [rayMatrix, rayBound, Fintype.sum_sum_type, xr, rowValue,
      rationalProgram] using hwrows (.inl i)
  · intro i
    simpa [rayMatrix, rayBound, Fintype.sum_sum_type, dr, rowValue,
      rationalProgram] using hwrows (.inr (.inl i))
  · have h : -primalValue (rationalProgram P) dr ≤ -1 := by
      simpa [rayMatrix, rayBound, Fintype.sum_sum_type, dr, primalValue,
        rationalProgram, Finset.sum_neg_distrib] using hwrows (.inr (.inr ()))
    linarith

/-- Every existing certificate can be replaced by one obeying a common bound. -/
theorem compress_integer_certificate {m n : ℕ} (P : Program ℤ m n)
    (H : ℕ) (hH : 1 ≤ H) (hA : ∀ i j, (P.A i j).natAbs ≤ H)
    (hb : ∀ i, (P.b i).natAbs ≤ H) (hc : ∀ j, (P.c j).natAbs ≤ H)
    (certificate : Certificate m n) (hv : IsValidCertificate (rationalProgram P) certificate) :
    ∃ certificate : Certificate m n, IsValidCertificate (rationalProgram P) certificate ∧
      BoundedCertificate (coordinateCap m n H) certificate := by
  cases certificate with
  | optimal x y =>
    obtain ⟨xr, yr, hv, hs⟩ := small_matching_pair P H hH hA hb hc x y hv.1 hv.2.1 hv.2.2
    exact ⟨.optimal xr yr, hv, hs⟩
  | infeasible y =>
    obtain ⟨yr, hv, hs⟩ := small_infeasibility_certificate P H hH hA hb y hv
    exact ⟨.infeasible yr, hv, hs⟩
  | unbounded x d =>
    obtain ⟨xr, dr, hv, hs⟩ := small_unbounded_certificate P H hH hA hb hc x d hv.1 hv.2
    exact ⟨.unbounded xr dr, hv, hs⟩

theorem bounded_certificate_encoding {m n : ℕ} (B : ℕ) (certificate : Certificate m n)
    (h : BoundedCertificate B certificate) :
    Lax759944.BinaryWordEncoding.bitSize
      (Lax109476.RationalEncoding.encodeCertificate certificate) ≤
        3 + (2 * n + m) * (4 + 2 * Nat.size B) := by
  open Lax759944.BinaryWordEncoding Lax109476.RationalEncoding EncodingSize in
    cases certificate with
    | optimal x y =>
      have hx := bounded_vector_size x B h.1
      have hy := bounded_vector_size y B h.2
      simp only [encodeCertificate, bitSize_append, bitSize_cons, bitSize_nil]
      change 1 + bitSize (encodeVector x) + bitSize (encodeVector y) ≤ _
      nlinarith
    | infeasible y =>
      have hy := bounded_vector_size y B h
      simp only [encodeCertificate, bitSize_append, bitSize_cons, bitSize_nil]
      change 2 + bitSize (encodeVector y) ≤ _
      nlinarith
    | unbounded x d =>
      have hx := bounded_vector_size x B h.1
      have hd := bounded_vector_size d B h.2
      simp only [encodeCertificate, bitSize_append, bitSize_cons, bitSize_nil]
      change 3 + bitSize (encodeVector x) + bitSize (encodeVector d) ≤ _
      nlinarith

end Lax109476Proofs.IntegerCertificates

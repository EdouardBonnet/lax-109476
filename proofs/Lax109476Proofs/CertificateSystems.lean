import Lax109476Proofs.IndexedPointRecovery
import Lax109476Proofs.IntegerCertificates

open scoped BigOperators

namespace Lax109476Proofs.CertificateSystems

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.FarkasCertificate Lax109476.RecessionDirection
open IntegerEncoding IntegerCertificates

def NonnegativeFeasible {κ ι : Type*} [Fintype ι]
    (A : κ → ι → ℤ) (b : κ → ℤ) (z : ι → ℚ) : Prop :=
  (∀ j, 0 ≤ z j) ∧ ∀ i, (∑ j, (A i j : ℚ) * z j) ≤ (b i : ℚ)

theorem pair_valid {m n : ℕ} (P : Program ℤ m n) (z : (Fin n ⊕ Fin m) → ℚ)
    (hz : NonnegativeFeasible (pairMatrix P) (pairBound P) z) :
    IsValidCertificate (rationalProgram P) (.optimal (fun j => z (.inl j)) (fun i => z (.inr i))) := by
  refine ⟨⟨fun j => hz.1 _, fun i => ?_⟩, ⟨fun i => hz.1 _, fun j => ?_⟩, ?_⟩
  · simpa [pairMatrix, pairBound, Fintype.sum_sum_type, rowValue, rationalProgram]
      using hz.2 (.inl i)
  · have h : -columnValue (rationalProgram P) (fun i => z (.inr i)) j ≤ -(P.c j : ℚ) := by
      simpa [pairMatrix, pairBound, Fintype.sum_sum_type, columnValue,
        rationalProgram, Finset.sum_neg_distrib] using hz.2 (.inr (.inl j))
    exact neg_le_neg_iff.mp h
  · have h₁ : primalValue (rationalProgram P) (fun j => z (.inl j)) -
        dualValue (rationalProgram P) (fun i => z (.inr i)) ≤ 0 := by
      simpa [pairMatrix, pairBound, Fintype.sum_sum_type, primalValue,
        dualValue, rationalProgram, Finset.sum_neg_distrib, sub_eq_add_neg]
        using hz.2 (.inr (.inr false))
    have h₂ : -primalValue (rationalProgram P) (fun j => z (.inl j)) +
        dualValue (rationalProgram P) (fun i => z (.inr i)) ≤ 0 := by
      simpa [pairMatrix, pairBound, Fintype.sum_sum_type, primalValue,
        dualValue, rationalProgram, Finset.sum_neg_distrib]
        using hz.2 (.inr (.inr true))
    linarith

theorem pair_feasible {m n : ℕ} (P : Program ℤ m n) (x : Fin n → ℚ) (y : Fin m → ℚ)
    (hv : IsValidCertificate (rationalProgram P) (.optimal x y)) :
    ∃ z, NonnegativeFeasible (pairMatrix P) (pairBound P) z := by
  refine ⟨Sum.elim x y, ?_, ?_⟩
  · intro j
    cases j with
    | inl j => exact hv.1.1 j
    | inr i => exact hv.2.1.1 i
  · intro i
    cases i with
    | inl i => simpa [pairMatrix, pairBound, Fintype.sum_sum_type,
        rowValue, rationalProgram] using hv.1.2 i
    | inr i =>
      cases i with
      | inl j =>
        simpa [pairMatrix, pairBound, Fintype.sum_sum_type, columnValue,
          rationalProgram, Finset.sum_neg_distrib] using neg_le_neg (hv.2.1.2 j)
      | inr v =>
        cases v
        · have h : primalValue (rationalProgram P) x - dualValue (rationalProgram P) y ≤ 0 :=
            by rw [hv.2.2]; simp
          simpa [pairMatrix, pairBound, Fintype.sum_sum_type, primalValue,
            dualValue, rationalProgram, Finset.sum_neg_distrib, sub_eq_add_neg] using h
        · have h : -primalValue (rationalProgram P) x + dualValue (rationalProgram P) y ≤ 0 :=
            by rw [hv.2.2]; simp
          simpa [pairMatrix, pairBound, Fintype.sum_sum_type, primalValue,
            dualValue, rationalProgram, Finset.sum_neg_distrib] using h

def farkasMatrix {m n : ℕ} (P : Program ℤ m n) : (Fin n ⊕ Unit) → Fin m → ℤ :=
  Sum.elim (fun j i => -P.A i j) (fun _ => P.b)

def farkasBound {n : ℕ} : (Fin n ⊕ Unit) → ℤ :=
  Sum.elim (fun _ => 0) (fun _ => -1)

theorem farkas_valid {m n : ℕ} (P : Program ℤ m n) (y : Fin m → ℚ)
    (hy : NonnegativeFeasible (farkasMatrix P) farkasBound y) :
    IsValidCertificate (rationalProgram P) (.infeasible y) := by
  refine ⟨hy.1, fun j => ?_, ?_⟩
  · have h : -columnValue (rationalProgram P) y j ≤ 0 := by
      simpa [farkasMatrix, farkasBound, columnValue, rationalProgram,
        Finset.sum_neg_distrib] using hy.2 (.inl j)
    linarith
  · have h : dualValue (rationalProgram P) y ≤ -1 := by
      simpa [farkasMatrix, farkasBound, dualValue, rationalProgram] using hy.2 (.inr ())
    linarith

theorem farkas_feasible {m n : ℕ} (P : Program ℤ m n) (H : ℕ) (hH : 1 ≤ H)
    (hA : ∀ i j, (P.A i j).natAbs ≤ H) (hb : ∀ i, (P.b i).natAbs ≤ H)
    (y : Fin m → ℚ) (hy : IsValidCertificate (rationalProgram P) (.infeasible y)) :
    ∃ z, NonnegativeFeasible (farkasMatrix P) farkasBound z := by
  obtain ⟨z, hz, _, hn⟩ := normalized_small_infeasibility_certificate P H hH hA hb y hy
  refine ⟨z, hz.1, fun i => ?_⟩
  cases i with
  | inl j =>
    simpa [farkasMatrix, farkasBound, columnValue, rationalProgram, Finset.sum_neg_distrib]
      using neg_nonpos.mpr (hz.2.1 j)
  | inr _ => simpa [farkasMatrix, farkasBound, dualValue, rationalProgram] using hn

theorem ray_valid {m n : ℕ} (P : Program ℤ m n) (z : (Fin n ⊕ Fin n) → ℚ)
    (hz : NonnegativeFeasible (rayMatrix P) (rayBound P) z) :
    IsValidCertificate (rationalProgram P) (.unbounded (fun j => z (.inl j)) (fun j => z (.inr j))) := by
  refine ⟨⟨fun j => hz.1 _, fun i => ?_⟩, fun j => hz.1 _, fun i => ?_, ?_⟩
  · simpa [rayMatrix, rayBound, Fintype.sum_sum_type, rowValue, rationalProgram]
      using hz.2 (.inl i)
  · simpa [rayMatrix, rayBound, Fintype.sum_sum_type, rowValue, rationalProgram]
      using hz.2 (.inr (.inl i))
  · have h : -primalValue (rationalProgram P) (fun j => z (.inr j)) ≤ -1 := by
      simpa [rayMatrix, rayBound, Fintype.sum_sum_type, primalValue,
        rationalProgram, Finset.sum_neg_distrib] using hz.2 (.inr (.inr ()))
    linarith

theorem ray_feasible {m n : ℕ} (P : Program ℤ m n) (x d : Fin n → ℚ)
    (hv : IsValidCertificate (rationalProgram P) (.unbounded x d)) :
    ∃ z, NonnegativeFeasible (rayMatrix P) (rayBound P) z := by
  let t := (primalValue (rationalProgram P) d)⁻¹
  have ht : 0 < t := inv_pos.mpr hv.2.2.2
  refine ⟨Sum.elim x (fun j => t * d j), ?_, ?_⟩
  · intro j
    cases j with
    | inl j => exact hv.1.1 j
    | inr j => exact mul_nonneg ht.le (hv.2.1 j)
  · intro i
    cases i with
    | inl i => simpa [rayMatrix, rayBound, Fintype.sum_sum_type, rowValue,
        rationalProgram] using hv.1.2 i
    | inr i =>
      cases i with
      | inl i =>
        have hscale : (∑ j, (P.A i j : ℚ) * (t * d j)) =
            t * rowValue (rationalProgram P) d i := by
          simp only [rowValue, rationalProgram, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        simp only [rayMatrix, rayBound, Fintype.sum_sum_type, Sum.elim_inl,
          Sum.elim_inr, Int.cast_zero, zero_mul, Finset.sum_const_zero, zero_add]
        rw [hscale]
        exact mul_nonpos_of_nonneg_of_nonpos ht.le (hv.2.2.1 i)
      | inr _ =>
        have hscale : (∑ j, -(P.c j : ℚ) * (t * d j)) =
            -(t * primalValue (rationalProgram P) d) := by
          simp only [primalValue, rationalProgram, Finset.mul_sum, neg_mul, Finset.sum_neg_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          ring
        simp only [rayMatrix, rayBound, Fintype.sum_sum_type, Sum.elim_inl,
          Sum.elim_inr, Int.cast_zero, Int.cast_neg, Int.cast_one, zero_mul,
          Finset.sum_const_zero, zero_add]
        rw [hscale]
        dsimp [t]
        rw [inv_mul_cancel₀ (ne_of_gt hv.2.2.2)]

end Lax109476Proofs.CertificateSystems

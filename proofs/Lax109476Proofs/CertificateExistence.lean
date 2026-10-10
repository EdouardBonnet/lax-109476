import Lax109476Proofs.RationalFeasibility
import Lax109476.CertificateExistence
import Mathlib.Tactic

open scoped BigOperators

namespace Lax109476Proofs.CertificateExistence

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.RecessionDirection
open Lax109476Proofs.RationalFeasibility

private def pairMatrix {m n : ℕ} (P : Program ℚ m n) :
    Matrix (Fin m ⊕ (Fin n ⊕ Bool)) (Fin n ⊕ Fin m) ℚ
  | .inl i => Sum.elim (P.A i) (fun _ => 0)
  | .inr (.inl j) => Sum.elim (fun _ => 0) (fun i => -P.A i j)
  | .inr (.inr false) => Sum.elim P.c (fun i => -P.b i)
  | .inr (.inr true) => Sum.elim (fun j => -P.c j) P.b

private def pairBound {m n : ℕ} (P : Program ℚ m n) :
    (Fin m ⊕ (Fin n ⊕ Bool)) → ℚ
  | .inl i => P.b i
  | .inr (.inl j) => -P.c j
  | .inr (.inr _) => 0

private theorem rational_matching_pair {m n : ℕ} (P : Program ℚ m n)
    (x : Fin n → ℝ) (y : Fin m → ℝ)
    (hx : PrimalFeasible (toReal P) x) (hy : DualFeasible (toReal P) y)
    (heq : primalValue (toReal P) x = dualValue (toReal P) y) :
    ∃ xr : Fin n → ℚ, ∃ yr : Fin m → ℚ,
      PrimalFeasible P xr ∧ DualFeasible P yr ∧ primalValue P xr = dualValue P yr := by
  let z : (Fin n ⊕ Fin m) → ℝ := Sum.elim x y
  have hz : ∀ j, 0 ≤ z j := by
    intro j
    cases j with
    | inl j => exact hx.1 j
    | inr i => exact hy.1 i
  have hrows : ∀ i, (∑ j, (pairMatrix P i j : ℝ) * z j) ≤ (pairBound P i : ℝ) := by
    intro i
    cases i with
    | inl i => simpa [pairMatrix, pairBound, z, Fintype.sum_sum_type, rowValue, toReal] using hx.2 i
    | inr i =>
      cases i with
      | inl j =>
        simpa [pairMatrix, pairBound, z, Fintype.sum_sum_type, columnValue, toReal,
          Finset.sum_neg_distrib] using neg_le_neg (hy.2 j)
      | inr b =>
        cases b
        · have h : primalValue (toReal P) x - dualValue (toReal P) y ≤ 0 := by rw [heq]; simp
          simpa [pairMatrix, pairBound, z, Fintype.sum_sum_type, primalValue, dualValue,
            toReal, Finset.sum_neg_distrib, sub_eq_add_neg] using h
        · have h : -primalValue (toReal P) x + dualValue (toReal P) y ≤ 0 := by rw [heq]; simp
          simpa [pairMatrix, pairBound, z, Fintype.sum_sum_type, primalValue, dualValue,
            toReal, Finset.sum_neg_distrib] using h
  obtain ⟨zr, hzr, hr⟩ := finite_rational_feasibility (pairMatrix P) (pairBound P) z hz hrows
  let xr : Fin n → ℚ := fun j => zr (.inl j)
  let yr : Fin m → ℚ := fun i => zr (.inr i)
  refine ⟨xr, yr, ⟨fun j => hzr _, ?_⟩, ⟨fun i => hzr _, ?_⟩, ?_⟩
  · intro i
    simpa [pairMatrix, pairBound, Fintype.sum_sum_type, xr, rowValue] using hr (.inl i)
  · intro j
    have h := hr (.inr (.inl j))
    have h' : -columnValue P yr j ≤ -P.c j := by
      simpa [pairMatrix, pairBound, Fintype.sum_sum_type, yr, columnValue,
        Finset.sum_neg_distrib] using h
    exact neg_le_neg_iff.mp h'
  · have h₁ := hr (.inr (.inr false))
    have h₂ := hr (.inr (.inr true))
    have hg₁ : primalValue P xr - dualValue P yr ≤ 0 := by
      simpa [pairMatrix, pairBound, Fintype.sum_sum_type, xr, yr, primalValue,
        dualValue, Finset.sum_neg_distrib, sub_eq_add_neg] using h₁
    have hg₂ : -primalValue P xr + dualValue P yr ≤ 0 := by
      simpa [pairMatrix, pairBound, Fintype.sum_sum_type, xr, yr, primalValue,
        dualValue, Finset.sum_neg_distrib] using h₂
    linarith

private theorem sum_scale {ι : Type} [Fintype ι] (a d : ι → ℝ) (t : ℝ) :
    (∑ j, a j * (t * d j)) = t * ∑ j, a j * d j := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem rational_improving_direction {m n : ℕ} (P : Program ℚ m n)
    (d : Fin n → ℝ) (hd : IsImprovingDirection (toReal P) d) :
    ∃ dr : Fin n → ℚ, IsImprovingDirection P dr := by
  let A : Matrix (Fin m ⊕ Unit) (Fin n) ℚ := Sum.elim P.A (fun _ j => -P.c j)
  let b : (Fin m ⊕ Unit) → ℚ := Sum.elim (fun _ => 0) (fun _ => -1)
  let t := (primalValue (toReal P) d)⁻¹
  let z := fun j => t * d j
  have ht : 0 < t := inv_pos.mpr hd.2.2
  have hz : ∀ j, 0 ≤ z j := fun j => mul_nonneg ht.le (hd.1 j)
  have hrows : ∀ i, (∑ j, (A i j : ℝ) * z j) ≤ (b i : ℝ) := by
    intro i
    cases i with
    | inl i =>
      simp only [A, b, z, Sum.elim_inl, Rat.cast_zero]
      rw [sum_scale]
      exact mul_nonpos_of_nonneg_of_nonpos ht.le (hd.2.1 i)
    | inr _ =>
      simp only [A, b, z, Sum.elim_inr, Rat.cast_neg, Rat.cast_one, neg_mul,
        Finset.sum_neg_distrib]
      rw [sum_scale]
      change -(t * primalValue (toReal P) d) ≤ -1
      dsimp [t]
      rw [inv_mul_cancel₀ (ne_of_gt hd.2.2)]
  obtain ⟨dr, hdr, hr⟩ := finite_rational_feasibility A b z hz hrows
  refine ⟨dr, hdr, ?_, ?_⟩
  · intro i
    exact hr (.inl i)
  · have h : -primalValue P dr ≤ -1 := by
      simpa [A, b, primalValue, Finset.sum_neg_distrib] using hr (.inr ())
    linarith

/--
---
conclusion: Lax109476.CertificateExistence.exists_valid_certificate
---
Split on real feasibility and boundedness. An infeasible rational system has
rational Farkas multipliers by rational elimination. In the bounded feasible
case, strong duality makes the combined primal–dual system with equal
objectives real feasible; rational feasibility gives a rational matching pair.
In the unbounded case, rationalize both a feasible base point and a recession
direction normalized to objective increase at least one. No solver theorem
or complexity assumption is used.
-/
theorem certificate_existence :
    ∀ (m n : ℕ) (P : Program ℚ m n), ∃ certificate : Certificate m n,
      IsValidCertificate P certificate := by
  intro m n P
  classical
  by_cases hf : IsFeasible (toReal P)
  · by_cases hb : IsBoundedAbove (toReal P)
    · obtain ⟨x, y, hx, hy, heq⟩ :=
        Lax109476.StrongDuality.exists_matching_optimizers m n (toReal P) hf hb
      obtain ⟨xr, yr, hxr, hyr, heqr⟩ := rational_matching_pair P x y hx hy heq
      exact ⟨.optimal xr yr, hxr, hyr, heqr⟩
    · obtain ⟨xr, hxr⟩ := Lax109476.RationalFeasibility.exists_rational_feasible_point m n P hf
      obtain ⟨d, hd⟩ := Lax109476.RecessionExistence.exists_improving_direction m n (toReal P) hb
      obtain ⟨dr, hdr⟩ := rational_improving_direction P d hd
      exact ⟨.unbounded xr dr, hxr, hdr⟩
  · have hq : ¬ ∃ x : Fin n → ℚ, PrimalFeasible P x := by
      rintro ⟨x, hx⟩
      exact hf ⟨realVector x, cast_feasible P x hx⟩
    obtain ⟨y, hy⟩ := rational_farkas_exists P hq
    exact ⟨.infeasible y, hy⟩

end Lax109476Proofs.CertificateExistence

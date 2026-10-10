import Lax109476Proofs.Basic
import Lax109476.PrimalAttainment
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

namespace Lax109476Proofs.Attainment

open Lax109476.LinearProgram Lax109476.FarkasCertificate

private def thresholdProgram {m n : ℕ} (P : Program ℝ m n) (α : ℝ) :
    Program ℝ (m + 1) n where
  A r j := Fin.lastCases (-P.c j) (fun i => P.A i j) r
  b r := Fin.lastCases (-α) P.b r
  c _ := 0

private theorem threshold_column {m n : ℕ} (P : Program ℝ m n)
    (α : ℝ) (z : Fin (m + 1) → ℝ) (j : Fin n) :
    columnValue (thresholdProgram P α) z j =
      columnValue P (fun i => z i.castSucc) j - P.c j * z (Fin.last m) := by
  simp [columnValue, thresholdProgram, Fin.sum_univ_castSucc, sub_eq_add_neg]

private theorem threshold_objective {m n : ℕ} (P : Program ℝ m n)
    (α : ℝ) (z : Fin (m + 1) → ℝ) :
    dualValue (thresholdProgram P α) z =
      dualValue P (fun i => z i.castSucc) - α * z (Fin.last m) := by
  simp [dualValue, thresholdProgram, Fin.sum_univ_castSucc, sub_eq_add_neg]

private theorem column_scale {m n : ℕ} (P : Program ℝ m n)
    (y : Fin m → ℝ) (t : ℝ) (j : Fin n) :
    columnValue P (fun i => t * y i) j = t * columnValue P y j := by
  simp only [columnValue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem dual_scale {m n : ℕ} (P : Program ℝ m n)
    (y : Fin m → ℝ) (t : ℝ) :
    dualValue P (fun i => t * y i) = t * dualValue P y := by
  simp only [dualValue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/--
---
conclusion: Lax109476.PrimalAttainment.exists_primal_optimizer
---
Let $\alpha$ be the finite supremum of the feasible objectives. Apply
Farkas' lemma to the original system with the extra constraint
$c^T x\ge\alpha$. An infeasibility certificate has a nonnegative multiplier
$t$ for this extra row. If $t=0$, it contradicts original feasibility.
If $t>0$, divide the remaining multipliers by $t$ to obtain a dual feasible
point with objective strictly below $\alpha$. Weak duality then contradicts
the supremum property. Thus the threshold system is feasible and attains
$\alpha$.
-/
theorem primal_attainment :
    ∀ (m n : ℕ) (P : Program ℝ m n), IsFeasible P → IsBoundedAbove P →
      ∃ x : Fin n → ℝ, IsPrimalOptimal P x := by
  intro m n P hf hb
  classical
  let S : Set ℝ := {v | ∃ x, PrimalFeasible P x ∧ primalValue P x = v}
  obtain ⟨x₀, hx₀⟩ := hf
  have hS : S.Nonempty := ⟨primalValue P x₀, x₀, hx₀, rfl⟩
  have hbounded : BddAbove S := by
    obtain ⟨B, hB⟩ := hb
    refine ⟨B, ?_⟩
    rintro v ⟨x, hx, rfl⟩
    exact hB x hx
  let α : ℝ := sSup S
  let Q := thresholdProgram P α
  have hQ : IsFeasible Q := by
    by_contra hn
    obtain ⟨z, hz⟩ := Lax109476.FarkasLemma.exists_infeasibility_certificate
      (m + 1) n Q hn
    let y : Fin m → ℝ := fun i => z i.castSucc
    let t : ℝ := z (Fin.last m)
    have hy : ∀ i, 0 ≤ y i := fun i => hz.1 i.castSucc
    have ht : 0 ≤ t := hz.1 (Fin.last m)
    have hcol : ∀ j, P.c j * t ≤ columnValue P y j := by
      intro j
      have h := hz.2.1 j
      change 0 ≤ columnValue (thresholdProgram P α) z j at h
      rw [threshold_column] at h
      change 0 ≤ columnValue P y j - P.c j * t at h
      linarith
    have hgap : dualValue P y < α * t := by
      have h := hz.2.2
      change dualValue (thresholdProgram P α) z < 0 at h
      rw [threshold_objective] at h
      change dualValue P y - α * t < 0 at h
      linarith
    by_cases hpos : 0 < t
    · let w : Fin m → ℝ := fun i => t⁻¹ * y i
      have hw : DualFeasible P w := by
        refine ⟨fun i => mul_nonneg (inv_nonneg.mpr ht) (hy i), ?_⟩
        intro j
        change P.c j ≤ columnValue P (fun i => t⁻¹ * y i) j
        rw [column_scale]
        calc
          P.c j = t⁻¹ * (P.c j * t) := by field_simp
          _ ≤ t⁻¹ * columnValue P y j :=
            mul_le_mul_of_nonneg_left (hcol j) (inv_nonneg.mpr ht)
      have hsup : α ≤ dualValue P w := by
        apply csSup_le hS
        rintro v ⟨x, hx, rfl⟩
        exact Lax109476.WeakDuality.primalValue_le_dualValue m n P x w hx hw
      change α ≤ dualValue P (fun i => t⁻¹ * y i) at hsup
      rw [dual_scale] at hsup
      have hscaled := mul_le_mul_of_nonneg_left hsup ht
      have heq : t * (t⁻¹ * dualValue P y) = dualValue P y := by field_simp
      rw [heq] at hscaled
      nlinarith
    · have ht0 : t = 0 := le_antisymm (le_of_not_gt hpos) ht
      have hcert : IsInfeasibilityCertificate P y := by
        refine ⟨hy, ?_, ?_⟩
        · intro j
          simpa only [ht0, mul_zero] using hcol j
        · simpa only [ht0, mul_zero] using hgap
      exact Lax109476.FarkasSoundness.certificate_not_feasible m n P y hcert ⟨x₀, hx₀⟩
  obtain ⟨x, hx⟩ := hQ
  have hxP : PrimalFeasible P x := by
    refine ⟨hx.1, ?_⟩
    intro i
    simpa [Q, thresholdProgram, rowValue] using hx.2 i.castSucc
  have hlower : α ≤ primalValue P x := by
    have h := hx.2 (Fin.last m)
    simpa [Q, thresholdProgram, rowValue, primalValue, Finset.sum_neg_distrib] using h
  refine ⟨x, hxP, ?_⟩
  intro w hw
  exact (le_csSup hbounded (show primalValue P w ∈ S from ⟨w, hw, rfl⟩)).trans hlower

end Lax109476Proofs.Attainment

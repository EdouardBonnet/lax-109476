import Lax109476Proofs.Basic
import Lax109476.OptimalDualMultipliers
import Lax109476.PrimalAttainment
import Lax109476.StrongDuality
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

namespace Lax109476Proofs.Duality

open Lax109476.LinearProgram Lax109476.FarkasCertificate

theorem row_scale {m n : ℕ} (P : Program ℝ m n) (d : Fin n → ℝ)
    (t : ℝ) (i : Fin m) : rowValue P (fun j => t * d j) i = t * rowValue P d i := by
  simp only [rowValue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem objective_scale {m n : ℕ} (P : Program ℝ m n) (d : Fin n → ℝ)
    (t : ℝ) : primalValue P (fun j => t * d j) = t * primalValue P d := by
  simp only [primalValue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem row_add {m n : ℕ} (P : Program ℝ m n) (x d : Fin n → ℝ)
    (i : Fin m) : rowValue P (fun j => x j + d j) i = rowValue P x i + rowValue P d i := by
  simp [rowValue, mul_add, Finset.sum_add_distrib]

theorem objective_add {m n : ℕ} (P : Program ℝ m n) (x d : Fin n → ℝ) :
    primalValue P (fun j => x j + d j) = primalValue P x + primalValue P d := by
  simp [primalValue, mul_add, Finset.sum_add_distrib]

private def multiplierProgram {m n : ℕ} (P : Program ℝ m n) (α : ℝ) :
    Program ℝ (n + 1) m where
  A r i := Fin.lastCases (P.b i) (fun j => -P.A i j) r
  b r := Fin.lastCases α (fun j => -P.c j) r
  c _ := 0

private theorem multiplier_row {m n : ℕ} (P : Program ℝ m n)
    (α : ℝ) (y : Fin m → ℝ) (j : Fin n) :
    rowValue (multiplierProgram P α) y j.castSucc = -columnValue P y j := by
  simp [rowValue, columnValue, multiplierProgram, Finset.sum_neg_distrib]

private theorem multiplier_last {m n : ℕ} (P : Program ℝ m n)
    (α : ℝ) (y : Fin m → ℝ) :
    rowValue (multiplierProgram P α) y (Fin.last n) = dualValue P y := by
  simp [rowValue, dualValue, multiplierProgram]

private theorem certificate_column {m n : ℕ} (P : Program ℝ m n)
    (α : ℝ) (z : Fin (n + 1) → ℝ) (i : Fin m) :
    columnValue (multiplierProgram P α) z i =
      -rowValue P (fun j => z j.castSucc) i + P.b i * z (Fin.last n) := by
  simp [columnValue, rowValue, multiplierProgram, Fin.sum_univ_castSucc,
    Finset.sum_neg_distrib]

private theorem certificate_objective {m n : ℕ} (P : Program ℝ m n)
    (α : ℝ) (z : Fin (n + 1) → ℝ) :
    dualValue (multiplierProgram P α) z =
      -primalValue P (fun j => z j.castSucc) + α * z (Fin.last n) := by
  simp [dualValue, primalValue, multiplierProgram, Fin.sum_univ_castSucc,
    Finset.sum_neg_distrib]

/--
---
conclusion: Lax109476.OptimalDualMultipliers.exists_matching_dual
---
Apply Farkas' lemma to the proposed dual multipliers with the additional
constraint $b^T y\le c^T x$. If this system is infeasible, its separating
vector consists of a nonnegative vector $d$ and scalar $\lambda$ satisfying
$Ad\le\lambda b$ and $c^T d>\lambda c^T x$.
For $\lambda>0$, the point $d/\lambda$ improves the alleged optimum.
For $\lambda=0$, the point $x+d$ improves it. Both are contradictions.
The system is therefore feasible, and weak duality gives equality.
-/
theorem optimal_dual_multipliers :
    ∀ (m n : ℕ) (P : Program ℝ m n) (x : Fin n → ℝ), IsPrimalOptimal P x →
      ∃ y : Fin m → ℝ, DualFeasible P y ∧ primalValue P x = dualValue P y := by
  intro m n P x hx
  classical
  let Q := multiplierProgram P (primalValue P x)
  have hQ : IsFeasible Q := by
    by_contra hQ
    obtain ⟨z, hz⟩ := Lax109476.FarkasLemma.exists_infeasibility_certificate
      (n + 1) m Q hQ
    let d : Fin n → ℝ := fun j => z j.castSucc
    let t : ℝ := z (Fin.last n)
    have hd : ∀ j, 0 ≤ d j := fun j => hz.1 j.castSucc
    have ht : 0 ≤ t := hz.1 (Fin.last n)
    have hrow : ∀ i, rowValue P d i ≤ P.b i * t := by
      intro i
      have h := hz.2.1 i
      change 0 ≤ columnValue (multiplierProgram P (primalValue P x)) z i at h
      rw [certificate_column] at h
      change 0 ≤ -rowValue P d i + P.b i * t at h
      linarith
    have hobj : primalValue P x * t < primalValue P d := by
      have h := hz.2.2
      change dualValue (multiplierProgram P (primalValue P x)) z < 0 at h
      rw [certificate_objective] at h
      change -primalValue P d + primalValue P x * t < 0 at h
      linarith
    by_cases hpos : 0 < t
    · let w : Fin n → ℝ := fun j => t⁻¹ * d j
      have hw : PrimalFeasible P w := by
        refine ⟨fun j => mul_nonneg (inv_nonneg.mpr ht) (hd j), ?_⟩
        intro i
        change rowValue P (fun j => t⁻¹ * d j) i ≤ P.b i
        rw [row_scale]
        calc
          t⁻¹ * rowValue P d i ≤ t⁻¹ * (P.b i * t) :=
            mul_le_mul_of_nonneg_left (hrow i) (inv_nonneg.mpr ht)
          _ = P.b i := by field_simp
      have hbest := hx.2 w hw
      change primalValue P (fun j => t⁻¹ * d j) ≤ primalValue P x at hbest
      rw [objective_scale] at hbest
      have hscaled := mul_le_mul_of_nonneg_left hbest ht
      have heq : t * (t⁻¹ * primalValue P d) = primalValue P d := by
        field_simp
      rw [heq] at hscaled
      nlinarith
    · have ht0 : t = 0 := le_antisymm (le_of_not_gt hpos) ht
      have hw : PrimalFeasible P (fun j => x j + d j) := by
        refine ⟨fun j => add_nonneg (hx.1.1 j) (hd j), ?_⟩
        intro i
        rw [row_add]
        have hi := hrow i
        rw [ht0, mul_zero] at hi
        linarith [hx.1.2 i]
      have hbest := hx.2 _ hw
      rw [objective_add] at hbest
      rw [ht0, mul_zero] at hobj
      linarith
  obtain ⟨y, hy⟩ := hQ
  have hdual : DualFeasible P y := by
    refine ⟨hy.1, ?_⟩
    intro j
    have h := hy.2 j.castSucc
    change rowValue (multiplierProgram P (primalValue P x)) y j.castSucc ≤ _ at h
    rw [multiplier_row] at h
    simp only [Q, multiplierProgram, Fin.lastCases_castSucc] at h
    linarith
  refine ⟨y, hdual, le_antisymm
    (Lax109476.WeakDuality.primalValue_le_dualValue m n P x y hx.1 hdual) ?_⟩
  have h := hy.2 (Fin.last n)
  change rowValue (multiplierProgram P (primalValue P x)) y (Fin.last n) ≤ _ at h
  rw [multiplier_last] at h
  simpa only [Q, multiplierProgram, Fin.lastCases_last] using h

/--
---
conclusion: Lax109476.StrongDuality.exists_matching_optimizers
---
Primal attainment supplies an optimizer; the optimal-dual-multipliers
theorem supplies matching dual multipliers. The graph keeps these two
independent steps visible.
-/
theorem strong_duality :
    ∀ (m n : ℕ) (P : Program ℝ m n), IsFeasible P → IsBoundedAbove P →
      ∃ (x : Fin n → ℝ) (y : Fin m → ℝ),
        PrimalFeasible P x ∧ DualFeasible P y ∧ primalValue P x = dualValue P y := by
  intro m n P hf hb
  obtain ⟨x, hx⟩ := Lax109476.PrimalAttainment.exists_primal_optimizer m n P hf hb
  obtain ⟨y, hy, heq⟩ := Lax109476.OptimalDualMultipliers.exists_matching_dual m n P x hx
  exact ⟨x, y, hx.1, hy, heq⟩

end Lax109476Proofs.Duality

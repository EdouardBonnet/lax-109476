import Lax109476.RecessionExistence
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

open scoped BigOperators

namespace Lax109476Proofs.Recession

open Lax109476.LinearProgram Lax109476.RecessionDirection

private def directionProgram {m n : ℕ} (P : Program ℝ m n) :
    Program ℝ (m + 1) n where
  A r j := Fin.lastCases (-P.c j) (fun i => P.A i j) r
  b r := Fin.lastCases (-1) (fun _ => 0) r
  c _ := 0

private theorem direction_column {m n : ℕ} (P : Program ℝ m n)
    (z : Fin (m + 1) → ℝ) (j : Fin n) :
    columnValue (directionProgram P) z j =
      columnValue P (fun i => z i.castSucc) j - P.c j * z (Fin.last m) := by
  simp [columnValue, directionProgram, Fin.sum_univ_castSucc, sub_eq_add_neg]

private theorem column_scale {m n : ℕ} (P : Program ℝ m n)
    (y : Fin m → ℝ) (t : ℝ) (j : Fin n) :
    columnValue P (fun i => t * y i) j = t * columnValue P y j := by
  simp only [columnValue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/--
---
conclusion: Lax109476.RecessionExistence.exists_improving_direction
---
Apply Farkas' lemma to $Ad\le0$, $d\ge0$, $c^Td\ge1$. An infeasibility
certificate has a strictly positive multiplier $t$ on the final row. Dividing
the other multipliers by $t$ gives a dual feasible vector for the original
program. Weak duality then supplies a finite objective bound, a contradiction.
-/
theorem recession_existence :
    ∀ (m n : ℕ) (P : Program ℝ m n), ¬ IsBoundedAbove P →
      ∃ d : Fin n → ℝ, IsImprovingDirection P d := by
  intro m n P hb
  let Q := directionProgram P
  have hQ : IsFeasible Q := by
    by_contra hn
    obtain ⟨z, hz⟩ := Lax109476.FarkasLemma.exists_infeasibility_certificate
      (m + 1) n Q hn
    let y : Fin m → ℝ := fun i => z i.castSucc
    let t : ℝ := z (Fin.last m)
    have hy : ∀ i, 0 ≤ y i := fun i => hz.1 i.castSucc
    have ht : 0 < t := by
      have h := hz.2.2
      change dualValue (directionProgram P) z < 0 at h
      simpa [dualValue, directionProgram, Fin.sum_univ_castSucc, t] using h
    have hcol : ∀ j, P.c j * t ≤ columnValue P y j := by
      intro j
      have h := hz.2.1 j
      change 0 ≤ columnValue (directionProgram P) z j at h
      rw [direction_column] at h
      change 0 ≤ columnValue P y j - P.c j * t at h
      linarith
    let w : Fin m → ℝ := fun i => t⁻¹ * y i
    have hw : DualFeasible P w := by
      refine ⟨fun i => mul_nonneg (inv_nonneg.mpr ht.le) (hy i), ?_⟩
      intro j
      change P.c j ≤ columnValue P (fun i => t⁻¹ * y i) j
      rw [column_scale]
      calc
        P.c j = t⁻¹ * (P.c j * t) := by field_simp
        _ ≤ t⁻¹ * columnValue P y j :=
          mul_le_mul_of_nonneg_left (hcol j) (inv_nonneg.mpr ht.le)
    exact hb ⟨dualValue P w, fun x hx =>
      Lax109476.WeakDuality.primalValue_le_dualValue m n P x w hx hw⟩
  obtain ⟨d, hd⟩ := hQ
  refine ⟨d, hd.1, ?_, ?_⟩
  · intro i
    have h := hd.2 i.castSucc
    simpa [Q, directionProgram, rowValue] using h
  · have h := hd.2 (Fin.last m)
    have hvalue : -primalValue P d ≤ -1 := by
      simpa [Q, directionProgram, rowValue, primalValue, Finset.sum_neg_distrib] using h
    linarith

end Lax109476Proofs.Recession

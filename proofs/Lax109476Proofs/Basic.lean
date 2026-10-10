import Lax109476.WeakDuality
import Lax109476.FarkasSoundness
import Lax109476.FarkasAlternative
import Lax109476.FarkasLemma
import Mathlib.Tactic

open scoped BigOperators

namespace Lax109476Proofs.Basic

open Lax109476.LinearProgram Lax109476.FarkasCertificate

theorem transpose_identity {m n : ℕ} (P : Program ℝ m n)
    (x : Fin n → ℝ) (y : Fin m → ℝ) :
    (∑ j, columnValue P y j * x j) = ∑ i, rowValue P x i * y i := by
  simp only [columnValue, rowValue, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/--
---
conclusion: Lax109476.WeakDuality.primalValue_le_dualValue
---
Multiply each dual inequality by the corresponding nonnegative primal
coordinate, rearrange the finite double sum, and multiply each primal
inequality by the corresponding nonnegative dual coordinate.
No LP existence theorem is used.
-/
theorem weak_duality :
    ∀ (m n : ℕ) (P : Program ℝ m n) (x : Fin n → ℝ) (y : Fin m → ℝ),
      PrimalFeasible P x → DualFeasible P y → primalValue P x ≤ dualValue P y := by
  intro m n P x y hx hy
  calc
    primalValue P x ≤ ∑ j, columnValue P y j * x j :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hy.2 j) (hx.1 j)
    _ = ∑ i, rowValue P x i * y i := transpose_identity P x y
    _ ≤ dualValue P y :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hx.2 i) (hy.1 i)

/--
---
conclusion: Lax109476.FarkasSoundness.certificate_not_feasible
---
A feasible point and a Farkas certificate would give a nonnegative
bilinear sum bounded above by a strictly negative number. This proves
soundness directly, without assuming Farkas certificate existence.
-/
theorem farkas_soundness :
    ∀ (m n : ℕ) (P : Program ℝ m n) (y : Fin m → ℝ),
      IsInfeasibilityCertificate P y → ¬ IsFeasible P := by
  intro m n P y hy ⟨x, hx⟩
  have hnonneg : 0 ≤ ∑ j, columnValue P y j * x j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hy.2.1 j) (hx.1 j)
  have hle : (∑ j, columnValue P y j * x j) ≤ dualValue P y := by
    rw [transpose_identity]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hx.2 i) (hy.1 i)
  exact (not_lt_of_ge (hnonneg.trans hle)) hy.2.2

/--
---
conclusion: Lax109476.FarkasAlternative.infeasible_iff_certificate
---
Combine Farkas certificate existence with the independent soundness theorem.
The two assumptions supply the two directions of the alternative.
-/
theorem farkas_alternative :
    ∀ (m n : ℕ) (P : Program ℝ m n),
      ¬ IsFeasible P ↔ ∃ y, IsInfeasibilityCertificate P y := by
  intro m n P
  constructor
  · exact Lax109476.FarkasLemma.exists_infeasibility_certificate m n P
  · rintro ⟨y, hy⟩
    exact Lax109476.FarkasSoundness.certificate_not_feasible m n P y hy

end Lax109476Proofs.Basic

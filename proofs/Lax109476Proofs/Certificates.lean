import Lax109476Proofs.Duality
import Lax109476.CertificateSoundness
import Lax109476.RecessionSoundness

open scoped BigOperators

namespace Lax109476Proofs.Certificates

open Lax109476.LinearProgram Lax109476.FarkasCertificate
open Lax109476.RecessionDirection Lax109476.RationalCertificates
open Lax109476Proofs.Duality

/--
---
conclusion: Lax109476.RecessionSoundness.direction_not_bounded
---
Given a proposed bound $B$, move from the feasible base point along the
improving direction by $(B-c^T x)/(c^T d)+1$. This nonnegative step preserves
feasibility and gives objective $B+c^T d>B$.
-/
theorem recession_soundness :
    ∀ (m n : ℕ) (P : Program ℝ m n) (x d : Fin n → ℝ),
      PrimalFeasible P x → IsImprovingDirection P d → ¬ IsBoundedAbove P := by
  intro m n P x d hx hd ⟨B, hB⟩
  have hbase := hB x hx
  have hpos : 0 < primalValue P d := hd.2.2
  let t := (B - primalValue P x) / primalValue P d + 1
  have ht : 0 ≤ t := by
    dsimp [t]
    exact add_nonneg (div_nonneg (sub_nonneg.mpr hbase) (le_of_lt hpos)) (by norm_num)
  let z : Fin n → ℝ := fun j => x j + t * d j
  have hz : PrimalFeasible P z := by
    refine ⟨fun j => add_nonneg (hx.1 j) (mul_nonneg ht (hd.1 j)), ?_⟩
    intro i
    change rowValue P (fun j => x j + t * d j) i ≤ P.b i
    rw [row_add, row_scale]
    have hdir : t * rowValue P d i ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos ht (hd.2.1 i)
    linarith [hx.2 i]
  have hval : primalValue P z = B + primalValue P d := by
    change primalValue P (fun j => x j + t * d j) = _
    rw [objective_add, objective_scale]
    dsimp [t]
    field_simp [ne_of_gt hpos]
    ring
  have hbound := hB z hz
  rw [hval] at hbound
  linarith [hd.2.2]

private theorem cast_row {m n : ℕ} (P : Program ℚ m n)
    (x : Fin n → ℚ) (i : Fin m) :
    rowValue (toReal P) (realVector x) i = (rowValue P x i : ℚ) := by
  simp [rowValue, toReal, realVector]

private theorem cast_column {m n : ℕ} (P : Program ℚ m n)
    (y : Fin m → ℚ) (j : Fin n) :
    columnValue (toReal P) (realVector y) j = (columnValue P y j : ℚ) := by
  simp [columnValue, toReal, realVector]

private theorem cast_primal {m n : ℕ} (P : Program ℚ m n)
    (x : Fin n → ℚ) :
    primalValue (toReal P) (realVector x) = (primalValue P x : ℚ) := by
  simp [primalValue, toReal, realVector]

private theorem cast_dual {m n : ℕ} (P : Program ℚ m n)
    (y : Fin m → ℚ) :
    dualValue (toReal P) (realVector y) = (dualValue P y : ℚ) := by
  simp [dualValue, toReal, realVector]

private theorem cast_feasible {m n : ℕ} (P : Program ℚ m n)
    (x : Fin n → ℚ) (hx : PrimalFeasible P x) :
    PrimalFeasible (toReal P) (realVector x) := by
  constructor
  · intro j
    change (0 : ℝ) ≤ (x j : ℚ)
    exact_mod_cast hx.1 j
  · intro i
    rw [cast_row]
    change ((rowValue P x i : ℚ) : ℝ) ≤ (P.b i : ℚ)
    exact_mod_cast hx.2 i

private theorem cast_dual_feasible {m n : ℕ} (P : Program ℚ m n)
    (y : Fin m → ℚ) (hy : DualFeasible P y) :
    DualFeasible (toReal P) (realVector y) := by
  constructor
  · intro i
    change (0 : ℝ) ≤ (y i : ℚ)
    exact_mod_cast hy.1 i
  · intro j
    rw [cast_column]
    change ((P.c j : ℚ) : ℝ) ≤ (columnValue P y j : ℚ)
    exact_mod_cast hy.2 j

private theorem cast_farkas {m n : ℕ} (P : Program ℚ m n)
    (y : Fin m → ℚ) (hy : IsInfeasibilityCertificate P y) :
    IsInfeasibilityCertificate (toReal P) (realVector y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change (0 : ℝ) ≤ (y i : ℚ)
    exact_mod_cast hy.1 i
  · intro j
    rw [cast_column]
    exact_mod_cast hy.2.1 j
  · rw [cast_dual]
    exact_mod_cast hy.2.2

private theorem cast_direction {m n : ℕ} (P : Program ℚ m n)
    (d : Fin n → ℚ) (hd : IsImprovingDirection P d) :
    IsImprovingDirection (toReal P) (realVector d) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    change (0 : ℝ) ≤ (d j : ℚ)
    exact_mod_cast hd.1 j
  · intro i
    rw [cast_row]
    exact_mod_cast hd.2.1 i
  · rw [cast_primal]
    exact_mod_cast hd.2.2

/--
---
conclusion: Lax109476.CertificateSoundness.valid_certificate_correct
---
Exact rational equalities and inequalities survive the embedding into the
reals. Weak duality proves optimality of a matching pair, Farkas soundness
proves infeasibility, and recession soundness proves unboundedness. Neither
certificate existence nor a solver is needed to verify an outcome.
-/
theorem certificate_soundness :
    ∀ (m n : ℕ) (P : Program ℚ m n) (certificate : Certificate m n),
      IsValidCertificate P certificate → IsCorrectOutcome P certificate := by
  intro m n P certificate h
  cases certificate with
  | optimal x y =>
      rcases h with ⟨hx, hy, heq⟩
      have hxR := cast_feasible P x hx
      have hyR := cast_dual_feasible P y hy
      have heqR : primalValue (toReal P) (realVector x) =
          dualValue (toReal P) (realVector y) := by
        rw [cast_primal, cast_dual, heq]
      refine ⟨hxR, ?_⟩
      intro z hz
      rw [heqR]
      exact Lax109476.WeakDuality.primalValue_le_dualValue m n (toReal P)
        z (realVector y) hz hyR
  | infeasible y =>
      exact Lax109476.FarkasSoundness.certificate_not_feasible m n
        (toReal P) (realVector y) (cast_farkas P y h)
  | unbounded x d =>
      have hxR := cast_feasible P x h.1
      exact ⟨⟨realVector x, hxR⟩,
        Lax109476.RecessionSoundness.direction_not_bounded m n (toReal P)
          (realVector x) (realVector d) hxR (cast_direction P d h.2)⟩

end Lax109476Proofs.Certificates

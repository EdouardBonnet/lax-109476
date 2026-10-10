import Lax109476Proofs.RationalFeasibilityDecision
import Lax109476Proofs.BinaryOptimization

open scoped BigOperators

namespace Lax109476Proofs.CoordinateOptimization

open Lax109476.LinearProgram Lax109476.RationalCertificates

/-- One additional rational inequality asks whether coordinate `j` can be
at most the binary-search threshold `t`. -/
def coordinateCut {m n : ℕ} (P : Program ℚ m n) (j : Fin n) (t : ℚ) :
    Program ℚ (m + 1) n where
  A := Fin.addCases P.A (fun _ k => if k = j then 1 else 0)
  b := Fin.addCases P.b (fun _ => t)
  c := P.c

theorem coordinateCut_feasible {m n : ℕ} (P : Program ℚ m n) (j : Fin n) (t : ℚ)
    (x : Fin n → ℝ) :
    PrimalFeasible (toReal (coordinateCut P j t)) x ↔
      PrimalFeasible (toReal P) x ∧ x j ≤ (t : ℝ) := by
  have hrow : ∀ i : Fin m, rowValue (toReal (coordinateCut P j t)) x
      (Fin.castAdd 1 i) = rowValue (toReal P) x i := by
    intro i
    simp [rowValue, toReal, coordinateCut]
  have hlast : rowValue (toReal (coordinateCut P j t)) x (Fin.natAdd m 0) = x j := by
    simp [rowValue, toReal, coordinateCut, apply_ite]
  constructor
  · rintro ⟨hx, hr⟩
    refine ⟨⟨hx, fun i => ?_⟩, ?_⟩
    · have h := hr (Fin.castAdd 1 i)
      rw [hrow] at h
      simpa [toReal, coordinateCut] using h
    · have h := hr (Fin.natAdd m 0)
      rw [hlast] at h
      simpa [toReal, coordinateCut] using h
  · rintro ⟨⟨hx, hr⟩, hj⟩
    refine ⟨hx, ?_⟩
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [hrow]
      simpa [toReal, coordinateCut] using hr i
    · have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rw [hlast]
      simpa [toReal, coordinateCut] using hj

def coordinateMinimum {m n : ℕ} (P : Program ℚ m n) (j : Fin n) (B : ℕ) : Option ℚ :=
  BinaryOptimization.minimum (fun t => RationalFeasibilityDecision.feasible (coordinateCut P j t)) B

theorem coordinateMinimum_exact {m n : ℕ} (P : Program ℚ m n) (j : Fin n)
    (x : Fin n → ℚ) (hx : PrimalFeasible (toReal P) (realVector x))
    (hmin : ∀ y, PrimalFeasible (toReal P) y → (x j : ℝ) ≤ y j)
    (B : ℕ) (hb : x j ≤ B) (hd : (x j).den ≤ B) :
    coordinateMinimum P j B = some (x j) := by
  apply BinaryOptimization.minimum_exact _ (x j) B _ _ hb hd
  · intro t
    rw [RationalFeasibilityDecision.feasible_correct]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨hyp, hyt⟩ := (coordinateCut_feasible P j t y).mp hy
      exact (Rat.cast_le (K := ℝ)).mp ((hmin y hyp).trans hyt)
    · intro ht
      refine ⟨realVector x, (coordinateCut_feasible P j t _).mpr ⟨hx, ?_⟩⟩
      exact (Rat.cast_le (K := ℝ)).mpr ht
  · exact (Rat.cast_nonneg (K := ℝ)).mp (hx.1 j)

end Lax109476Proofs.CoordinateOptimization

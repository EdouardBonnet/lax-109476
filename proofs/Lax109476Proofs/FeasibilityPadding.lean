import Lax109476Proofs.IntegerFeasibilityDecision

open scoped BigOperators

namespace Lax109476Proofs.FeasibilityPadding

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding

/-- Two nonnegative dummy variables, each constrained to be at most zero,
allow the same ellipsoid implementation to handle all input dimensions. -/
def pad {K : Type} [Zero K] [One K] {m n : ℕ} (P : Program K m n) :
    Program K (m + 2) (n + 2) where
  A := Fin.addCases (fun i => Fin.addCases (P.A i) (fun _ => 0))
    (fun k => Fin.addCases (fun _ => 0) (fun j => if k = j then 1 else 0))
  b := Fin.addCases P.b (fun _ => 0)
  c := Fin.addCases P.c (fun _ => 0)

theorem extend_feasible {m n : ℕ} (P : Program ℝ m n) (x : Fin n → ℝ)
    (hx : PrimalFeasible P x) :
    PrimalFeasible (pad P) (Fin.addCases x (fun _ => 0)) := by
  constructor
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro j
      simpa using hx.1 j
    · intro j
      simp
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      simpa [pad, rowValue, Fin.sum_univ_add] using hx.2 i
    · intro i
      simp [pad, rowValue, Fin.sum_univ_add]

theorem restrict_feasible {m n : ℕ} (P : Program ℝ m n) (x : Fin (n + 2) → ℝ)
    (hx : PrimalFeasible (pad P) x) :
    PrimalFeasible P (fun j => x (Fin.castAdd 2 j)) := by
  constructor
  · intro j
    exact hx.1 (Fin.castAdd 2 j)
  · intro i
    simpa [pad, rowValue, Fin.sum_univ_add] using hx.2 (Fin.castAdd 2 i)

theorem pad_feasible_iff {m n : ℕ} (P : Program ℝ m n) :
    IsFeasible (pad P) ↔ IsFeasible P := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨_, restrict_feasible P x hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨_, extend_feasible P x hx⟩

theorem cast_pad {m n : ℕ} (P : Program ℤ m n) :
    toReal (rationalProgram (pad P)) = pad (toReal (rationalProgram P)) := by
  unfold pad toReal rationalProgram
  congr 1
  · funext i j
    refine Fin.addCases ?_ ?_ i
    · intro i
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp
    · intro i
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [apply_ite]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro i <;> simp
  · funext j
    refine Fin.addCases ?_ ?_ j <;> intro j <;> simp

theorem padded_bounds {m n : ℕ} (P : Program ℤ m n) (H : ℕ) (hH : 1 ≤ H)
    (hA : ∀ i j, (P.A i j).natAbs ≤ H) (hb : ∀ i, (P.b i).natAbs ≤ H) :
    (∀ i j, ((pad P).A i j).natAbs ≤ H) ∧ (∀ i, ((pad P).b i).natAbs ≤ H) := by
  constructor
  · intro i j
    refine Fin.addCases ?_ ?_ i
    · intro i
      refine Fin.addCases ?_ ?_ j
      · intro j
        simpa [pad] using hA i j
      · intro j
        simp [pad]
    · intro i
      refine Fin.addCases ?_ ?_ j
      · intro j
        simp [pad]
      · intro j
        simp only [pad, Fin.addCases_right]
        split_ifs <;> simp_all
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      simpa [pad] using hb i
    · intro i
      simp [pad]

def feasible {m n : ℕ} (P : Program ℤ m n) (H : ℕ) : Bool :=
  IntegerFeasibilityDecision.feasible (pad P) H

/-- Padding supplies a computable exact feasibility decision for every
dimension; no promise of positive dimension or an interior point is needed. -/
theorem feasible_correct {m n : ℕ} (P : Program ℤ m n) (H : ℕ) (hH : 1 ≤ H)
    (hA : ∀ i j, (P.A i j).natAbs ≤ H) (hb : ∀ i, (P.b i).natAbs ≤ H) :
    feasible P H = true ↔ IsFeasible (toReal (rationalProgram P)) := by
  obtain ⟨ha, hb⟩ := padded_bounds P H hH hA hb
  rw [feasible, IntegerFeasibilityDecision.feasible_correct (pad P) H (by omega) hH ha hb,
    cast_pad, pad_feasible_iff]

end Lax109476Proofs.FeasibilityPadding

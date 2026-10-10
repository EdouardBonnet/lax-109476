import Lax109476Proofs.PointRecovery

open scoped BigOperators Matrix

namespace Lax109476Proofs.IntegerPointRecovery

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding PointRecovery

def slackMatrix {m n : ℕ} (P : Program ℤ m n) : Matrix (Fin m) (Fin (n + m)) ℤ :=
  fun i => Fin.addCases (P.A i) (fun j => if j = i then 1 else 0)

def withSlacks {m n : ℕ} (P : Program ℤ m n) (x : Fin n → ℚ) : Fin (n + m) → ℚ :=
  Fin.addCases x (fun i => (P.b i : ℚ) - rowValue (rationalProgram P) x i)

theorem slack_rows {m n : ℕ} (P : Program ℤ m n) (z : Fin (n + m) → ℚ) (i : Fin m) :
    (((slackMatrix P).map (fun a => (a : ℚ))) *ᵥ z) i =
      rowValue (rationalProgram P) (fun j => z (Fin.castAdd m j)) i + z (Fin.natAdd n i) := by
  simp [slackMatrix, Matrix.mulVec, Matrix.map, dotProduct, Fin.sum_univ_add,
    rowValue, rationalProgram, apply_ite]

theorem withSlacks_feasible {m n : ℕ} (P : Program ℤ m n) (x : Fin n → ℚ)
    (hx : PrimalFeasible (rationalProgram P) x) :
    LexicographicSupport.Feasible (slackMatrix P |>.map (fun a => (a : ℚ)))
      (fun i => (P.b i : ℚ)) (withSlacks P x) := by
  constructor
  · intro j
    refine Fin.addCases (fun j => ?_) (fun i => ?_) j
    · simpa [withSlacks] using hx.1 j
    · simpa [withSlacks, rationalProgram] using sub_nonneg.mpr (hx.2 i)
  · funext i
    rw [slack_rows]
    simp [withSlacks]

theorem slack_point_feasible {m n : ℕ} (P : Program ℤ m n) (z : Fin (n + m) → ℚ)
    (hz : LexicographicSupport.Feasible (slackMatrix P |>.map (fun a => (a : ℚ)))
      (fun i => (P.b i : ℚ)) z) :
    PrimalFeasible (rationalProgram P) (fun j => z (Fin.castAdd m j)) := by
  refine ⟨fun j => hz.1 _, fun i => ?_⟩
  have h := congrFun hz.2 i
  rw [slack_rows] at h
  have hpos := hz.1 (Fin.natAdd n i)
  change 0 ≤ z (Fin.natAdd n i) at hpos
  change rowValue _ _ _ ≤ (P.b i : ℚ)
  linarith

def point {m n : ℕ} (P : Program ℤ m n) (H : ℕ) : Option (Fin n → ℚ) :=
  (standardPoint (slackMatrix P) P.b H).map (fun z j => z (Fin.castAdd m j))

theorem point_correct {m n : ℕ} (P : Program ℤ m n) (H : ℕ) (hH : 1 ≤ H)
    (hA : ∀ i j, (P.A i j).natAbs ≤ H) (hb : ∀ i, (P.b i).natAbs ≤ H)
    (hf : ∃ x, PrimalFeasible (rationalProgram P) x) :
    ∃ x, point P H = some x ∧ PrimalFeasible (rationalProgram P) x := by
  obtain ⟨x₀, hx₀⟩ := hf
  have hC : ∀ i j, (slackMatrix P i j).natAbs ≤ H := by
    intro i j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa [slackMatrix] using hA i j
    · simp only [slackMatrix, Fin.addCases_right]
      split_ifs <;> norm_num <;> omega
  obtain ⟨z, he, hz, _⟩ := standardPoint_correct (slackMatrix P) P.b H hC hb
    ⟨withSlacks P x₀, withSlacks_feasible P x₀ hx₀⟩
  refine ⟨fun j => z (Fin.castAdd m j), ?_, slack_point_feasible P z hz⟩
  simp [point, he]

end Lax109476Proofs.IntegerPointRecovery

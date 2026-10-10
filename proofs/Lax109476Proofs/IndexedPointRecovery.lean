import Lax109476Proofs.IntegerPointRecovery
import Mathlib.Logic.Equiv.Fin.Basic

open scoped BigOperators

namespace Lax109476Proofs.IndexedPointRecovery

open Lax109476.LinearProgram IntegerEncoding

def reindexProgram {κ ι : Type*} {r n : ℕ} (A : κ → ι → ℤ) (b : κ → ℤ)
    (er : κ ≃ Fin r) (ec : ι ≃ Fin n) : Program ℤ r n where
  A i j := A (er.symm i) (ec.symm j)
  b i := b (er.symm i)
  c := 0

theorem reindex_row {κ ι : Type*} [Fintype ι] {r n : ℕ} (A : κ → ι → ℤ) (b : κ → ℤ)
    (er : κ ≃ Fin r) (ec : ι ≃ Fin n) (x : Fin n → ℚ) (i : κ) :
    rowValue (rationalProgram (reindexProgram A b er ec)) x (er i) =
      ∑ j, (A i j : ℚ) * x (ec j) := by
  have h := ec.sum_comp (fun j : Fin n => (A i (ec.symm j) : ℚ) * x j)
  simpa [rowValue, rationalProgram, reindexProgram] using h.symm

def point {κ ι : Type*} {r n : ℕ} (A : κ → ι → ℤ) (b : κ → ℤ)
    (er : κ ≃ Fin r) (ec : ι ≃ Fin n) (H : ℕ) : Option (ι → ℚ) :=
  (IntegerPointRecovery.point (reindexProgram A b er ec) H).map (fun x j => x (ec j))

theorem point_correct {κ ι : Type*} [Fintype ι] {r n : ℕ} (A : κ → ι → ℤ) (b : κ → ℤ)
    (er : κ ≃ Fin r) (ec : ι ≃ Fin n) (H : ℕ) (hH : 1 ≤ H)
    (hA : ∀ i j, (A i j).natAbs ≤ H) (hb : ∀ i, (b i).natAbs ≤ H)
    (hf : ∃ x : ι → ℚ, (∀ j, 0 ≤ x j) ∧ ∀ i, (∑ j, (A i j : ℚ) * x j) ≤ (b i : ℚ)) :
    ∃ x : ι → ℚ, point A b er ec H = some x ∧
      (∀ j, 0 ≤ x j) ∧ ∀ i, (∑ j, (A i j : ℚ) * x j) ≤ (b i : ℚ) := by
  obtain ⟨x₀, hx₀, hr₀⟩ := hf
  have hfeas : PrimalFeasible (rationalProgram (reindexProgram A b er ec))
      (fun j => x₀ (ec.symm j)) := by
    refine ⟨fun j => hx₀ _, fun i => ?_⟩
    have h := hr₀ (er.symm i)
    have he := reindex_row A b er ec (fun j => x₀ (ec.symm j)) (er.symm i)
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply] at he
    rw [he]
    exact h
  obtain ⟨x, he, hx⟩ := IntegerPointRecovery.point_correct (reindexProgram A b er ec) H hH
    (fun i j => hA _ _) (fun i => hb _) ⟨_, hfeas⟩
  refine ⟨fun j => x (ec j), ?_, fun j => hx.1 _, fun i => ?_⟩
  · simp [point, he]
  · have h := hx.2 (er i)
    rw [reindex_row] at h
    simpa [rationalProgram, reindexProgram] using h

end Lax109476Proofs.IndexedPointRecovery

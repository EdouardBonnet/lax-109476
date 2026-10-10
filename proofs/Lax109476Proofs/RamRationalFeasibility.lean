import Lax109476Proofs.RamFeasibilityQuery

namespace Lax109476Proofs.RamRationalFeasibility

open Lax109476.LinearProgram Lax109476.RationalEncoding Lax109476.RationalCertificates
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep IntegerEncoding

def decideFeasible : Com := .seq RamFeasibilityQuery.copyInput RamPaddedFeasibility.decideFeasible

def wordWidth (L : ℕ) : ℕ := RamPaddedFeasibility.wordWidth L + RamDecoder.wordWidth (2 * L)

def instructionBound (L : ℕ) : ℕ := 71 * L + 58 + RamPaddedFeasibility.instructionBound L

/-- The same total rational ellipsoid decision used by certificate recovery
is realized by a fixed command with uniform polynomial resource bounds. -/
theorem decideFeasible_spec (m n : ℕ) (P : Program ℚ m n) (w : ℕ)
    (hw : wordWidth (bitSize (encodeProgram P)) ≤ w) :
    Spec (2 ^ w) (RamFeasibilityQuery.Input P) decideFeasible
      (fun _ τ => decide (τ.vars "search.found" = 1) = RationalFeasibilityDecision.feasible P)
      (instructionBound (bitSize (encodeProgram P))) := by
  let L := bitSize (encodeProgram P)
  have hwCopy : RamDecoder.wordWidth (2 * L) ≤ w := by dsimp only [L]; unfold wordWidth at hw; omega
  have hwFeas : RamPaddedFeasibility.wordWidth L ≤ w := by dsimp only [L]; unfold wordWidth at hw; omega
  have hdim := EncodingSize.dimension_bound P
  obtain ⟨hA, hb, hc⟩ := integerProgram_bounds P
  intro σ hσ
  obtain ⟨τ, hr₁, hτ⟩ := RamFeasibilityQuery.copyInput_spec m n P w hwCopy σ hσ
  obtain ⟨υ, hr₂, hυ⟩ := RamPaddedFeasibility.decideFeasible_spec m n L w (integerProgram P)
    hdim hA hb hwFeas τ hτ
  have hcells := RamSolverInitialization.cells_bound P
  have hcost := Nat.mul_le_mul_left 71 (show m * n + m ≤ L by omega)
  exact ⟨υ, (hr₁.seq hr₂).mono (by dsimp only [instructionBound, L]; dsimp only [L] at hcost; omega), hυ⟩

theorem decideFeasible_correct_spec (m n : ℕ) (P : Program ℚ m n) (w : ℕ)
    (hw : wordWidth (bitSize (encodeProgram P)) ≤ w) :
    Spec (2 ^ w) (RamFeasibilityQuery.Input P) decideFeasible
      (fun _ τ => (τ.vars "search.found" = 1 ↔ IsFeasible (toReal P)))
      (instructionBound (bitSize (encodeProgram P))) := by
  refine (decideFeasible_spec m n P w hw).post ?_
  intro σ τ _ hτ
  have hcorrect := RationalFeasibilityDecision.feasible_correct P
  rw [← hτ, decide_eq_true_eq] at hcorrect
  exact hcorrect

end Lax109476Proofs.RamRationalFeasibility

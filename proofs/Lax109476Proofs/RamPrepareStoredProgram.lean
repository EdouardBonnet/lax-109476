import Lax109476Proofs.RamSolverInitialization

namespace Lax109476Proofs.RamPrepareStoredProgram

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamStoredProgram RationalArithmeticBounds IntegerEncoding

def prepare : Com := .seq RamProgramSize.prepareSize RamProgramDenominator.prepareDenominator
def instructionBound (L : ℕ) : ℕ := (36 * (L + 1) + 61) * L + 37 * L + 82

theorem instructionBound_monotone {L S : ℕ} (h : L ≤ S) : instructionBound L ≤ instructionBound S := by
  unfold instructionBound
  gcongr

theorem prepare_spec (m n : ℕ) (P : Program ℚ m n) (w : ℕ)
    (hw : RamDecoder.wordWidth (bitSize (encodeProgram P)) ≤ w) :
    Spec (2 ^ w) (fun σ => RepresentsProgram P σ ∧ σ.vars "input.valid" = 1) prepare
      (fun _ τ => RepresentsProgram P τ ∧ τ.vars "input.valid" = 1 ∧
        τ.vars "input.bits" = bitSize (encodeProgram P) ∧ τ.vars "den.value" = programDenominator P)
      (instructionBound (bitSize (encodeProgram P))) := by
  let L := bitSize (encodeProgram P)
  let H := 2 ^ L
  have hHL : H < 2 ^ w := Nat.pow_lt_pow_right (by decide)
    (by dsimp only [RamDecoder.wordWidth] at hw; omega)
  have hH : 1 ≤ H := Nat.one_le_pow L 2 (by decide)
  have h8 : 8 ≤ w := by dsimp only [RamDecoder.wordWidth] at hw; omega
  have h256 : 256 ≤ 2 ^ w := by simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) h8
  have h2 : 2 < 2 ^ w := by omega
  have hLB : L < 2 ^ w := (Nat.lt_two_pow_self (n := L)).trans hHL
  have hcells := RamSolverInitialization.cells_bound P
  have hmB : m < 2 ^ w := (by omega : m ≤ L).trans_lt hLB
  have hnB : n < 2 ^ w := (by omega : n ≤ L).trans_lt hLB
  have hmnB : m * n < 2 ^ w := (by omega : m * n ≤ L).trans_lt hLB
  have hA : ∀ i j, Height (P.A i j) H := fun i j => RamSolverInitialization.datum_height P (.inl (i, j))
  have hb : ∀ i, Height (P.b i) H := fun i => RamSolverInitialization.datum_height P (.inr (.inl i))
  have hc : ∀ j, Height (P.c j) H := fun j => RamSolverInitialization.datum_height P (.inr (.inr j))
  have hDB : programDenominator P < 2 ^ w := (programDenominator_bound P).trans_lt hHL
  rintro σ ⟨hσP, hσvalid⟩
  obtain ⟨τ, hr₁, hτbits, hτP, _⟩ := RamProgramSize.prepareSize_spec (2 ^ w) H m n P
    h2 hH hHL hmB hnB hmnB hA hb hc hLB σ hσP
  obtain ⟨υ, hr₂, hυden, hυP, _⟩ := RamProgramDenominator.prepareDenominator_spec (2 ^ w) m n P
    (by omega) hmB hnB hmnB hDB τ hτP
  have hυbits := (hr₂.frame_var "input.bits" (by decide)).trans hτbits
  have hυvalid := ((hr₁.seq hr₂).frame_var "input.valid" (by decide)).trans hσvalid
  have hms : m.size ≤ L := (RationalSizeBounds.size_le_self m).trans (by omega)
  have hns : n.size ≤ L := (RationalSizeBounds.size_le_self n).trans (by omega)
  have hmul := Nat.mul_le_mul_left (36 * (L + 1) + 61) hcells
  refine ⟨υ, (hr₁.seq hr₂).mono ?_, hυP, hυvalid, hυbits, hυden⟩
  simp only [instructionBound, H, Nat.size_pow, L]
  dsimp only [L] at hmul hms hns
  omega

end Lax109476Proofs.RamPrepareStoredProgram

import Lax109476Proofs.RamPrepareStoredProgram
import Lax109476Proofs.RamDecodedProgram

namespace Lax109476Proofs.RamInitializationTotal

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamStoredProgram IntegerEncoding RamDecodedProgram

def wordWidth (L : ℕ) : ℕ := RamDecoder.wordWidth (canonicalBound L)
def instructionBound (L : ℕ) : ℕ := RamSolverInitialization.instructionBound (canonicalBound L)

def Output (xs : List ℕ) (σ : Env) : Prop := σ.vars "input.valid" = 0 ∨
  (RamDecoder.AcceptedHeader xs ∧ σ.vars "input.valid" = 1 ∧ RepresentsProgram (decodedProgram xs) σ ∧
    σ.vars "input.bits" = bitSize (encodeProgram (decodedProgram xs)) ∧
    σ.vars "den.value" = programDenominator (decodedProgram xs) ∧ σ.inp = [])

theorem decoder_bound_monotone {L S : ℕ} (h : L ≤ S) :
    RamDecoder.instructionBound L (L + 1) ≤ RamDecoder.instructionBound S (S + 1) := by
  unfold RamDecoder.instructionBound
  gcongr

theorem initialize_spec (xs : List ℕ) (w : ℕ) (hw : wordWidth (bitSize xs) ≤ w) :
    Spec (2 ^ w) (RamDecoder.Input (2 ^ w) xs) RamSolverInitialization.initializeSolver
      (fun _ τ => Output xs τ ∧ τ.InpBounded (2 ^ w)) (instructionBound (bitSize xs)) := by
  let L := bitSize xs
  let C := canonicalBound L
  have hLC : L ≤ C := canonicalBound_ge L
  have hwDecode : RamDecoder.wordWidth L ≤ w := by
    dsimp only [wordWidth] at hw
    unfold RamDecoder.wordWidth at hw ⊢
    dsimp only [C, L] at hLC
    omega
  have h1 : 1 < 2 ^ w := by
    have h2w : 2 ≤ w := by unfold RamDecoder.wordWidth at hwDecode; omega
    have hp : 4 ≤ 2 ^ w := by simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) h2w
    omega
  have hDecodeCost := decoder_bound_monotone hLC
  intro σ hσ
  obtain ⟨τ, hr₁, hτ⟩ := RamDecoder.decode_bounded_spec xs w hwDecode σ hσ
  by_cases hh : RamDecoder.AcceptedHeader xs
  · obtain ⟨hτP, hτflag⟩ := output_program (2 ^ w) xs τ hh hτ
    by_cases hv : τ.vars "input.valid" = 1
    · let P := decodedProgram xs
      have hsize : bitSize (encodeProgram P) ≤ C := decoded_size xs hh
      have hwPrepare : RamDecoder.wordWidth (bitSize (encodeProgram P)) ≤ w := by
        unfold RamDecoder.wordWidth
        have hwC : RamDecoder.wordWidth C ≤ w := hw
        unfold RamDecoder.wordWidth at hwC
        omega
      obtain ⟨υ, hr₂, hυP, hυvalid, hυbits, hυden⟩ := RamPrepareStoredProgram.prepare_spec _ _ P w hwPrepare τ ⟨hτP, hv⟩
      have hτinp := output_empty_of_valid (2 ^ w) xs τ hh hτ hv
      have hυinp := (hr₂.frame_inp (by decide)).trans hτinp
      have hb : (Cond.eq (.var "input.valid") (.lit 1)).evalB (2 ^ w) τ = some true := by
        simpa [hv] using evalB_condEq
          (evalB_var (B := 2 ^ w) (σ := τ) (x := "input.valid") (by rw [hv]; exact h1)) (evalB_lit h1)
      have hr := hr₁.seq (Run.ite_true (d := .skip) hb hr₂)
      have hPrepareCost := RamPrepareStoredProgram.instructionBound_monotone hsize
      refine ⟨υ, hr.mono ?_, Or.inr ⟨hh, hυvalid, hυP, hυbits, hυden, hυinp⟩,
        hr.inpBounded hσ.2.1⟩
      dsimp only [instructionBound, RamSolverInitialization.instructionBound,
        RamPrepareStoredProgram.instructionBound, Cond.size, Expr.size] at *
      dsimp only [C, L] at hDecodeCost hPrepareCost
      omega
    · have hz : τ.vars "input.valid" = 0 := by omega
      have hb : (Cond.eq (.var "input.valid") (.lit 1)).evalB (2 ^ w) τ = some false := by
        simpa [hz] using evalB_condEq
          (evalB_var (B := 2 ^ w) (σ := τ) (x := "input.valid") (by rw [hz]; omega)) (evalB_lit h1)
      have hr := hr₁.seq (Run.ite_false (c := RamPrepareStoredProgram.prepare) hb Run.skip)
      refine ⟨τ, hr.mono ?_, Or.inl hz, hr.inpBounded hσ.2.1⟩
      dsimp only [instructionBound, RamSolverInitialization.instructionBound, Cond.size, Expr.size] at *
      dsimp only [C, L] at hDecodeCost
      omega
  · have hz : τ.vars "input.valid" = 0 := by
      have hbad := hτ
      simp only [RamDecoder.Output, if_neg hh] at hbad
      exact hbad.1
    have hb : (Cond.eq (.var "input.valid") (.lit 1)).evalB (2 ^ w) τ = some false := by
      simpa [hz] using evalB_condEq
        (evalB_var (B := 2 ^ w) (σ := τ) (x := "input.valid") (by rw [hz]; omega)) (evalB_lit h1)
    have hr := hr₁.seq (Run.ite_false (c := RamPrepareStoredProgram.prepare) hb Run.skip)
    refine ⟨τ, hr.mono ?_, Or.inl hz, hr.inpBounded hσ.2.1⟩
    dsimp only [instructionBound, RamSolverInitialization.instructionBound, Cond.size, Expr.size] at *
    dsimp only [C, L] at hDecodeCost
    omega

end Lax109476Proofs.RamInitializationTotal

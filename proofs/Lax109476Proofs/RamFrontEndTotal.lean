import Lax109476Proofs.RamInitializationTotal
import Lax109476Proofs.RamSolverFrontEnd

namespace Lax109476Proofs.RamFrontEndTotal

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamStoredProgram RamClearProgram RamEllipsoidStep RationalArithmeticBounds IntegerEncoding RamDecodedProgram

def Input (B : ℕ) (xs : List ℕ) (σ : Env) : Prop := RamDecoder.Input B xs σ ∧
  Extents "int.A" (if RamReadHeader.ValidDimensions xs then xs.headD 0 * xs.tail.headD 0 else 0) σ ∧
  Extents "int.b" (if RamReadHeader.ValidDimensions xs then xs.headD 0 else 0) σ ∧
  Extents "int.c" (if RamReadHeader.ValidDimensions xs then xs.tail.headD 0 else 0) σ

def Output (xs : List ℕ) (σ : Env) : Prop := σ.vars "input.valid" = 0 ∨
  (RamDecoder.AcceptedHeader xs ∧ RamSolverFrontEnd.Output (decodedProgram xs) σ)

def wordWidth (L : ℕ) : ℕ := RamInitializationTotal.wordWidth L
def instructionBound (L : ℕ) : ℕ := RamSolverFrontEnd.instructionBound (canonicalBound L)

theorem frontEnd_spec (xs : List ℕ) (w : ℕ) (hw : wordWidth (bitSize xs) ≤ w) :
    Spec (2 ^ w) (Input (2 ^ w) xs) RamSolverFrontEnd.frontEnd
      (fun _ τ => Output xs τ ∧ τ.InpBounded (2 ^ w)) (instructionBound (bitSize xs)) := by
  let C := canonicalBound (bitSize xs)
  have hwC : RamDecoder.wordWidth C ≤ w := hw
  have h1 : 1 < 2 ^ w := by
    have h2w : 2 ≤ w := by unfold RamDecoder.wordWidth at hwC; omega
    have hp : 4 ≤ 2 ^ w := by simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) h2w
    omega
  rintro σ ⟨hσInput, hσA, hσb, hσc⟩
  obtain ⟨τ, hr₁, hτOutput, hτBounded⟩ := RamInitializationTotal.initialize_spec xs w hw σ hσInput
  rcases hτOutput with hz | ⟨hheader, hτvalid, hτP, hτbits, hτD, hτinp⟩
  · have hb : (Cond.eq (.var "input.valid") (.lit 1)).evalB (2 ^ w) τ = some false := by
      simpa [hz] using evalB_condEq
        (evalB_var (B := 2 ^ w) (σ := τ) (x := "input.valid") (by rw [hz]; omega)) (evalB_lit h1)
    have hr := hr₁.seq (Run.ite_false (c := clearProgram) hb Run.skip)
    refine ⟨τ, hr.mono ?_, Or.inl hz, hr.inpBounded hσInput.2.1⟩
    dsimp only [instructionBound, RamSolverFrontEnd.instructionBound, RamInitializationTotal.instructionBound,
      Cond.size, Expr.size]
    omega
  · let P := decodedProgram xs
    let K := bitSize (encodeProgram P)
    let H := 2 ^ K
    have hsize : K ≤ C := decoded_size xs hheader
    have hwP : RamDecoder.wordWidth K ≤ w := by
      unfold RamDecoder.wordWidth at hwC ⊢
      omega
    have hHL : H < 2 ^ w := Nat.pow_lt_pow_right (by decide)
      (by unfold RamDecoder.wordWidth at hwP; omega)
    have hH : 1 ≤ H := Nat.one_le_pow _ _ (by decide)
    have hKB : K < 2 ^ w := (Nat.lt_two_pow_self (n := K)).trans hHL
    have hcells := RamSolverInitialization.cells_bound P
    have hmB : xs.headD 0 < 2 ^ w := (by omega : xs.headD 0 ≤ K).trans_lt hKB
    have hnB : xs.tail.headD 0 < 2 ^ w := (by omega : xs.tail.headD 0 ≤ K).trans_lt hKB
    have hmnB : xs.headD 0 * xs.tail.headD 0 < 2 ^ w :=
      (by omega : xs.headD 0 * xs.tail.headD 0 ≤ K).trans_lt hKB
    have hA : ∀ i j, Height (P.A i j) H := fun i j => RamSolverInitialization.datum_height P (.inl (i, j))
    have hb : ∀ i, Height (P.b i) H := fun i => RamSolverInitialization.datum_height P (.inr (.inl i))
    have hc : ∀ j, Height (P.c j) H := fun j => RamSolverInitialization.datum_height P (.inr (.inr j))
    have hD : programDenominator P ≤ H := programDenominator_bound P
    have hguard := RamSolverFrontEnd.clearing_word_guard K w hwP
    have hτA := RamAdvanceState.extents_of_run hr₁ "int.A" _ hσA
    have hτb := RamAdvanceState.extents_of_run hr₁ "int.b" _ hσb
    have hτc := RamAdvanceState.extents_of_run hr₁ "int.c" _ hσc
    simp only [if_pos hheader.2] at hτA hτb hτc
    obtain ⟨υ, hr₂, hυI, hυP, hυD, hυbits⟩ := clearProgram_spec (2 ^ w) H _ _ P
      hH hmB hnB hmnB hguard hA hb hc hD τ ⟨hτP, hτA, hτb, hτc, hτD⟩
    have hυvalid := (hr₂.frame_var "input.valid" (by decide)).trans hτvalid
    have hυinp := (hr₂.frame_inp (by decide)).trans hτinp
    have hbcond : (Cond.eq (.var "input.valid") (.lit 1)).evalB (2 ^ w) τ = some true := by
      simpa [hτvalid] using evalB_condEq
        (evalB_var (B := 2 ^ w) (σ := τ) (x := "input.valid") (by rw [hτvalid]; exact h1)) (evalB_lit h1)
    have hr := hr₁.seq (Run.ite_true (d := .skip) hbcond hr₂)
    have hmul : (72 * (K + 1) + 135) * (xs.headD 0 * xs.tail.headD 0 + xs.headD 0 + xs.tail.headD 0) ≤
        (72 * (C + 1) + 135) * C :=
      Nat.mul_le_mul (by omega) (hcells.trans hsize)
    refine ⟨υ, hr.mono ?_, Or.inr ⟨hheader, hυP, hυI, hυvalid, hυbits.trans hτbits, hυD, hυinp⟩,
      hr₂.inpBounded hτBounded⟩
    dsimp only [instructionBound, RamSolverFrontEnd.instructionBound, RamInitializationTotal.instructionBound,
      Cond.size, Expr.size, H] at *
    rw [Nat.size_pow]
    dsimp only [C, K, P] at hmul ⊢
    omega

end Lax109476Proofs.RamFrontEndTotal

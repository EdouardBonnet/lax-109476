import Lax109476Proofs.RamSolverInitialization
import Lax109476Proofs.RamClearProgram

namespace Lax109476Proofs.RamSolverFrontEnd

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamStoredProgram RamClearProgram RamEllipsoidStep RationalArithmeticBounds IntegerEncoding

def frontEnd : Com := .seq RamSolverInitialization.initializeSolver
  (.ite (.eq (.var "input.valid") (.lit 1)) clearProgram .skip)

def Input {m n : ℕ} (B : ℕ) (P : Program ℚ m n) (σ : Env) : Prop :=
  RamDecoder.Input B (encodeProgram P) σ ∧ Extents "int.A" (m * n) σ ∧
    Extents "int.b" m σ ∧ Extents "int.c" n σ

def Output {m n : ℕ} (P : Program ℚ m n) (τ : Env) : Prop :=
  RepresentsProgram P τ ∧ IntegerRep P τ ∧ τ.vars "input.valid" = 1 ∧
    τ.vars "input.bits" = bitSize (encodeProgram P) ∧
    τ.vars "den.value" = programDenominator P ∧ τ.inp = []

def instructionBound (L : ℕ) : ℕ := RamSolverInitialization.instructionBound L +
  (72 * (L + 1) + 135) * L + 86

theorem clearing_word_guard (L w : ℕ) (hw : RamDecoder.wordWidth L ≤ w) :
    2 * (2 ^ L) ^ 2 + 3 < 2 ^ w := by
  have he : 2 * L + 3 ≤ w := by unfold RamDecoder.wordWidth at hw; omega
  have hp : 1 ≤ 2 ^ (2 * L) := Nat.one_le_pow _ _ (by decide)
  have hlarge : 2 * (2 ^ L) ^ 2 + 3 < 2 ^ (2 * L + 3) := by
    rw [← pow_mul, Nat.mul_comm L 2, pow_add]
    norm_num
    omega
  exact hlarge.trans_le (Nat.pow_le_pow_right (by decide) he)

theorem frontEnd_valid_spec (m n : ℕ) (P : Program ℚ m n) (w : ℕ)
    (hw : RamDecoder.wordWidth (bitSize (encodeProgram P)) ≤ w) :
    Spec (2 ^ w) (Input (2 ^ w) P) frontEnd
      (fun _ τ => Output P τ ∧ τ.InpBounded (2 ^ w))
      (instructionBound (bitSize (encodeProgram P))) := by
  let L := bitSize (encodeProgram P)
  let H := 2 ^ L
  have hHL : H < 2 ^ w := Nat.pow_lt_pow_right (by decide)
    (by dsimp only [RamDecoder.wordWidth] at hw; omega)
  have hH : 1 ≤ H := Nat.one_le_pow L 2 (by decide)
  have hLB : L < 2 ^ w := (Nat.lt_two_pow_self (n := L)).trans hHL
  have hcells := RamSolverInitialization.cells_bound P
  have hmB : m < 2 ^ w := (by omega : m ≤ L).trans_lt hLB
  have hnB : n < 2 ^ w := (by omega : n ≤ L).trans_lt hLB
  have hmnB : m * n < 2 ^ w := (by omega : m * n ≤ L).trans_lt hLB
  have hA : ∀ i j, Height (P.A i j) H := fun i j => RamSolverInitialization.datum_height P (.inl (i, j))
  have hb : ∀ i, Height (P.b i) H := fun i => RamSolverInitialization.datum_height P (.inr (.inl i))
  have hc : ∀ j, Height (P.c j) H := fun j => RamSolverInitialization.datum_height P (.inr (.inr j))
  have hD : programDenominator P ≤ H := programDenominator_bound P
  have hB := clearing_word_guard L w hw
  rintro σ ⟨hσ, hσA, hσb, hσc⟩
  obtain ⟨τ, hr₁, hτP, hτvalid, hτbits, hτD, hτinp, hτbounded⟩ :=
    RamSolverInitialization.initialize_valid_spec m n P w hw σ hσ
  have hτA := RamAdvanceState.extents_of_run hr₁ "int.A" (m * n) hσA
  have hτb := RamAdvanceState.extents_of_run hr₁ "int.b" m hσb
  have hτc := RamAdvanceState.extents_of_run hr₁ "int.c" n hσc
  obtain ⟨υ, hr₂, hυI, hυP, hυD, hυbits⟩ := clearProgram_spec (2 ^ w) H m n P
    hH hmB hnB hmnB hB hA hb hc hD τ ⟨hτP, hτA, hτb, hτc, hτD⟩
  have hυvalid := (hr₂.frame_var "input.valid" (by decide)).trans hτvalid
  have hυinp := (hr₂.frame_inp (by decide)).trans hτinp
  have hcond : (Cond.eq (.var "input.valid") (.lit 1)).evalB (2 ^ w) τ = some true := by
    simpa [hτvalid] using evalB_condEq
      (evalB_var (B := 2 ^ w) (σ := τ) (x := "input.valid") (by rw [hτvalid]; omega))
      (evalB_lit (by omega : 1 < 2 ^ w))
  have hr := hr₁.seq (Run.ite_true (d := .skip) hcond hr₂)
  have hmul := Nat.mul_le_mul_left (72 * (L + 1) + 135) hcells
  refine ⟨υ, hr.mono ?_, ⟨hυP, hυI, hυvalid, hυbits.trans hτbits, hυD, hυinp⟩,
    hr₂.inpBounded hτbounded⟩
  simp only [instructionBound, Cond.size, Expr.size, H, Nat.size_pow, L]
  dsimp only [L] at hmul
  omega

end Lax109476Proofs.RamSolverFrontEnd

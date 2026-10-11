import Lax109476Proofs.RamSolverTotalExecution

namespace Lax109476Proofs.RamSolverCanonicalExecution

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamEllipsoidStep RamSolverWorkspace RamUniformSolverBounds

def Input {m n : ℕ} (B : ℕ) (P : Program ℚ m n) (σ : Env) : Prop :=
  RamSolverFrontEnd.Input B P σ ∧ Extents "source.A" (m * n) σ ∧
  Extents "source.b" m σ ∧ Extents "source.c" n σ ∧
  All m n (stackLength (bitSize (encodeProgram P))) σ

theorem front_cost_monotone {L K : ℕ} (h : L ≤ K) :
    RamSolverFrontEnd.instructionBound L ≤ RamSolverFrontEnd.instructionBound K := by
  unfold RamSolverFrontEnd.instructionBound RamSolverInitialization.instructionBound RamDecoder.instructionBound
  gcongr

theorem solve_spec (m n w : ℕ) (P : Program ℚ m n)
    (hw : wordWidth (bitSize (encodeProgram P)) ≤ w) :
    Spec (2 ^ w) (Input (2 ^ w) P) RamExactSolverProgram.solve (RamSolverFinish.Result P)
      (instructionBound (bitSize (encodeProgram P))) := by
  let L := bitSize (encodeProgram P)
  have hL : L ≤ canonicalSize L := RamDecodedProgram.canonicalBound_ge L
  have hwFront : RamDecoder.wordWidth L ≤ w := by
    have hh : RamDecoder.wordWidth (canonicalSize L) ≤ w := front_width L w hw
    unfold RamDecoder.wordWidth at hh ⊢
    omega
  have h1 : 1 < 2 ^ w := by
    have hw2 : 2 ≤ w := by unfold RamDecoder.wordWidth at hwFront; omega
    have hp : 4 ≤ 2 ^ w := by simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hw2
    omega
  rintro σ ⟨hσInput, hσA, hσb, hσc, hσAll⟩
  obtain ⟨τ, hrFront, hτFront, hτBound⟩ := RamSolverFrontEnd.frontEnd_valid_spec m n P w hwFront σ hσInput
  have hτA := RamAdvanceState.extents_of_run hrFront _ _ hσA
  have hτb := RamAdvanceState.extents_of_run hrFront _ _ hσb
  have hτc := RamAdvanceState.extents_of_run hrFront _ _ hσc
  have hτAll := all_of_run hrFront _ _ _ hσAll
  obtain ⟨υ, hrFinish, cert, hυout, hvalid⟩ := RamSolverFinish.finish_spec m n (stackLength L) w P
    (branch_width L L w hL hw) (stack_depth L L hL) τ ⟨hτFront, hτA, hτb, hτc, hτAll⟩
  have hcond : (Cond.eq (.var "input.valid") (.lit 1)).evalB (2 ^ w) τ = some true := by
    simpa [hτFront.2.2.1] using evalB_condEq
      (evalB_var (B := 2 ^ w) (σ := τ) (x := "input.valid")
        (by rw [hτFront.2.2.1]; exact h1)) (evalB_lit h1)
  have hr := hrFront.seq (Run.ite_true (d := .skip) hcond hrFinish)
  have hfrontCost := front_cost_monotone hL
  have hbranchCost := branch_cost_monotone (parameter_monotone hL)
  refine ⟨υ, hr.mono ?_, cert, ?_, hvalid⟩
  · dsimp only [instructionBound, RamFrontEndTotal.instructionBound, RamSolverFinish.instructionBound,
      Cond.size, Expr.size, parameter, canonicalSize, L] at *
    omega
  · simpa only [hrFront.out_eq RamSolverTotalExecution.front_noWrite] using hυout

end Lax109476Proofs.RamSolverCanonicalExecution

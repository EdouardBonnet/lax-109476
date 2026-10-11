import Lax109476Proofs.RamSolverFinish

namespace Lax109476Proofs.RamSolverTotalExecution

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamSolverWorkspace RamDecodedProgram RamUniformSolverBounds

def Input (B : ℕ) (xs : List ℕ) (σ : Env) : Prop :=
  RamFrontEndTotal.Input B xs σ ∧
  Extents "source.A" (xs.headD 0 * xs.tail.headD 0) σ ∧
  Extents "source.b" (xs.headD 0) σ ∧ Extents "source.c" (xs.tail.headD 0) σ ∧
  All (xs.headD 0) (xs.tail.headD 0) (stackLength (bitSize xs)) σ

def Result (xs : List ℕ) (σ τ : Env) : Prop :=
  (τ.vars "input.valid" = 0 ∧ τ.out = σ.out) ∨ RamSolverFinish.Result (decodedProgram xs) σ τ

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
theorem front_noWrite : RamSolverFrontEnd.frontEnd.NoWrite := by decide

theorem solve_spec (xs : List ℕ) (w : ℕ) (hw : wordWidth (bitSize xs) ≤ w) :
    Spec (2 ^ w) (Input (2 ^ w) xs) RamExactSolverProgram.solve (Result xs)
      (instructionBound (bitSize xs)) := by
  let L := bitSize xs
  have h1 : 1 < 2 ^ w := by
    have hwF := front_width L w hw
    have hh : RamDecoder.wordWidth (canonicalBound L) ≤ w := hwF
    have hw2 : 2 ≤ w := by unfold RamDecoder.wordWidth at hh; omega
    have hp : 4 ≤ 2 ^ w := by simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hw2
    omega
  rintro σ ⟨hσFront, hσA, hσb, hσc, hσAll⟩
  obtain ⟨τ, hrFront, hτResult, hτBound⟩ := RamFrontEndTotal.frontEnd_spec xs w (front_width L w hw) σ hσFront
  rcases hτResult with hτzero | ⟨hheader, hτFront⟩
  · have hcond : (Cond.eq (.var "input.valid") (.lit 1)).evalB (2 ^ w) τ = some false := by
      simpa [hτzero] using evalB_condEq
        (evalB_var (B := 2 ^ w) (σ := τ) (x := "input.valid") (by rw [hτzero]; omega)) (evalB_lit h1)
    have hr := hrFront.seq (Run.ite_false
      (c := .seq RamCertificateSetup.save RamExactSolverProgram.chooseCertificate) hcond Run.skip)
    exact ⟨τ, hr.mono (by
      dsimp only [instructionBound, Cond.size, Expr.size]
      omega), Or.inl ⟨hτzero, hrFront.out_eq front_noWrite⟩⟩
  · let P := decodedProgram xs
    let K := bitSize (encodeProgram P)
    have hK : K ≤ canonicalSize L := decoded_size xs hheader
    have hτA := RamAdvanceState.extents_of_run hrFront _ _ hσA
    have hτb := RamAdvanceState.extents_of_run hrFront _ _ hσb
    have hτc := RamAdvanceState.extents_of_run hrFront _ _ hσc
    have hτAll := all_of_run hrFront _ _ _ hσAll
    obtain ⟨υ, hrFinish, cert, hυout, hvalid⟩ := RamSolverFinish.finish_spec _ _ (stackLength L) w P
      (branch_width L K w hK hw) (stack_depth L K hK) τ ⟨hτFront, hτA, hτb, hτc, hτAll⟩
    have hcond : (Cond.eq (.var "input.valid") (.lit 1)).evalB (2 ^ w) τ = some true := by
      simpa [hτFront.2.2.1] using evalB_condEq
        (evalB_var (B := 2 ^ w) (σ := τ) (x := "input.valid")
          (by rw [hτFront.2.2.1]; exact h1)) (evalB_lit h1)
    have hr := hrFront.seq (Run.ite_true (d := .skip) hcond hrFinish)
    have hcost := branch_cost_monotone (parameter_monotone hK)
    refine ⟨υ, hr.mono ?_, Or.inr ⟨cert, ?_, hvalid⟩⟩
    · dsimp only [instructionBound, RamSolverFinish.instructionBound, Cond.size, Expr.size,
        parameter, K, P, L] at *
      omega
    · simpa only [hrFront.out_eq front_noWrite] using hυout

end Lax109476Proofs.RamSolverTotalExecution

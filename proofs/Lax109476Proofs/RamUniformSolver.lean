import Lax109476Proofs.RamSolverAllocation
import Lax109476Proofs.RamSolverCanonicalExecution
import Lax109476Proofs.RamSolverOutputBounds
import Lax109476Proofs.RamAutomaticLayout
import Lax109476.PolynomialTimeSolver

namespace Lax109476Proofs.RamUniformSolver

open Lax109476.LinearProgram Lax109476.RationalEncoding Lax109476.RationalCertificates
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Transfer

theorem run_exists (xs : List ℕ) : ∃ τ,
    Run (2 ^ RamUniformSolverBounds.wordWidth (bitSize xs)) RamExactSolverProgram.solve
      (initEnv (RamSolverAllocation.ext xs) (xs.length :: xs)) τ
      (RamUniformSolverBounds.instructionBound (bitSize xs)) := by
  obtain ⟨τ, hr, _⟩ := RamSolverTotalExecution.solve_spec xs _ le_rfl _
    (RamSolverAllocation.initialized xs _ (RamSolverOutputBounds.input_fits xs))
  exact ⟨τ, hr⟩

noncomputable def finalEnv (xs : List ℕ) : Env := Classical.choose (run_exists xs)
noncomputable def solve (xs : List ℕ) : List ℕ := (finalEnv xs).out

theorem run_spec (xs : List ℕ) :
    Run (2 ^ RamUniformSolverBounds.wordWidth (bitSize xs)) RamExactSolverProgram.solve
      (initEnv (RamSolverAllocation.ext xs) (xs.length :: xs)) (finalEnv xs)
      (RamUniformSolverBounds.instructionBound (bitSize xs)) := Classical.choose_spec (run_exists xs)

theorem polynomial_time : RamPolytime solve := by
  have hWidth := RamUniformSolverBounds.width_polynomial
  have hCost := RamUniformSolverBounds.cost_polynomial
  unfold RamResourcePolynomial.HasPolynomial at hWidth hCost
  obtain ⟨W, hW⟩ := hWidth
  obtain ⟨T, hT⟩ := hCost
  apply RamTransfer.ramPolytime_of_solves (RamAutomaticLayout.layout RamExactSolverProgram.solve)
    RamExactSolverProgram.solve solve W T
  · intro xs; rw [hW]; exact RamUniformSolverBounds.positive _
  · intro xs v hv
    rw [hW]
    simp only [List.mem_append] at hv
    rcases hv with hv | hv
    · exact RamSolverOutputBounds.input_fits xs v hv
    · exact RamSolverOutputBounds.output_of_run (run_spec xs) (by simp [initEnv]) v hv
  · refine ⟨RamAutomaticLayout.layout_ok _, ?_, ?_⟩
    · rintro tape ⟨xs, rfl⟩
      simp only [List.tail_cons]
      rw [hW]
      exact RamSolverOutputBounds.input_fits xs
    · rintro tape ⟨xs, rfl⟩
      refine ⟨RamSolverAllocation.ext xs, finalEnv xs, ?_, rfl⟩
      simp only [List.tail_cons]
      rw [hW, hT]
      exact run_spec xs

theorem initialized_canonical (m n : ℕ) (P : Program ℚ m n) :
    RamSolverCanonicalExecution.Input
      (2 ^ RamUniformSolverBounds.wordWidth (bitSize (encodeProgram P))) P
      (initEnv (RamSolverAllocation.ext (encodeProgram P)) ((encodeProgram P).length :: encodeProgram P)) := by
  have h := RamSolverAllocation.initialized (encodeProgram P) _ (RamSolverOutputBounds.input_fits _)
  have hdim := (RamDecoder.encodedHeader_accepted m n P).2
  have hm : (encodeProgram P).headD 0 = m := by rw [WordDecoding.encodeProgram_rows]; rfl
  have hn : (encodeProgram P).tail.headD 0 = n := by rw [WordDecoding.encodeProgram_rows]; rfl
  rcases h with ⟨⟨hDecoder, hIntA, hIntb, hIntc⟩, hSourceA, hSourceb, hSourcec, hAll⟩
  simp only [if_pos hdim, hm, hn] at hIntA hIntb hIntc hSourceA hSourceb hSourcec hAll
  exact ⟨⟨hDecoder, hIntA, hIntb, hIntc⟩, hSourceA, hSourceb, hSourcec, hAll⟩

theorem correct (m n : ℕ) (P : Program ℚ m n) : ∃ certificate : Certificate m n,
    solve (encodeProgram P) = encodeCertificate certificate ∧ IsValidCertificate P certificate := by
  obtain ⟨τ, hr, cert, hout, hvalid⟩ := RamSolverCanonicalExecution.solve_spec m n _ P le_rfl _
    (initialized_canonical m n P)
  obtain ⟨_, _, hbig⟩ := hr.bigStep
  obtain ⟨_, _, hactual⟩ := (run_spec (encodeProgram P)).bigStep
  have heq := (BigStep.unique hbig hactual).1
  refine ⟨cert, ?_, hvalid⟩
  change (finalEnv (encodeProgram P)).out = encodeCertificate cert
  rw [← heq]
  simpa [initEnv] using hout

/--
---
conclusion: Lax109476.PolynomialTimeSolver.exists_exact_polynomial_time_solver
---
One fixed structured command decodes arbitrary input, selects a feasible
certificate system using exact ellipsoid decisions, recovers a rational
point, and writes its certificate. Its polynomial bounds transfer through
the registered compiler and word-RAM model.
-/
theorem exists_exact_polynomial_time_solver :
    ∃ solve : List ℕ → List ℕ, RamPolytime solve ∧
      ∀ (m n : ℕ) (P : Program ℚ m n), ∃ certificate : Certificate m n,
        solve (encodeProgram P) = encodeCertificate certificate ∧ IsValidCertificate P certificate :=
  ⟨solve, polynomial_time, correct⟩

end Lax109476Proofs.RamUniformSolver

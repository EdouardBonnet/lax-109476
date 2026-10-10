import Lax109476Proofs.RamRationalFeasibility

namespace Lax109476Proofs.RamEncodedFeasibility

open Lax109476.LinearProgram Lax109476.RationalEncoding Lax109476.RationalCertificates
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def decideFeasible : Com := .seq RamSolverFrontEnd.frontEnd
  (.ite (.eq (.var "input.valid") (.lit 1)) RamRationalFeasibility.decideFeasible .skip)

def wordWidth (L : ℕ) : ℕ := RamDecoder.wordWidth L + RamRationalFeasibility.wordWidth L

def instructionBound (L : ℕ) : ℕ := RamSolverFrontEnd.instructionBound L +
  RamRationalFeasibility.instructionBound L + 4

def Input {m n : ℕ} (B : ℕ) (P : Program ℚ m n) (σ : Env) : Prop :=
  RamSolverFrontEnd.Input B P σ ∧ RamFeasibilityQuery.Workspace m n σ

/-- Decoding, denominator clearing, padding, parameter setup, normalization,
and exact ellipsoid search compose on the registered binary LP input. -/
theorem decideFeasible_spec (m n : ℕ) (P : Program ℚ m n) (w : ℕ)
    (hw : wordWidth (bitSize (encodeProgram P)) ≤ w) :
    Spec (2 ^ w) (Input (2 ^ w) P) decideFeasible
      (fun _ τ => decide (τ.vars "search.found" = 1) = RationalFeasibilityDecision.feasible P)
      (instructionBound (bitSize (encodeProgram P))) := by
  have hwFront : RamDecoder.wordWidth (bitSize (encodeProgram P)) ≤ w := by unfold wordWidth at hw; omega
  have hwFeas : RamRationalFeasibility.wordWidth (bitSize (encodeProgram P)) ≤ w := by unfold wordWidth at hw; omega
  have h1 : 1 < 2 ^ w := by
    have hwidth : 0 < w := by unfold RamDecoder.wordWidth at hwFront; omega
    exact Nat.one_lt_pow (ne_of_gt hwidth) (by decide)
  rintro σ ⟨hσfront, hσwork⟩
  obtain ⟨τ, hr₁, ⟨⟨hτA, hτb, hτc, hτm, hτn, hτcount⟩, hτint, hτvalid, hτbits, hτden, hτinp⟩, hτbound⟩ :=
    RamSolverFrontEnd.frontEnd_valid_spec m n P w hwFront σ hσfront
  have hτwork : RamFeasibilityQuery.Workspace m n τ := by
    rcases hσwork with ⟨hA, hb, hpadA, hpadb, hrows, hrhs, hcenter, hshape, hell, hnormal⟩
    exact ⟨RamAdvanceState.extents_of_run hr₁ _ _ hA,
      RamAdvanceState.extents_of_run hr₁ _ _ hb,
      RamAdvanceState.extents_of_run hr₁ _ _ hpadA,
      RamAdvanceState.extents_of_run hr₁ _ _ hpadb,
      RamAdvanceState.extents_of_run hr₁ _ _ hrows,
      RamAdvanceState.extents_of_run hr₁ _ _ hrhs,
      RamAdvanceState.extents_of_run hr₁ _ _ hcenter,
      RamAdvanceState.extents_of_run hr₁ _ _ hshape,
      RamAdvanceState.workspace_of_run hr₁ _ hell,
      RamAdvanceState.extents_of_run hr₁ _ _ hnormal⟩
  obtain ⟨υ, hr₂, hυ⟩ := RamRationalFeasibility.decideFeasible_spec m n P w hwFeas τ
    ⟨hτint, hτwork, hτm, hτn, hτcount, hτbits⟩
  have hcond : (Cond.eq (.var "input.valid") (.lit 1)).evalB (2 ^ w) τ = some true := by
    simpa [hτvalid] using evalB_condEq
      (evalB_var (B := 2 ^ w) (σ := τ) (x := "input.valid") (hτvalid ▸ h1)) (evalB_lit h1)
  exact ⟨υ, (hr₁.seq (Run.ite_true (d := .skip) hcond hr₂)).mono
    (by simp only [instructionBound, Cond.size, Expr.size]; omega), hυ⟩

theorem decideFeasible_correct_spec (m n : ℕ) (P : Program ℚ m n) (w : ℕ)
    (hw : wordWidth (bitSize (encodeProgram P)) ≤ w) :
    Spec (2 ^ w) (Input (2 ^ w) P) decideFeasible
      (fun _ τ => (τ.vars "search.found" = 1 ↔ IsFeasible (toReal P)))
      (instructionBound (bitSize (encodeProgram P))) := by
  refine (decideFeasible_spec m n P w hw).post ?_
  intro σ τ _ hτ
  have hcorrect := RationalFeasibilityDecision.feasible_correct P
  rw [← hτ, decide_eq_true_eq] at hcorrect
  exact hcorrect

end Lax109476Proofs.RamEncodedFeasibility

import Lax109476Proofs.RamSolverOriginalContext

namespace Lax109476Proofs.RamSolverBranchFrames

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamExactSolverProgram

def leaves : List Com := [optimalSystem, infeasibleSystem, unboundedSystem,
  optimalDecision, infeasibleDecision, optimalRecovery, infeasibleRecovery, unboundedRecovery,
  RamCertificateSetup.restore]

theorem included (c : Com) (hc : c ∈ leaves) :
    (c.wvars ⊆ chooseCertificate.wvars) ∧ (c.warrs ⊆ chooseCertificate.warrs) := by
  simp only [leaves, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor <;> intro a ha
  all_goals simp only [chooseCertificate, afterOptimal, afterInfeasible, Com.wvars, Com.warrs,
    List.mem_append] at *
  all_goals tauto

theorem context_of_leaf {B k m n L : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ k)
    (hc : c ∈ leaves) (P : Program ℤ m n) (hσ : RamSolverOriginalContext.Context P L σ) :
    RamSolverOriginalContext.Context P L τ :=
  RamSolverOriginalContext.context_of_run hr P hσ (included c hc).1 (included c hc).2

theorem relabel_noWrite (f : String → String) (c : Com) :
    (RamArrayRelabel.command f c).NoWrite ↔ c.NoWrite := by
  induction c <;> simp_all [RamArrayRelabel.command, Com.NoWrite]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
theorem build_noWrite : optimalSystem.NoWrite ∧ infeasibleSystem.NoWrite ∧ unboundedSystem.NoWrite := by
  simp only [optimalSystem, infeasibleSystem, unboundedSystem, RamCertificateArrayRelabel.isolated,
    relabel_noWrite]
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
theorem stored_decision_noWrite : RamStoredFeasibility.decideFeasible.NoWrite := by decide

theorem decision_noWrite : optimalDecision.NoWrite ∧ infeasibleDecision.NoWrite := by
  simp only [optimalDecision, infeasibleDecision, RamCertificateDecision.decideFeasible,
    Com.NoWrite, RamArrayRelabel.prefixed, relabel_noWrite, stored_decision_noWrite, and_true]
  constructor
  all_goals unfold RamCertificateDecision.prepare
  all_goals decide

theorem restore_noWrite : RamCertificateSetup.restore.NoWrite := by decide

end Lax109476Proofs.RamSolverBranchFrames

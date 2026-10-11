import Lax109476Proofs.RamExactSolverProgram

namespace Lax109476Proofs.RamSolverWorkspace

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamCertificateArrayRelabel

def recoveryView (name : String) (σ : Env) : Env := RamArrayRelabel.view (relabel name) σ

def Recovery (name : String) (r s N : ℕ) (σ : Env) : Prop :=
  Extents "system.A" (r * s) (recoveryView name σ) ∧
  Extents "system.b" r (recoveryView name σ) ∧
  Extents "point.A" ((r + r) * (s + r)) (recoveryView name σ) ∧
  Extents "point.b" (r + r) (recoveryView name σ) ∧
  Extents "point.x" (s + r) (recoveryView name σ) ∧
  RamRecoveryThreshold.Workspace (r + r) (s + r) (recoveryView name σ) ∧
  ((recoveryView name σ).arrs "cf.stack").length = N

def Decision (name : String) (r s : ℕ) (σ : Env) : Prop :=
  Extents "lp.A" (r * s) (RamCertificateDecision.prefixedView name σ) ∧
  Extents "lp.b" r (RamCertificateDecision.prefixedView name σ) ∧
  Extents "lp.c" s (RamCertificateDecision.prefixedView name σ) ∧
  Extents "int.A" (r * s) (RamCertificateDecision.prefixedView name σ) ∧
  Extents "int.b" r (RamCertificateDecision.prefixedView name σ) ∧
  Extents "int.c" s (RamCertificateDecision.prefixedView name σ) ∧
  RamFeasibilityQuery.Workspace r s (RamCertificateDecision.prefixedView name σ)

def All (m n N : ℕ) (σ : Env) : Prop :=
  Recovery "optimal.recovery." (m + (n + 2)) (n + m) N σ ∧
  Decision "optimal.decision." (m + (n + 2)) (n + m) σ ∧
  Recovery "infeasible.recovery." (n + 1) m N σ ∧
  Decision "infeasible.decision." (n + 1) m σ ∧
  Recovery "unbounded.recovery." (m + (m + 1)) (n + n) N σ

theorem recovery_of_run {B k : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ k)
    (name : String) (r s N : ℕ) (hσ : Recovery name r s N σ) : Recovery name r s N τ := by
  obtain ⟨_, _, hstep⟩ := hr.bigStep
  have hlen := RamAdvanceState.array_length_of_bigStep hstep
  simpa only [Recovery, recoveryView, RamArrayRelabel.view, Extents,
    RamRecoveryThreshold.Workspace, RamRecoveryQuery.Extent, RamFeasibilityQuery.Workspace,
    RamEllipsoidStep.Workspace, hlen] using hσ

theorem decision_of_run {B k : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ k)
    (name : String) (r s : ℕ) (hσ : Decision name r s σ) : Decision name r s τ := by
  obtain ⟨_, _, hstep⟩ := hr.bigStep
  have hlen := RamAdvanceState.array_length_of_bigStep hstep
  simpa only [Decision, RamCertificateDecision.prefixedView, RamArrayRelabel.view, Extents,
    RamFeasibilityQuery.Workspace, RamEllipsoidStep.Workspace, hlen] using hσ

theorem all_of_run {B k : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ k)
    (m n N : ℕ) (hσ : All m n N σ) : All m n N τ :=
  ⟨recovery_of_run hr _ _ _ _ hσ.1, decision_of_run hr _ _ _ hσ.2.1,
    recovery_of_run hr _ _ _ _ hσ.2.2.1, decision_of_run hr _ _ _ hσ.2.2.2.1,
    recovery_of_run hr _ _ _ _ hσ.2.2.2.2⟩

theorem recovery_input {r s S N : ℕ} (F : Program ℤ r s) (name : String) (σ : Env)
    (hData : RamEquationData.Data F (recoveryView name σ)) (hH : σ.vars "system.H" = 2 ^ (2 * S))
    (hW : Recovery name r s N σ) : RamRecoverFeasibleSystem.Input F S N (recoveryView name σ) :=
  ⟨hData, hH, hW.2.2.1, hW.2.2.2.1, hW.2.2.2.2.1, hW.2.2.2.2.2.1, hW.2.2.2.2.2.2⟩

theorem decision_input {r s : ℕ} (F : Program ℤ r s) (source target : String) (σ : Env)
    (hData : RamEquationData.Data F (RamCertificateDecision.prefixedView source σ))
    (hW : Decision target r s σ) : RamCertificateDecision.Input F source target σ := by
  simpa only [RamCertificateDecision.Input, Decision, RamCertificateDecision.prefixedView,
    RamArrayRelabel.view, Extents, String.append_assoc] using And.intro hData hW

theorem equation_data_view {r s : ℕ} (F : Program ℤ r s) (name : String) (σ : Env) :
    RamEquationData.Data F (recoveryView name σ) ↔
      RamEquationData.Data F (RamCertificateDecision.prefixedView name σ) := by
  simp [RamEquationData.Data, recoveryView, RamCertificateDecision.prefixedView,
    RamArrayRelabel.view, RamRationalArrays.Represents, relabel, sourceNames]

end Lax109476Proofs.RamSolverWorkspace

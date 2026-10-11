import Lax109476Proofs.RamSolverBranchFrames
import Lax109476Proofs.RamSolverBranchComposition

namespace Lax109476Proofs.RamSolverBranchSpecs

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamCertificateArrayRelabel RamSolverWorkspace RamSolverOriginalContext

def State {m n : ℕ} (P : Program ℤ m n) (L N : ℕ) (σ : Env) : Prop :=
  Context P L σ ∧ All m n N σ

theorem state_of_leaf {B k m n L N : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ k)
    (hc : c ∈ RamSolverBranchFrames.leaves) (P : Program ℤ m n) (hσ : State P L N σ) : State P L N τ :=
  ⟨RamSolverBranchFrames.context_of_leaf hr hc P hσ.1, all_of_run hr _ _ _ hσ.2⟩

theorem build_spec (B m n r s L N K : ℕ) (P : Program ℤ m n) (F : Program ℤ r s)
    (name : String) (c : Com) (hname : ∀ a ∈ sourceNames, a.length < name.length)
    (hleaf : isolated name c ∈ RamSolverBranchFrames.leaves) (hNoWrite : (isolated name c).NoWrite)
    (hWork : ∀ σ, All m n N σ → Recovery name r s N σ)
    (hbuild : Spec B (RamCertificateFamilies.Input P r s) c
      (fun _ τ => RamCertificateSource.Data P τ ∧ RamEquationData.Data F τ) K) :
    Spec B (fun σ => RamCertificateSource.Data P σ ∧ State P L N σ) (isolated name c)
      (RamSolverBranchComposition.BuildPost (State P L N) (fun σ => RamEquationData.Data F (recoveryView name σ))) K := by
  rintro σ ⟨hσSource, hσState⟩
  have hσW := hWork σ hσState.2
  have hσInput : RamCertificateFamilies.Input P r s (recoveryView name σ) :=
    ⟨(source_data_view P name σ).mpr hσSource, hσW.1, hσW.2.1⟩
  obtain ⟨τ, hr, _, hτData⟩ := spec_isolated name hname hbuild σ hσInput
  exact ⟨τ, hr, state_of_leaf hr hleaf P hσState, hτData, hr.out_eq hNoWrite⟩

theorem decision_spec (B m n r s L N K : ℕ) (P : Program ℤ m n) (F : Program ℤ r s)
    (source target : String) (f : Bool)
    (hleaf : RamCertificateDecision.decideFeasible source target ∈ RamSolverBranchFrames.leaves)
    (hNoWrite : (RamCertificateDecision.decideFeasible source target).NoWrite)
    (hWork : ∀ σ, All m n N σ → Decision target r s σ)
    (hdecision : Spec B (RamCertificateDecision.Input F source target)
      (RamCertificateDecision.decideFeasible source target)
      (fun _ τ => RamEquationData.Data F (RamCertificateDecision.prefixedView source τ) ∧
        RamBisectionCommit.condition.evalB B τ = some f) K) :
    Spec B (fun σ => State P L N σ ∧ RamEquationData.Data F (recoveryView source σ))
      (RamCertificateDecision.decideFeasible source target)
      (RamSolverBranchComposition.DecisionPost (State P L N)
        (fun σ => RamEquationData.Data F (recoveryView source σ)) B f) K := by
  rintro σ ⟨hσState, hσData⟩
  have hσInput := decision_input F source target σ ((equation_data_view F source σ).mp hσData)
    (hWork σ hσState.2)
  obtain ⟨τ, hr, hτData, hτcond⟩ := hdecision σ hσInput
  exact ⟨τ, hr, state_of_leaf hr hleaf P hσState,
    (equation_data_view F source τ).mpr hτData, hτcond, hr.out_eq hNoWrite⟩

theorem recovery_spec (B m n r s L N K tag : ℕ) (P : Program ℤ m n) (F : Program ℤ r s)
    (name : String) (hname : ∀ a ∈ sourceNames, a.length < name.length)
    (hWork : ∀ σ, All m n N σ → Recovery name r s N σ)
    (hrecovery : Spec B (RamRecoverFeasibleSystem.Input F (RamCertificateSetup.parameter L) N)
      (RamRecoverCertificate.recover tag) (RamSolverBranchComposition.Result P) K) :
    Spec B (fun σ => State P L N σ ∧ RamEquationData.Data F (recoveryView name σ))
      (isolated name (RamRecoverCertificate.recover tag)) (RamSolverBranchComposition.Result P) K := by
  rintro σ ⟨hσState, hσData⟩
  have hσInput := recovery_input F name σ hσData hσState.1.2.2 (hWork σ hσState.2)
  obtain ⟨τ, hr, cert, hτout, hvalid⟩ := spec_isolated name hname hrecovery σ hσInput
  exact ⟨τ, hr, cert, hτout, hvalid⟩

theorem restore_spec (B m n L N : ℕ) (P : Program ℤ m n) (hm : m < B) (hn : n < B) :
    Spec B (State P L N) RamCertificateSetup.restore
      (fun σ τ => RamCertificateSource.Data P τ ∧ State P L N τ ∧ τ.out = σ.out) 4 := by
  intro σ hσ
  obtain ⟨τ, hr, hτSource, hτContext⟩ := RamSolverOriginalContext.restore_spec B m n L P hm hn σ hσ.1
  exact ⟨τ, hr, hτSource, ⟨hτContext, all_of_run hr _ _ _ hσ.2⟩,
    hr.out_eq RamSolverBranchFrames.restore_noWrite⟩

end Lax109476Proofs.RamSolverBranchSpecs

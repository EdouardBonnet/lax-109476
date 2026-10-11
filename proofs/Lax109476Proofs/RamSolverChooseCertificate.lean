import Lax109476Proofs.RamSolverBranchSpecs
import Lax109476Proofs.RamSolverBranchBounds

namespace Lax109476Proofs.RamSolverChooseCertificate

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamExactSolverProgram RamCertificateArrayRelabel RamSolverBranchSpecs RamSolverWorkspace

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2400000 in
theorem choose_spec (m n L N w : ℕ) (P : Program ℤ m n) (hdim : m + n ≤ L)
    (hw : RamSolverBranchBounds.wordWidth (RamCertificateSetup.parameter L) ≤ w)
    (hN : RamRationalReconstruction.depthBound
      (RamRecoverFeasibleSystem.recoveryBits (RamCertificateSetup.parameter L)) + 1 ≤ N)
    (hA : ∀ i j, (P.A i j).natAbs ≤ 2 ^ (2 * RamCertificateSetup.parameter L))
    (hb : ∀ i, (P.b i).natAbs ≤ 2 ^ (2 * RamCertificateSetup.parameter L))
    (hc : ∀ j, (P.c j).natAbs ≤ 2 ^ (2 * RamCertificateSetup.parameter L)) :
    Spec (2 ^ w) (fun σ => RamCertificateSource.Data P σ ∧ State P L N σ)
      chooseCertificate (RamSolverBranchComposition.Result P)
      (RamSolverBranchBounds.instructionBound (RamCertificateSetup.parameter L)) := by
  let S := RamCertificateSetup.parameter L
  let H := 2 ^ (2 * S)
  let KO := RamSolverBranchBounds.buildCost S
  let KD := RamSolverBranchBounds.decisionCost S
  let KR := RamSolverBranchBounds.recoveryCost S
  have hS : 2 * (m + n) + 2 ≤ S := by dsimp only [S, RamCertificateSetup.parameter]; omega
  have hm : m ≤ S := by omega
  have hn : n ≤ S := by omega
  have hoR : m + (n + 2) ≤ S := by omega
  have hoC : n + m ≤ S := by omega
  have hiR : n + 1 ≤ S := by omega
  have huR : m + (m + 1) ≤ S := by omega
  have huC : n + n ≤ S := by omega
  have hH : 1 ≤ H := Nat.one_le_pow _ _ (by decide)
  have hHB : H < 2 ^ w := (RamSolverBranchBounds.guards S w hw).1
  have hSource := RamSolverBranchBounds.source_guard hm hn (by omega) hw
  have hoGuard := RamSolverBranchBounds.product_guard hoR hoC hw
  have hiGuard := RamSolverBranchBounds.product_guard hiR hm hw
  have huGuard := RamSolverBranchBounds.product_guard huR huC hw
  have hoA := CertificateFamilyHeight.optimal_A_bound P H hA hb hc
  have hob := CertificateFamilyHeight.optimal_b_bound P H hb hc
  have hiA := CertificateFamilyHeight.infeasible_A_bound P H hA hb
  have hib := CertificateFamilyHeight.infeasible_b_bound P H hH
  have huA := CertificateFamilyHeight.unbounded_A_bound P H hA hc
  have hub := CertificateFamilyHeight.unbounded_b_bound P H hH hb
  have hoBuildRaw := (RamCertificateFamilies.optimal_spec (2 ^ w) H m n P hH hHB hSource hoGuard hA hb hc).mono (K' := KO)
    (by have hh := RamSolverBranchBounds.build_cost hoR hoC; dsimp only [KO]; omega)
  have hiBuildRaw := (RamCertificateFamilies.infeasible_spec (2 ^ w) H m n P hH hHB hSource hiGuard hA hb).mono (K' := KO)
    (by have hh := RamSolverBranchBounds.build_cost hiR hm; dsimp only [KO]; omega)
  have huBuildRaw := (RamCertificateFamilies.unbounded_spec (2 ^ w) H m n P hH hHB hSource huGuard hA hb hc).mono (K' := KO)
    (by have hh := RamSolverBranchBounds.build_cost huR huC; dsimp only [KO]; omega)
  have hoBuild := build_spec (2 ^ w) m n _ _ L N KO P (CertificateFamilyPrograms.optimal P)
    "optimal.recovery." RamCertificateFamilies.optimal optimal_prefix
    (by change optimalSystem ∈ RamSolverBranchFrames.leaves; simp [RamSolverBranchFrames.leaves])
    RamSolverBranchFrames.build_noWrite.1 (fun _ h => h.1) hoBuildRaw
  have hiBuild := build_spec (2 ^ w) m n _ _ L N KO P (CertificateFamilyPrograms.infeasible P)
    "infeasible.recovery." RamCertificateFamilies.infeasible infeasible_prefix
    (by change infeasibleSystem ∈ RamSolverBranchFrames.leaves; simp [RamSolverBranchFrames.leaves])
    RamSolverBranchFrames.build_noWrite.2.1 (fun _ h => h.2.2.1) hiBuildRaw
  have huBuild := build_spec (2 ^ w) m n _ _ L N KO P (CertificateFamilyPrograms.unbounded P)
    "unbounded.recovery." RamCertificateFamilies.unbounded unbounded_prefix
    (by change unboundedSystem ∈ RamSolverBranchFrames.leaves; simp [RamSolverBranchFrames.leaves])
    RamSolverBranchFrames.build_noWrite.2.2 (fun _ h => h.2.2.2.2) huBuildRaw
  have hoFrameA : ∀ t ∈ RamCopy.suffixes,
      "optimal.recovery." ++ ("system.A" ++ t) ∉ optimalDecision.warrs := by
    intro t ht; simp [RamCopy.suffixes] at ht
    rcases ht with rfl | rfl | rfl
    · exact optimal_stored_system_preserved.1
    · exact optimal_stored_system_preserved.2.1
    · exact optimal_stored_system_preserved.2.2.1
  have hoFrameb : ∀ t ∈ RamCopy.suffixes,
      "optimal.recovery." ++ ("system.b" ++ t) ∉ optimalDecision.warrs := by
    intro t ht; simp [RamCopy.suffixes] at ht
    rcases ht with rfl | rfl | rfl
    · exact optimal_stored_system_preserved.2.2.2.1
    · exact optimal_stored_system_preserved.2.2.2.2.1
    · exact optimal_stored_system_preserved.2.2.2.2.2
  have hiFrameA : ∀ t ∈ RamCopy.suffixes,
      "infeasible.recovery." ++ ("system.A" ++ t) ∉ infeasibleDecision.warrs := by
    intro t ht; simp [RamCopy.suffixes] at ht
    rcases ht with rfl | rfl | rfl
    · exact infeasible_stored_system_preserved.1
    · exact infeasible_stored_system_preserved.2.1
    · exact infeasible_stored_system_preserved.2.2.1
  have hiFrameb : ∀ t ∈ RamCopy.suffixes,
      "infeasible.recovery." ++ ("system.b" ++ t) ∉ infeasibleDecision.warrs := by
    intro t ht; simp [RamCopy.suffixes] at ht
    rcases ht with rfl | rfl | rfl
    · exact infeasible_stored_system_preserved.2.2.2.1
    · exact infeasible_stored_system_preserved.2.2.2.2.1
    · exact infeasible_stored_system_preserved.2.2.2.2.2
  have hoDecideRaw := (RamCertificateDecision.decideFeasible_spec _ _ S w (CertificateFamilyPrograms.optimal P)
    "optimal.recovery." "optimal.decision." hHB hoGuard (RamSolverBranchBounds.decision_width hoR hoC hw)
    hoA hob (fun _ => rfl)
    (by simp [RamCopy.Disjoint, RamCopy.suffixes]) (by simp [RamCopy.Disjoint, RamCopy.suffixes])
    (by simp [RamCopy.Disjoint, RamCopy.suffixes]) hoFrameA hoFrameb).mono
    (RamSolverBranchBounds.decision_cost hoR hoC)
  have hiDecideRaw := (RamCertificateDecision.decideFeasible_spec _ _ S w (CertificateFamilyPrograms.infeasible P)
    "infeasible.recovery." "infeasible.decision." hHB hiGuard (RamSolverBranchBounds.decision_width hiR hm hw)
    hiA hib (fun _ => rfl)
    (by simp [RamCopy.Disjoint, RamCopy.suffixes]) (by simp [RamCopy.Disjoint, RamCopy.suffixes])
    (by simp [RamCopy.Disjoint, RamCopy.suffixes]) hiFrameA hiFrameb).mono
    (RamSolverBranchBounds.decision_cost hiR hm)
  have hoDecide := decision_spec (2 ^ w) m n _ _ L N KD P (CertificateFamilyPrograms.optimal P)
    "optimal.recovery." "optimal.decision." _
    (by change optimalDecision ∈ RamSolverBranchFrames.leaves; simp [RamSolverBranchFrames.leaves])
    RamSolverBranchFrames.decision_noWrite.1 (fun _ h => h.2.1) hoDecideRaw
  have hiDecide := decision_spec (2 ^ w) m n _ _ L N KD P (CertificateFamilyPrograms.infeasible P)
    "infeasible.recovery." "infeasible.decision." _
    (by change infeasibleDecision ∈ RamSolverBranchFrames.leaves; simp [RamSolverBranchFrames.leaves])
    RamSolverBranchFrames.decision_noWrite.2 (fun _ h => h.2.2.2.1) hiDecideRaw
  have hoRecover : (∃ x, PrimalFeasible (IntegerEncoding.rationalProgram (CertificateFamilyPrograms.optimal P)) x) →
      Spec (2 ^ w) (fun σ => State P L N σ ∧ RamEquationData.Data (CertificateFamilyPrograms.optimal P)
        (recoveryView "optimal.recovery." σ)) optimalRecovery (RamSolverBranchComposition.Result P) KR := by
    intro hf
    exact recovery_spec (2 ^ w) m n _ _ L N KR 0 P _ "optimal.recovery." optimal_prefix (fun _ h => h.1)
      ((RamRecoverCertificate.optimal_spec m n S N w P (by omega)
        (RamSolverBranchBounds.recovery_width hoR hoC hw) hN hoA hob hf).mono
          (RamSolverBranchBounds.recovery_cost hoR hoC))
  have hiRecover : (∃ x, PrimalFeasible (IntegerEncoding.rationalProgram (CertificateFamilyPrograms.infeasible P)) x) →
      Spec (2 ^ w) (fun σ => State P L N σ ∧ RamEquationData.Data (CertificateFamilyPrograms.infeasible P)
        (recoveryView "infeasible.recovery." σ)) infeasibleRecovery (RamSolverBranchComposition.Result P) KR := by
    intro hf
    exact recovery_spec (2 ^ w) m n _ _ L N KR 1 P _ "infeasible.recovery." infeasible_prefix (fun _ h => h.2.2.1)
      ((RamRecoverCertificate.infeasible_spec m n S N w P (by omega)
        (RamSolverBranchBounds.recovery_width hiR hm hw) hN hiA hib hf).mono
          (RamSolverBranchBounds.recovery_cost hiR hm))
  have huRecover : (∃ x, PrimalFeasible (IntegerEncoding.rationalProgram (CertificateFamilyPrograms.unbounded P)) x) →
      Spec (2 ^ w) (fun σ => State P L N σ ∧ RamEquationData.Data (CertificateFamilyPrograms.unbounded P)
        (recoveryView "unbounded.recovery." σ)) unboundedRecovery (RamSolverBranchComposition.Result P) KR := by
    intro hf
    exact recovery_spec (2 ^ w) m n _ _ L N KR 2 P _ "unbounded.recovery." unbounded_prefix (fun _ h => h.2.2.2.2)
      ((RamRecoverCertificate.unbounded_spec m n S N w P (by omega)
        (RamSolverBranchBounds.recovery_width huR huC hw) hN huA hub hf).mono
          (RamSolverBranchBounds.recovery_cost huR huC))
  have hsmall := (RamSolverBranchBounds.guards S w hw).2
  have hmB : m < 2 ^ w := by nlinarith
  have hnB : n < 2 ^ w := by nlinarith
  have hcombined := RamSolverBranchComposition.choose_spec (2 ^ w) m n H KO KO KO KD KD KR P hH hA hb
    (State P L N) _ _ _ hoBuild hiBuild huBuild hoDecide hiDecide
    (restore_spec (2 ^ w) m n L N P hmB hnB) hoRecover hiRecover huRecover
  exact hcombined.mono (by
    dsimp only [RamSolverBranchBounds.instructionBound, KO, KD, KR, S]
    simp only [RamBisectionCommit.condition, Cond.size, Expr.size]
    omega)

end Lax109476Proofs.RamSolverChooseCertificate

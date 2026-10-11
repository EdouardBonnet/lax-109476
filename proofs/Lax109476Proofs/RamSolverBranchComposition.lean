import Lax109476Proofs.RamSolverAlternative
import Lax109476Proofs.RamExactSolverProgram

namespace Lax109476Proofs.RamSolverBranchComposition

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open IntegerEncoding RamExactSolverProgram

def Result {m n : ℕ} (P : Program ℤ m n) (σ τ : Env) : Prop :=
  ∃ certificate : Certificate m n,
    τ.out = σ.out ++ encodeCertificate certificate ∧ IsValidCertificate (rationalProgram P) certificate

def BuildPost (State Data : Env → Prop) (σ τ : Env) : Prop := State τ ∧ Data τ ∧ τ.out = σ.out
def DecisionPost (State Data : Env → Prop) (B : ℕ) (f : Bool) (σ τ : Env) : Prop :=
  State τ ∧ Data τ ∧ RamBisectionCommit.condition.evalB B τ = some f ∧ τ.out = σ.out

theorem choose_spec (B m n H KO KI KU DO DI KR : ℕ) (P : Program ℤ m n)
    (hH : 1 ≤ H) (hA : ∀ i j, (P.A i j).natAbs ≤ H) (hb : ∀ i, (P.b i).natAbs ≤ H)
    (State DataO DataI DataU : Env → Prop)
    (hoBuild : Spec B (fun σ => RamCertificateSource.Data P σ ∧ State σ) optimalSystem
      (BuildPost State DataO) KO)
    (hiBuild : Spec B (fun σ => RamCertificateSource.Data P σ ∧ State σ) infeasibleSystem
      (BuildPost State DataI) KI)
    (huBuild : Spec B (fun σ => RamCertificateSource.Data P σ ∧ State σ) unboundedSystem
      (BuildPost State DataU) KU)
    (hoDecide : Spec B (fun σ => State σ ∧ DataO σ) optimalDecision
      (DecisionPost State DataO B (RationalFeasibilityDecision.feasible
        (rationalProgram (CertificateFamilyPrograms.optimal P)))) DO)
    (hiDecide : Spec B (fun σ => State σ ∧ DataI σ) infeasibleDecision
      (DecisionPost State DataI B (RationalFeasibilityDecision.feasible
        (rationalProgram (CertificateFamilyPrograms.infeasible P)))) DI)
    (hrestore : Spec B State RamCertificateSetup.restore
      (fun σ τ => RamCertificateSource.Data P τ ∧ State τ ∧ τ.out = σ.out) 4)
    (hoRecover : (∃ x, PrimalFeasible (rationalProgram (CertificateFamilyPrograms.optimal P)) x) →
      Spec B (fun σ => State σ ∧ DataO σ) optimalRecovery (Result P) KR)
    (hiRecover : (∃ x, PrimalFeasible (rationalProgram (CertificateFamilyPrograms.infeasible P)) x) →
      Spec B (fun σ => State σ ∧ DataI σ) infeasibleRecovery (Result P) KR)
    (huRecover : (∃ x, PrimalFeasible (rationalProgram (CertificateFamilyPrograms.unbounded P)) x) →
      Spec B (fun σ => State σ ∧ DataU σ) unboundedRecovery (Result P) KR) :
    Spec B (fun σ => RamCertificateSource.Data P σ ∧ State σ) chooseCertificate (Result P)
      (KO + KI + KU + DO + DI + KR + 10 + 2 * RamBisectionCommit.condition.size) := by
  intro σ hσ
  obtain ⟨τ, hrO, hτState, hτData, hτout⟩ := hoBuild σ hσ
  obtain ⟨υ, hrDO, hυState, hυData, hυcond, hυout⟩ := hoDecide τ ⟨hτState, hτData⟩
  cases hfO : RationalFeasibilityDecision.feasible (rationalProgram (CertificateFamilyPrograms.optimal P)) with
  | true =>
    obtain ⟨ρ, hrR, cert, hρout, hvalid⟩ := hoRecover (RamSolverAlternative.feasible_point _ hfO) υ ⟨hυState, hυData⟩
    have hr := hrO.seq (hrDO.seq (Run.ite_true (d := .seq RamCertificateSetup.restore
      (.seq infeasibleSystem (.seq infeasibleDecision afterInfeasible))) (hfO ▸ hυcond) hrR))
    exact ⟨ρ, hr.mono (by omega), cert, by simpa only [hυout, hτout] using hρout, hvalid⟩
  | false =>
    obtain ⟨ρ, hrReset, hρSource, hρState, hρout⟩ := hrestore υ hυState
    obtain ⟨ξ, hrI, hξState, hξData, hξout⟩ := hiBuild ρ ⟨hρSource, hρState⟩
    obtain ⟨ζ, hrDI, hζState, hζData, hζcond, hζout⟩ := hiDecide ξ ⟨hξState, hξData⟩
    cases hfI : RationalFeasibilityDecision.feasible (rationalProgram (CertificateFamilyPrograms.infeasible P)) with
    | true =>
      obtain ⟨η, hrR, cert, hηout, hvalid⟩ := hiRecover (RamSolverAlternative.feasible_point _ hfI) ζ ⟨hζState, hζData⟩
      have hrAfterI := Run.ite_true (d := .seq RamCertificateSetup.restore (.seq unboundedSystem unboundedRecovery))
        (hfI ▸ hζcond) hrR
      have hrAfterO := Run.ite_false (c := optimalRecovery) (hfO ▸ hυcond)
        (hrReset.seq (hrI.seq (hrDI.seq hrAfterI)))
      have hr := hrO.seq (hrDO.seq hrAfterO)
      exact ⟨η, hr.mono (by omega), cert,
        by simpa only [hζout, hξout, hρout, hυout, hτout] using hηout, hvalid⟩
    | false =>
      obtain ⟨η, hrResetI, hηSource, hηState, hηout⟩ := hrestore ζ hζState
      obtain ⟨θ, hrU, hθState, hθData, hθout⟩ := huBuild η ⟨hηSource, hηState⟩
      have hfU := RamSolverAlternative.remaining_unbounded P H hH hA hb hfO hfI
      obtain ⟨ι, hrR, cert, hιout, hvalid⟩ := huRecover hfU θ ⟨hθState, hθData⟩
      have hrAfterI := Run.ite_false (c := infeasibleRecovery) (hfI ▸ hζcond) (hrResetI.seq (hrU.seq hrR))
      have hrAfterO := Run.ite_false (c := optimalRecovery) (hfO ▸ hυcond)
        (hrReset.seq (hrI.seq (hrDI.seq hrAfterI)))
      have hr := hrO.seq (hrDO.seq hrAfterO)
      exact ⟨ι, hr.mono (by omega), cert,
        by simpa only [hθout, hηout, hζout, hξout, hρout, hυout, hτout] using hιout, hvalid⟩

end Lax109476Proofs.RamSolverBranchComposition

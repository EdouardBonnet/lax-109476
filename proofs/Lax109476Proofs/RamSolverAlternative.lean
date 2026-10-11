import Lax109476Proofs.CertificateFamilyPrograms
import Lax109476Proofs.RationalFeasibilityDecision

namespace Lax109476Proofs.RamSolverAlternative

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding

theorem feasible_point {m n : ℕ} (P : Program ℤ m n)
    (h : RationalFeasibilityDecision.feasible (rationalProgram P) = true) :
    ∃ x, PrimalFeasible (rationalProgram P) x :=
  RationalFeasibility.rational_feasibility m n _ ((RationalFeasibilityDecision.feasible_correct _).mp h)

theorem remaining_unbounded {m n : ℕ} (P : Program ℤ m n) (H : ℕ) (hH : 1 ≤ H)
    (hA : ∀ i j, (P.A i j).natAbs ≤ H) (hb : ∀ i, (P.b i).natAbs ≤ H)
    (ho : RationalFeasibilityDecision.feasible (rationalProgram (CertificateFamilyPrograms.optimal P)) = false)
    (hi : RationalFeasibilityDecision.feasible (rationalProgram (CertificateFamilyPrograms.infeasible P)) = false) :
    ∃ x, PrimalFeasible (rationalProgram (CertificateFamilyPrograms.unbounded P)) x := by
  have hno : ¬ IsFeasible (toReal (rationalProgram (CertificateFamilyPrograms.optimal P))) := by
    intro h
    have ht := (RationalFeasibilityDecision.feasible_correct _).mpr h
    rw [ho] at ht
    cases ht
  have hni : ¬ IsFeasible (toReal (rationalProgram (CertificateFamilyPrograms.infeasible P))) := by
    intro h
    have ht := (RationalFeasibilityDecision.feasible_correct _).mpr h
    rw [hi] at ht
    cases ht
  rcases CertificateFamilyPrograms.some_family_feasible P H hH hA hb with h | h | h
  · exact False.elim (hno h)
  · exact False.elim (hni h)
  · exact RationalFeasibility.rational_feasibility _ _ _ h

end Lax109476Proofs.RamSolverAlternative

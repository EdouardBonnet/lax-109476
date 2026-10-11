import Lax109476Proofs.RamResourcePolynomial

namespace Lax109476Proofs.RamSolverBranchBounds

def wordWidth (S : ℕ) : ℕ := RamRecoverFeasibleSystem.wordWidth S S S +
  RamStoredFeasibility.wordWidth (RamCertificateDecision.sizeBound S S S)

def recoveryCost (S : ℕ) : ℕ := RamRecoverFeasibleSystem.instructionBound S S S + 35 * S + 10
def buildCost (S : ℕ) : ℕ := 142 * (S * S) + 98 * S + 74
def decisionCost (S : ℕ) : ℕ := RamCertificateDecision.instructionBound S S S
def instructionBound (S : ℕ) : ℕ := 3 * buildCost S + 2 * decisionCost S + recoveryCost S + 32

theorem guards (S w : ℕ) (hw : wordWidth S ≤ w) :
    2 ^ (2 * S) < 2 ^ w ∧ S * S + 2 * S + 8 < 2 ^ w := by
  have hh : RamRecoverFeasibleSystem.wordWidth S S S ≤ w := by unfold wordWidth at hw; omega
  have hguard : S * S + 2 * S + 8 ≤ w := by
    unfold RamRecoverFeasibleSystem.wordWidth RamCoordinateCapBounds.wordWidth at hh
    nlinarith
  have hexp : 2 * S < w := by
    unfold RamRecoverFeasibleSystem.wordWidth RamCoordinateCapBounds.wordWidth at hh
    nlinarith
  exact ⟨Nat.pow_lt_pow_right (by decide) hexp, hguard.trans_lt (Nat.lt_two_pow_self (n := w))⟩

theorem product_guard {r s S w : ℕ} (hr : r ≤ S) (hs : s ≤ S) (hw : wordWidth S ≤ w) :
    r * s + r + s + 4 < 2 ^ w := by
  have hprod := Nat.mul_le_mul hr hs
  have hh := (guards S w hw).2
  omega

theorem source_guard {m n S w : ℕ} (hm : m ≤ S) (hn : n ≤ S) (hDim : m + n ≤ S)
    (hw : wordWidth S ≤ w) : m * n + 2 * m + 2 * n + 8 < 2 ^ w := by
  have hprod := Nat.mul_le_mul hm hn
  have hh := (guards S w hw).2
  omega

theorem recovery_width {r s S w : ℕ} (hr : r ≤ S) (hs : s ≤ S) (hw : wordWidth S ≤ w) :
    RamRecoverFeasibleSystem.wordWidth r s S ≤ w :=
  (RamRecoveryResourceMonotonicity.recovery_width hr hs le_rfl).trans (by unfold wordWidth at hw; omega)

theorem recovery_cost {r s S : ℕ} (hr : r ≤ S) (hs : s ≤ S) :
    RamRecoverFeasibleSystem.instructionBound r s S + 35 * s + 10 ≤ recoveryCost S := by
  have h := RamRecoveryResourceMonotonicity.recovery_cost hr hs (show S ≤ S from le_rfl)
  unfold recoveryCost
  omega

theorem decision_width {r s S w : ℕ} (hr : r ≤ S) (hs : s ≤ S) (hw : wordWidth S ≤ w) :
    RamStoredFeasibility.wordWidth (RamCertificateDecision.sizeBound r s S) ≤ w := by
  have hsize : RamCertificateDecision.sizeBound r s S ≤ RamCertificateDecision.sizeBound S S S := by
    unfold RamCertificateDecision.sizeBound
    gcongr
  exact (RamStoredFeasibilityBounds.wordWidth_monotone hsize).trans (by unfold wordWidth at hw; omega)

theorem decision_cost {r s S : ℕ} (hr : r ≤ S) (hs : s ≤ S) :
    RamCertificateDecision.instructionBound r s S ≤ decisionCost S := by
  unfold decisionCost RamCertificateDecision.instructionBound
  have hsize : RamCertificateDecision.sizeBound r s S ≤ RamCertificateDecision.sizeBound S S S := by
    unfold RamCertificateDecision.sizeBound
    gcongr
  have hstored := RamStoredFeasibilityBounds.instructionBound_monotone hsize
  have hp := Nat.mul_le_mul hr hs
  omega

theorem build_cost {r s S : ℕ} (hr : r ≤ S) (hs : s ≤ S) :
    142 * (r * s) + 98 * r + 74 ≤ buildCost S := by
  have hp := Nat.mul_le_mul hr hs
  unfold buildCost
  omega

theorem width_polynomial : RamResourcePolynomial.HasPolynomial wordWidth := by
  unfold wordWidth
  apply RamResourcePolynomial.add RamResourcePolynomial.recovery_width RamResourcePolynomial.decision_width

theorem cost_polynomial : RamResourcePolynomial.HasPolynomial instructionBound := by
  unfold instructionBound recoveryCost buildCost decisionCost
  apply RamResourcePolynomial.add
  · apply RamResourcePolynomial.add
    · apply RamResourcePolynomial.add
      · apply RamResourcePolynomial.mul (RamResourcePolynomial.constant 3)
        exact RamResourcePolynomial.add
          (RamResourcePolynomial.add
            (RamResourcePolynomial.mul (RamResourcePolynomial.constant 142)
              (RamResourcePolynomial.mul RamResourcePolynomial.identity RamResourcePolynomial.identity))
            (RamResourcePolynomial.mul (RamResourcePolynomial.constant 98) RamResourcePolynomial.identity))
          (RamResourcePolynomial.constant 74)
      · exact RamResourcePolynomial.mul (RamResourcePolynomial.constant 2) RamResourcePolynomial.decision_cost
    · apply RamResourcePolynomial.add
      · exact RamResourcePolynomial.add RamResourcePolynomial.recovery_cost
          (RamResourcePolynomial.mul (RamResourcePolynomial.constant 35) RamResourcePolynomial.identity)
      · exact RamResourcePolynomial.constant 10
  · exact RamResourcePolynomial.constant 32

end Lax109476Proofs.RamSolverBranchBounds

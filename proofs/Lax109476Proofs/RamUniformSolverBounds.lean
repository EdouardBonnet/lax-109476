import Lax109476Proofs.RamSolverChooseCertificate
import Lax109476Proofs.RamFrontEndTotal

namespace Lax109476Proofs.RamUniformSolverBounds

open RamResourcePolynomial

def canonicalSize (L : ℕ) : ℕ := RamDecodedProgram.canonicalBound L
def parameter (L : ℕ) : ℕ := RamCertificateSetup.parameter (canonicalSize L)
def stackLength (L : ℕ) : ℕ := RamRationalReconstruction.depthBound
  (RamRecoverFeasibleSystem.recoveryBits (parameter L)) + 1
def wordWidth (L : ℕ) : ℕ := RamFrontEndTotal.wordWidth L +
  RamSolverBranchBounds.wordWidth (parameter L) + 32 * (parameter L + 1) ^ 2 + 32
def instructionBound (L : ℕ) : ℕ := RamFrontEndTotal.instructionBound L +
  71 * canonicalSize L + 100 + RamSolverBranchBounds.instructionBound (parameter L) + 16

@[gcongr] theorem decision_size_monotone {r s S t u T : ℕ} (hr : r ≤ t) (hs : s ≤ u) (hS : S ≤ T) :
    RamCertificateDecision.sizeBound r s S ≤ RamCertificateDecision.sizeBound t u T := by
  unfold RamCertificateDecision.sizeBound
  gcongr

@[gcongr] theorem decision_cost_monotone {r s S t u T : ℕ} (hr : r ≤ t) (hs : s ≤ u) (hS : S ≤ T) :
    RamCertificateDecision.instructionBound r s S ≤ RamCertificateDecision.instructionBound t u T := by
  unfold RamCertificateDecision.instructionBound
  gcongr

@[gcongr] theorem branch_width_monotone {S T : ℕ} (h : S ≤ T) :
    RamSolverBranchBounds.wordWidth S ≤ RamSolverBranchBounds.wordWidth T := by
  unfold RamSolverBranchBounds.wordWidth
  gcongr

@[gcongr] theorem branch_cost_monotone {S T : ℕ} (h : S ≤ T) :
    RamSolverBranchBounds.instructionBound S ≤ RamSolverBranchBounds.instructionBound T := by
  unfold RamSolverBranchBounds.instructionBound RamSolverBranchBounds.buildCost
    RamSolverBranchBounds.decisionCost RamSolverBranchBounds.recoveryCost
  gcongr

@[gcongr] theorem parameter_monotone {L K : ℕ} (h : L ≤ K) :
    RamCertificateSetup.parameter L ≤ RamCertificateSetup.parameter K := by
  unfold RamCertificateSetup.parameter
  omega

theorem canonical_polynomial : HasPolynomial canonicalSize := decoded_size
theorem parameter_polynomial : HasPolynomial parameter :=
  compose (f := RamCertificateSetup.parameter) (g := canonicalSize)
    RamResourcePolynomial.parameter canonical_polynomial

theorem stack_polynomial : HasPolynomial stackLength := by
  have h : HasPolynomial (fun S => RamRationalReconstruction.depthBound
      (RamRecoverFeasibleSystem.recoveryBits S) + 1) := by
    unfold RamRationalReconstruction.depthBound RamRecoverFeasibleSystem.recoveryBits RamRecoverFeasibleSystem.capBits
    polynomial_arithmetic
  exact compose (f := fun S => RamRationalReconstruction.depthBound
    (RamRecoverFeasibleSystem.recoveryBits S) + 1) (g := parameter) h parameter_polynomial

theorem front_width_polynomial : HasPolynomial RamFrontEndTotal.wordWidth := by
  apply compose (g := canonicalSize) _ canonical_polynomial
  change HasPolynomial RamDecoder.wordWidth
  unfold RamDecoder.wordWidth
  polynomial_arithmetic

theorem front_cost_polynomial : HasPolynomial RamFrontEndTotal.instructionBound := by
  apply compose (g := canonicalSize) _ canonical_polynomial
  change HasPolynomial RamSolverFrontEnd.instructionBound
  unfold RamSolverFrontEnd.instructionBound RamSolverInitialization.instructionBound RamDecoder.instructionBound
  polynomial_arithmetic

theorem width_polynomial : HasPolynomial wordWidth := by
  unfold wordWidth
  apply add
  · apply add
    · exact add front_width_polynomial (compose RamSolverBranchBounds.width_polynomial parameter_polynomial)
    · exact compose (f := fun S => 32 * (S + 1) ^ 2) (g := parameter)
        (mul (constant 32) (pow (add identity (constant 1)) 2)) parameter_polynomial
  · exact constant 32

theorem cost_polynomial : HasPolynomial instructionBound := by
  unfold instructionBound
  exact add (add (add (add front_cost_polynomial (mul (constant 71) canonical_polynomial))
    (constant 100)) (compose RamSolverBranchBounds.cost_polynomial parameter_polynomial)) (constant 16)

theorem positive (L : ℕ) : 0 < wordWidth L := by unfold wordWidth; omega

theorem front_width (L w : ℕ) (hw : wordWidth L ≤ w) : RamFrontEndTotal.wordWidth L ≤ w := by
  unfold wordWidth at hw
  omega

theorem branch_width (L K w : ℕ) (hK : K ≤ canonicalSize L) (hw : wordWidth L ≤ w) :
    RamSolverBranchBounds.wordWidth (RamCertificateSetup.parameter K) ≤ w := by
  have hp := parameter_monotone hK
  have hb := branch_width_monotone hp
  unfold wordWidth parameter at hw
  omega

theorem stack_depth (L K : ℕ) (hK : K ≤ canonicalSize L) :
    RamRationalReconstruction.depthBound (RamRecoverFeasibleSystem.recoveryBits (RamCertificateSetup.parameter K)) + 1 ≤
      stackLength L := by
  unfold stackLength parameter RamRationalReconstruction.depthBound
  have h := RamRecoveryResourceMonotonicity.recovery_bits (parameter_monotone hK)
  omega

end Lax109476Proofs.RamUniformSolverBounds

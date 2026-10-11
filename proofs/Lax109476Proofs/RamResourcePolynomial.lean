import Lax109476Proofs.RamRecoveryResourceMonotonicity
import Lax109476Proofs.RamDecodedProgram
import Lax109476Proofs.RamCertificateDecision
import Lax109476Proofs.RamCertificateSetup

namespace Lax109476Proofs.RamResourcePolynomial

def HasPolynomial (f : ℕ → ℕ) : Prop := ∃ p : Polynomial ℕ, ∀ n, p.eval n = f n

theorem constant (k : ℕ) : HasPolynomial (fun _ => k) := by
  exact ⟨Polynomial.C k, fun n => by simp⟩

theorem identity : HasPolynomial (fun n => n) := by
  exact ⟨Polynomial.X, fun n => by simp⟩

theorem add {f g : ℕ → ℕ} (hf : HasPolynomial f) (hg : HasPolynomial g) :
    HasPolynomial (fun n => f n + g n) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun n => by simp [hp, hq]⟩

theorem mul {f g : ℕ → ℕ} (hf : HasPolynomial f) (hg : HasPolynomial g) :
    HasPolynomial (fun n => f n * g n) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun n => by simp [hp, hq]⟩

theorem pow {f : ℕ → ℕ} (hf : HasPolynomial f) (k : ℕ) :
    HasPolynomial (fun n => (f n) ^ k) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p ^ k, fun n => by simp [hp]⟩

theorem compose {f g : ℕ → ℕ} (hf : HasPolynomial f) (hg : HasPolynomial g) :
    HasPolynomial (fun n => f (g n)) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p.comp q, fun n => by simp [Polynomial.eval_comp, hp, hq]⟩

attribute [irreducible] HasPolynomial

open Lean Meta Elab Tactic

private partial def polynomialProof (n body : Expr) : MetaM Expr := do
  let body := body.consumeMData.headBeta.consumeMData
  if body == n then return mkConst ``identity
  if !(body.containsFVar n.fvarId!) then return ← mkAppM ``constant #[body]
  let args := body.getAppArgs
  let fn := body.getAppFn.constName?
  if fn == some ``HAdd.hAdd || fn == some ``Nat.add then
    return ← mkAppM ``add #[← polynomialProof n args[args.size - 2]!, ← polynomialProof n args[args.size - 1]!]
  if fn == some ``HMul.hMul || fn == some ``Nat.mul then
    return ← mkAppM ``mul #[← polynomialProof n args[args.size - 2]!, ← polynomialProof n args[args.size - 1]!]
  if fn == some ``HPow.hPow || fn == some ``Nat.pow then
    return ← mkAppM ``pow #[← polynomialProof n args[args.size - 2]!, args[args.size - 1]!]
  let known := if fn == some ``RamStoredFeasibility.wordWidth then some `Lax109476Proofs.RamResourcePolynomial.stored_width
    else if fn == some ``RamStoredFeasibility.instructionBound then some `Lax109476Proofs.RamResourcePolynomial.stored_cost
    else if fn == some ``RamRationalReconstruction.wordWidth then some `Lax109476Proofs.RamResourcePolynomial.reconstruction_width
    else if fn == some ``RamRationalReconstruction.instructionBound then some `Lax109476Proofs.RamResourcePolynomial.reconstruction_cost
    else none
  if let some theoremName := known then
    return ← mkAppM ``compose #[mkConst theoremName, ← polynomialProof n args[args.size - 1]!]
  throwError "Unrecognized polynomial expression: {body}"

elab "polynomial_arithmetic" : tactic => do
  liftMetaTactic fun goal => do
    goal.withContext do
      let target ← goal.getType
      let f := target.getAppArgs[0]!
      withLocalDeclD `n (mkConst ``Nat) fun n => do
        let body := (mkApp f n).headBeta
        let proof ← polynomialProof n body
        goal.assign proof
        return []

theorem decoded_size : HasPolynomial RamDecodedProgram.canonicalBound := by
  unfold RamDecodedProgram.canonicalBound
  polynomial_arithmetic

theorem parameter : HasPolynomial RamCertificateSetup.parameter := by
  unfold RamCertificateSetup.parameter
  polynomial_arithmetic

theorem stored_width : HasPolynomial RamStoredFeasibility.wordWidth := by
  unfold RamStoredFeasibility.wordWidth RamRationalFeasibility.wordWidth
    RamPaddedFeasibility.wordWidth RamIntegerFeasibility.wordWidth RamFeasibilitySetup.wordWidth
    RamFeasibilityScaleBounds.wordWidth RamSearchBounds.wordWidth RamEllipsoidBitBounds.wordWidth
    RamEllipsoidBitBounds.magnitudeExponent RamEllipsoidBitBounds.formExponent
    RamTrajectoryBounds.stateBits RamNormalizedBounds.coefficientBits
    RamIntegerFeasibility.iterationBound RamDecoder.wordWidth
  polynomial_arithmetic

set_option maxRecDepth 6000 in
theorem stored_cost : HasPolynomial RamStoredFeasibility.instructionBound := by
  unfold RamStoredFeasibility.instructionBound RamRationalFeasibility.instructionBound
    RamPaddedFeasibility.instructionBound RamIntegerFeasibility.uniformInstructionBound
    RamFeasibilitySetup.instructionBound RamFeasibilityParameters.instructionBound
    RamSearchBounds.instructionBound RamSearchBounds.stepBound RamSearchBounds.rowBound
    RamTrajectoryBounds.instructionBound RamTrajectoryBounds.stateBits
    RamEllipsoidBitBounds.magnitudeExponent RamEllipsoidBitBounds.formExponent
    RamNormalizedBounds.coefficientBits RamIntegerFeasibility.iterationBound
  dsimp only
  polynomial_arithmetic

theorem reconstruction_width : HasPolynomial RamRationalReconstruction.wordWidth := by
  unfold RamRationalReconstruction.wordWidth RamRationalReconstruction.depthBound
    RamConvergentBounds.wordWidth RamConvergentBounds.exponent RamDecoder.wordWidth
  polynomial_arithmetic

theorem reconstruction_cost : HasPolynomial RamRationalReconstruction.instructionBound := by
  unfold RamRationalReconstruction.instructionBound RamRationalReconstruction.depthBound
    RamConvergentBounds.instructionBound RamConvergentBounds.exponent
  polynomial_arithmetic

theorem recovery_width : HasPolynomial (fun S => RamRecoverFeasibleSystem.wordWidth S S S) := by
  unfold RamRecoverFeasibleSystem.wordWidth RamCoordinateCapBounds.wordWidth
    RamPointRecoveryBounds.wordWidth RamPointRecoveryBounds.querySize
    RamRecoverFeasibleSystem.recoveryBits RamRecoverFeasibleSystem.capBits RamDecoder.wordWidth
  polynomial_arithmetic

theorem recovery_cost : HasPolynomial (fun S => RamRecoverFeasibleSystem.instructionBound S S S) := by
  unfold RamRecoverFeasibleSystem.instructionBound RamPointRecoveryBounds.instructionBound
    RamPointRecoveryBounds.queryCost RamPointRecoveryBounds.querySize
    RamRecoverFeasibleSystem.recoveryBits RamRecoverFeasibleSystem.capBits
  polynomial_arithmetic

theorem decision_width : HasPolynomial (fun S => RamStoredFeasibility.wordWidth
    (RamCertificateDecision.sizeBound S S S)) := by
  apply compose stored_width
  unfold RamCertificateDecision.sizeBound
  polynomial_arithmetic

theorem decision_cost : HasPolynomial (fun S => RamCertificateDecision.instructionBound S S S) := by
  unfold RamCertificateDecision.instructionBound RamCertificateDecision.sizeBound
  polynomial_arithmetic

end Lax109476Proofs.RamResourcePolynomial

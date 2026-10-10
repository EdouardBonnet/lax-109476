import Lax109476Proofs.RamNormalizeQuery
import Lax109476Proofs.RamFeasibilityParameters
import Lax109476Proofs.RamNormalizedBounds
import Lax109476Proofs.RamSolverFrontEnd

namespace Lax109476Proofs.RamFeasibilitySetup

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamMatrixStorage RamEllipsoidStep IntegerEncoding NormalizedFeasibility
open RamNormalizedBounds

def setup : Com := .seq RamFeasibilityParameters.prepareParameters RamNormalizeQuery.normalizeQuery

def wordWidth (S : ℕ) : ℕ := RamFeasibilityScaleBounds.wordWidth S +
  RamDecoder.wordWidth (coefficientBits S) + (S + 1) ^ 2 + S + 2

def instructionBound (S : ℕ) : ℕ := RamFeasibilityParameters.instructionBound S +
  (72 * (coefficientBits S + 1) + 181) * (S * S) +
  (72 * (coefficientBits S + 1) + 189) * S + 78

def Input {m n : ℕ} (P : Program ℤ m n) (S : ℕ) (σ : Env) : Prop :=
  Represents "pad.A" (RamMatrixStorage.flatten (rationalProgram P).A) σ ∧
    Represents "pad.b" (List.ofFn (rationalProgram P).b) σ ∧
    Extents "search.rows" ((m + n) * n) σ ∧ Extents "search.rhs" (m + n) σ ∧
    Extents "ell.center" n σ ∧ Extents "ell.shape" (n * n) σ ∧ Workspace n σ ∧
    Extents "ell.normal" n σ ∧ σ.vars "query.m" = m ∧ σ.vars "query.n" = n ∧ σ.vars "query.bits" = S

theorem setup_spec (m n S w : ℕ) (P : Program ℤ m n) (hdim : m + n ≤ S)
    (hA : ∀ i j, (P.A i j).natAbs ≤ 2 ^ (2 * S))
    (hb : ∀ i, (P.b i).natAbs ≤ 2 ^ (2 * S)) (hw : wordWidth S ≤ w) :
    Spec (2 ^ w) (Input P S) setup
      (fun _ τ => RamSearchBounds.Input
        (normalizedMatrix P (outerScale n (IntegerCertificates.coordinateCap m n (2 ^ (2 * S)))))
        (normalizedBound P (1 / (precisionDenominator m n (2 ^ (2 * S)) : ℚ)))
        (EllipsoidSequence.thresholdSteps n (ballExponent m n (2 ^ (2 * S))) + 1) τ)
      (instructionBound S) := by
  let H := 2 ^ (2 * S)
  let M := 2 ^ coefficientBits S
  let D := precisionDenominator m n H
  let R := outerScale n (IntegerCertificates.coordinateCap m n H)
  let N := EllipsoidSequence.thresholdSteps n (ballExponent m n H) + 1
  have hwParams : RamFeasibilityScaleBounds.wordWidth S ≤ w := by unfold wordWidth at hw; omega
  have hwNormal : RamDecoder.wordWidth (coefficientBits S) ≤ w := by unfold wordWidth at hw; omega
  have hM : 1 ≤ M := Nat.one_le_pow _ _ (by decide)
  have hguard := RamSolverFrontEnd.clearing_word_guard (coefficientBits S) w hwNormal
  have hHM : H ≤ M := Nat.pow_le_pow_right (by decide) (by unfold coefficientBits; omega)
  have hsize := IterationBudget.ballExponent_polynomial m n S hdim
  have hball : ballDenominator m n H ≤ M := (Nat.lt_size_self _).le.trans
    (Nat.pow_le_pow_right (by decide) (by change ballExponent m n H ≤ coefficientBits S; dsimp only [H]; unfold coefficientBits; omega))
  have hfactors := factors_le_ball m n H
  have hR : R ≤ M := hfactors.2.trans hball
  have hD : 0 < D := precisionDenominator_pos _ _ _
  have hDM : D ≤ M := hfactors.1.trans hball
  have hn : n ≤ S := by omega
  have hprod : (m + n) * n ≤ S * S := Nat.mul_le_mul hdim hn
  have hwD : S * S + S + 1 ≤ w := by unfold wordWidth at hw; nlinarith
  have hwidth := (Nat.lt_two_pow_self (n := S * S + S + 1)).trans_le
    (Nat.pow_le_pow_right (by decide) hwD)
  have hdims : (m + n) * n + m + n + 1 < 2 ^ w := by omega
  rintro σ ⟨hσA, hσb, hσrows, hσrhs, hσcenter, hσshape, hσworkspace, hσnormal, hσm, hσn, hσbits⟩
  obtain ⟨τ, hr₁, hparams, hτC, hτbits, harr⟩ :=
    RamFeasibilityParameters.prepareParameters_spec m n S w hdim hwParams σ ⟨hσm, hσn, hσbits⟩
  obtain ⟨hτD, hτR, hτE, hτN, hτm, hτn, hτH⟩ := hparams
  have hτinput : RamNormalizeQuery.Input P R D N τ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hτm, hτn, hτR, hτD, hτN⟩
    · simpa only [Represents, harr] using hσA
    · simpa only [Represents, harr] using hσb
    · simpa only [Extents, harr] using hσrows
    · simpa only [Extents, harr] using hσrhs
    · simpa only [Extents, harr] using hσcenter
    · simpa only [Extents, harr] using hσshape
    · exact RamAdvanceState.workspace_of_run hr₁ n hσworkspace
    · simpa only [Extents, harr] using hσnormal
  obtain ⟨υ, hr₂, hυ⟩ := RamNormalizeQuery.normalizeQuery_spec (2 ^ w) M m n R D N P
    hM hR hD hDM hdims hguard (fun i j => (hA i j).trans hHM) (fun i => (hb i).trans hHM) τ hτinput
  have hmulA := Nat.mul_le_mul_left (72 * (coefficientBits S + 1) + 181) hprod
  have hmulb := Nat.mul_le_mul_left (72 * (coefficientBits S + 1) + 189) hdim
  refine ⟨υ, (hr₁.seq hr₂).mono ?_, hυ⟩
  simp only [instructionBound, M, Nat.size_pow]
  omega

end Lax109476Proofs.RamFeasibilitySetup

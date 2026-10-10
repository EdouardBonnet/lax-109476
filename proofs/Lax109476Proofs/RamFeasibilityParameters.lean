import Lax109476Proofs.RamCoordinateCapBounds
import Lax109476Proofs.RamFeasibilityScaleBounds

namespace Lax109476Proofs.RamFeasibilityParameters

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamCoordinateCap RamFeasibilityScales IntegerCertificates

def prepareParameters : Com := .seq
  (.assign "cap.H" (.shiftl (.lit 1) (.mul (.lit 2) (.var "query.bits"))))
  (.seq prepareCap prepareScales)

def instructionBound (S : ℕ) : ℕ := 1536 * (S + 1) ^ 2 + 48 * S + 158

theorem prepareParameters_spec (m n S w : ℕ) (hdim : m + n ≤ S)
    (hw : RamFeasibilityScaleBounds.wordWidth S ≤ w) :
    Spec (2 ^ w) (fun σ => σ.vars "query.m" = m ∧ σ.vars "query.n" = n ∧ σ.vars "query.bits" = S)
      prepareParameters
      (fun σ τ => Output m n (2 ^ (2 * S)) τ ∧
        τ.vars "cap.value" = coordinateCap m n (2 ^ (2 * S)) ∧
        τ.vars "query.bits" = S ∧ τ.arrs = σ.arrs)
      (instructionBound S) := by
  have hsq : (S + 1) ^ 2 ≤ (S + 1) ^ 4 :=
    pow_le_pow_right₀ (by omega : 1 ≤ S + 1) (by decide : 2 ≤ 4)
  have hSsq : S ≤ (S + 1) ^ 2 := by nlinarith
  have hwcap : RamCoordinateCapBounds.wordWidth S ≤ w := by
    dsimp [RamCoordinateCapBounds.wordWidth, RamFeasibilityScaleBounds.wordWidth] at hw ⊢
    nlinarith
  have hmag := RamFeasibilityScaleBounds.magnitude_fits m n S w hdim hw
  have hH : 2 ^ (2 * S) < 2 ^ w := by dsimp [RamFeasibilityScales.magnitude] at hmag; omega
  have he : 2 * S < 2 ^ w := (Nat.lt_two_pow_self (n := 2 * S)).trans hH
  have h1 : 1 < 2 ^ w := by have h := Nat.one_le_pow (2 * S) 2 (by decide); omega
  have hw2 : 2 ≤ w := by
    have hp : 1 ≤ (S + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    dsimp [RamFeasibilityScaleBounds.wordWidth] at hw
    omega
  have h4 : 4 ≤ 2 ^ w := by simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hw2
  have h2 : 2 < 2 ^ w := by omega
  have hSB : S < 2 ^ w := by omega
  intro σ ⟨hσm, hσn, hσbits⟩
  have hr₁ : Run (2 ^ w)
      (.assign "cap.H" (.shiftl (.lit 1) (.mul (.lit 2) (.var "query.bits")))) σ
      (σ.setVar "cap.H" (2 ^ (2 * S))) 6 := by
    apply Run.assign
    simpa only [hσbits, Bop.apply_mul, Bop.apply_shiftl, one_mul] using
      evalB_bin (evalB_lit h1)
        (evalB_bin (evalB_lit h2) (evalB_var (B := 2 ^ w) (σ := σ) (x := "query.bits")
          (hσbits ▸ hSB)) (show Bop.mul.apply 2 (σ.vars "query.bits") < 2 ^ w by simpa [hσbits] using he))
        (show Bop.shiftl.apply 1 (Bop.mul.apply 2 (σ.vars "query.bits")) < 2 ^ w by simpa [hσbits] using hH)
  obtain ⟨τ, hr₂, hτC, hτH, hτm, hτn⟩ :=
    RamCoordinateCapBounds.prepareCap_bounded_spec m n S w hdim hwcap (σ.setVar "cap.H" (2 ^ (2 * S)))
      ⟨by simpa using hσm, by simpa using hσn, by simp⟩
  obtain ⟨υ, hr₃, hυ⟩ := RamFeasibilityScaleBounds.prepareScales_bounded_spec m n S w hdim hw
    τ ⟨hτm, hτn, hτH, hτC⟩
  have hr := hr₁.seq (hr₂.seq hr₃)
  refine ⟨υ, hr.mono ?_, hυ, (hr₃.frame_var "cap.value" (by decide)).trans hτC,
    (hr.frame_var "query.bits" (by decide)).trans hσbits, ?_⟩
  · dsimp [instructionBound]
    omega
  · funext a
    exact hr.frame_arr a (by simp [prepareParameters, Com.warrs, prepareCap, prepareScales,
      RamNaturalPower.factorial, RamNaturalPower.factorialStep, RamNaturalPower.power,
      RamNaturalPower.powerStep, RamBitLength.bitLength, RamBitLength.bitLengthLoop, RamBitLength.bitLengthStep])

end Lax109476Proofs.RamFeasibilityParameters

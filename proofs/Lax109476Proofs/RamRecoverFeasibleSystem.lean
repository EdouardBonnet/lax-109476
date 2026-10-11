import Lax109476Proofs.RamEquationBuilder
import Lax109476Proofs.StandardPointCapComparison
import Lax109476Proofs.RamCoordinateCapBounds

namespace Lax109476Proofs.RamRecoverFeasibleSystem

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEquationData RamEllipsoidStep RationalArithmeticBounds
open IntegerEncoding IntegerPointRecovery

def capBits (S : ℕ) : ℕ := 32 * (S + 1) ^ 2
def recoveryBits (S : ℕ) : ℕ := 4 * capBits S + 2 * S + 2

def wordWidth (m n S : ℕ) : ℕ :=
  RamPointRecoveryBounds.wordWidth (m + m) (n + m) (recoveryBits S) +
    RamCoordinateCapBounds.wordWidth S + (m + m) * (n + m) + m + m + n + 4 + S + 8

def instructionBound (m n S : ℕ) : ℕ :=
  118 * ((m + m) * (n + m)) + 91 * (m + m) + 33 * (n + m) + 48 * S + 192 +
    RamPointRecoveryBounds.instructionBound (m + m) (n + m) (recoveryBits S) (capBits S)

def prepareCap : Com := .seq (.assign "query.m" (.var "system.m"))
  (.seq (.assign "query.n" (.var "system.n")) (.assign "cap.H" (.var "system.H")))

def recover : Com := .seq RamEquationBuilder.buildSystem (.seq prepareCap
  (.seq RamCoordinateCap.prepareCap
    (.seq (.assign "minimum.bound" (.var "cap.value")) RamPointInitialization.recover)))

def Input {m n : ℕ} (P : Program ℤ m n) (S N : ℕ) (σ : Env) : Prop :=
  Data P σ ∧ σ.vars "system.H" = 2 ^ (2 * S) ∧
    Extents "point.A" ((m + m) * (n + m)) σ ∧ Extents "point.b" (m + m) σ ∧
    Extents "point.x" (n + m) σ ∧ RamRecoveryThreshold.Workspace (m + m) (n + m) σ ∧
    (σ.arrs "cf.stack").length = N

theorem prepareCap_spec (B m n H : ℕ) (hm : m < B) (hn : n < B) (hH : H < B) :
    Spec B (fun σ => σ.vars "system.m" = m ∧ σ.vars "system.n" = n ∧ σ.vars "system.H" = H)
      prepareCap (fun _ τ => τ.vars "query.m" = m ∧ τ.vars "query.n" = n ∧ τ.vars "cap.H" = H) 6 := by
  rintro σ ⟨hσm, hσn, hσH⟩
  run_vcg
  all_goals simp_all

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
theorem recover_spec (m n S N w : ℕ) (P : Program ℤ m n)
    (hdim : m + n ≤ S) (hw : wordWidth m n S ≤ w)
    (hN : RamRationalReconstruction.depthBound (recoveryBits S) + 1 ≤ N)
    (hA : ∀ i j, (P.A i j).natAbs ≤ 2 ^ (2 * S)) (hb : ∀ i, (P.b i).natAbs ≤ 2 ^ (2 * S))
    (hf : ∃ x, PrimalFeasible (rationalProgram P) x) :
    Spec (2 ^ w) (Input P S N) recover
      (fun _ τ => ∃ z : Fin (n + m) → ℚ,
        RamRecoveryThreshold.Persistent (RamStandardPointRecovery.program (slackMatrix P) P.b) z (n + m) τ ∧
          PrimalFeasible (rationalProgram P) (fun j => z (Fin.castAdd m j)) ∧
            ∀ j, Height (z j) (IntegerCertificates.coordinateCap m n (2 ^ (2 * S))))
      (instructionBound m n S) := by
  let H := 2 ^ (2 * S)
  let D := IntegerCertificates.coordinateCap m n H
  let R := recoveryBits S
  let E := RamStandardPointRecovery.program (slackMatrix P) P.b
  have hH1 : 1 ≤ H := Nat.one_le_pow _ _ (by decide)
  have hwCap : RamCoordinateCapBounds.wordWidth S ≤ w := by unfold wordWidth at hw; omega
  have hwPoint : RamPointRecoveryBounds.wordWidth (m + m) (n + m) R ≤ w := by
    dsimp only [R]; unfold wordWidth at hw; omega
  have hguard : (m + m) * (n + m) + m + m + n + 4 < 2 ^ w :=
    (by unfold wordWidth at hw; omega : (m + m) * (n + m) + m + m + n + 4 ≤ w).trans_lt
      (Nat.lt_two_pow_self (n := w))
  have hmag := RamCoordinateCapBounds.magnitude_fits m n S w hdim hwCap
  have hHB : H < 2 ^ w := by dsimp only [RamCoordinateCap.magnitude] at hmag; dsimp only [H]; omega
  have hmB : m < 2 ^ w := by omega
  have hnB : n < 2 ^ w := by omega
  have hDbits : D.size ≤ capBits S := RationalSizeBounds.certificate_cap_size
    (2 * (m + n) + 2) S (by omega)
  have hR : 4 * capBits S + 2 ≤ R := by dsimp only [R, recoveryBits]; omega
  have hHR : H ≤ 2 ^ R := Nat.pow_le_pow_right (by decide) (by dsimp only [R, recoveryBits]; omega)
  have hslack : ∀ i j, (slackMatrix P i j).natAbs ≤ H := by
    intro i j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa [slackMatrix] using hA i j
    · simp only [slackMatrix, Fin.addCases_right]
      split_ifs <;> norm_num <;> omega
  obtain ⟨x₀, hx₀⟩ := hf
  have hfeas : ∃ x, LexicographicSupport.Feasible ((slackMatrix P).map (fun z => (z : ℚ)))
      (fun i => (P.b i : ℚ)) x := ⟨withSlacks P x₀, withSlacks_feasible P x₀ hx₀⟩
  rintro σ ⟨hσData, hσH, hσA, hσb, hσx, hσW, hσN⟩
  obtain ⟨τ, hr₁, hτData, hτE⟩ := RamEquationBuilder.buildSystem_spec (2 ^ w) H m n P hH1 hHB hguard hA hb σ
    ⟨hσData, hσA, hσb⟩
  have hτH := (hr₁.frame_var "system.H" (by decide)).trans hσH
  obtain ⟨υ, hr₂, hυm, hυn, hυH⟩ := prepareCap_spec (2 ^ w) m n H hmB hnB hHB τ ⟨hτData.2.2.1, hτData.2.2.2, hτH⟩
  obtain ⟨ρ, hr₃, hρD, _, _, _⟩ := RamCoordinateCapBounds.prepareCap_bounded_spec m n S w hdim hwCap υ ⟨hυm, hυn, hυH⟩
  have hDB : D < 2 ^ w := by dsimp only [RamCoordinateCap.magnitude] at hmag; dsimp only [D, H]; omega
  have hr₄ : Run (2 ^ w) (.assign "minimum.bound" (.var "cap.value")) ρ (ρ.setVar "minimum.bound" D) 2 :=
    Run.assign (by simpa only [hρD] using (evalB_var (B := 2 ^ w) (σ := ρ) (x := "cap.value") (hρD ▸ hDB)))
  let ξ := ρ.setVar "minimum.bound" D
  have hrPrepare := hr₂.seq (hr₃.seq hr₄)
  have hξE : RamPointInitialization.Base E ξ := by
    rcases hτE with ⟨hEA, hEb, hEm, hEn⟩
    exact ⟨RamReadBody.represents_frame _ _ hEA hrPrepare (by intro s hs; change _ ∉ ([] : List String); simp),
      RamReadBody.represents_frame _ _ hEb hrPrepare (by intro s hs; change _ ∉ ([] : List String); simp),
      (hrPrepare.frame_var "point.m" (by decide)).trans hEm, (hrPrepare.frame_var "point.n" (by decide)).trans hEn⟩
  have hrPre := hr₁.seq hrPrepare
  have hξW := RamRecoveryThreshold.workspace_frame hrPre _ _ hσW
  have hξx := RamAdvanceState.extents_of_run hrPre "point.x" (n + m) hσx
  have hξN : (ξ.arrs "cf.stack").length = N := by rw [hrPre.frame_arr _ (by decide)]; exact hσN
  obtain ⟨ζ, hr₅, z, hζ, hz, hzHeight⟩ := RamStandardPointRecovery.recover_with_cap_spec m (n + m) H R (capBits S) N w D
    (slackMatrix P) P.b hslack hb hHR (StandardPointCapComparison.slack_cap_le m n H)
    hDbits hR hN hwPoint hfeas ξ ⟨hξE, hξW, hξx, by simp [ξ], hξN⟩
  refine ⟨ζ, (hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq hr₅)))).mono ?_, z, hζ,
    slack_point_feasible P z hz, fun j => height_mono _ (hzHeight j) (StandardPointCapComparison.slack_cap_le m n H)⟩
  dsimp only [instructionBound, R]
  omega

end Lax109476Proofs.RamRecoverFeasibleSystem

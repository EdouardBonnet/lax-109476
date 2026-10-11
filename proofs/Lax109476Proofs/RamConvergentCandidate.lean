import Lax109476Proofs.RamConvergentBounds
import Lax109476Proofs.RamReconstructionCandidate

namespace Lax109476Proofs.RamConvergentCandidate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RamRationalScalars RamScalarFrame

def testCandidate : Com := .seq (readLeft "recon.hi")
  (.seq (.assign "cf.depth" (.var "recon.i"))
    (.seq RamContinuedFractionConvergent.convergent RamReconstructionCandidate.check))

theorem testCandidate_spec (S K N j w D : ℕ) (l u : ℚ) (hu0 : 0 ≤ u)
    (hl : Height l (2 ^ S)) (hu : Height u (2 ^ S)) (hj : j ≤ K) (hN : K + 1 ≤ N)
    (hw : RamConvergentBounds.wordWidth S K ≤ w) (hDB : D < 2 ^ w) :
    Spec (2 ^ w) (fun σ => Value "recon.lo" l σ ∧ Value "recon.hi" u σ ∧
      σ.vars "recon.bound" = D ∧ σ.vars "recon.i" = j ∧ (σ.arrs "cf.stack").length = N)
      testCandidate
      (fun _ τ => τ.vars "recon.accept" =
        (if (RationalReconstruction.convergent u j).den ≤ D ∧ l ≤ RationalReconstruction.convergent u j ∧
          RationalReconstruction.convergent u j ≤ u then 1 else 0) ∧
        FractionOutput (RationalReconstruction.convergent u j) τ)
      (RamConvergentBounds.instructionBound S K + 132) := by
  let E := RamConvergentBounds.exponent S K
  let R := 2 ^ E
  have hSE : S ≤ E := by dsimp [E, RamConvergentBounds.exponent]; nlinarith
  have hMR : 2 ^ S ≤ R := Nat.pow_le_pow_right (by decide) hSE
  have hwD : RamDecoder.wordWidth E ≤ w := by dsimp only [E]; unfold RamConvergentBounds.wordWidth at hw; omega
  have hguard := RamSolverFrontEnd.clearing_word_guard E w hwD
  have hRB : R < 2 ^ w := by dsimp only [R]; apply Nat.pow_lt_pow_right (by decide); unfold RamDecoder.wordWidth at hwD; omega
  have h1 : 1 < 2 ^ w := by omega
  have hjB : j < 2 ^ w := (by unfold RamConvergentBounds.wordWidth at hw; omega : j ≤ w).trans_lt (Nat.lt_two_pow_self (n := w))
  have hcr : Height (RationalReconstruction.convergent u j) R :=
    height_mono _ (ContinuedFractionBounds.convergent_height u (2 ^ S) j hu0 hu)
      ((Nat.pow_le_pow_right (by positivity) (show j + 1 ≤ j + 2 by omega)).trans
        (RamConvergentBounds.intermediate_bound S K j hj))
  rintro σ ⟨hσl, hσu, hσD, hσj, hσN⟩
  obtain ⟨τ, hr₁, hτu⟩ := readLeft_spec (2 ^ w) "recon.hi" u h1
    ((hu.1.trans hMR).trans_lt hRB) ((hu.2.trans hMR).trans_lt hRB)
    (by simp [RamCopy.Disjoint, RamCopy.suffixes]) σ hσu
  have hτj : τ.vars "recon.i" = j := (hr₁.frame_var _ (by decide)).trans hσj
  have hr₂ : Run (2 ^ w) (.assign "cf.depth" (.var "recon.i")) τ (τ.setVar "cf.depth" j) 2 :=
    Run.assign (by simpa only [hτj] using evalB_var (B := 2 ^ w) (σ := τ) (x := "recon.i") (hτj ▸ hjB))
  have hleft : LeftValue u (τ.setVar "cf.depth" j) := by simpa [LeftValue, vars_setVar] using hτu
  have hlen : ((τ.setVar "cf.depth" j).arrs "cf.stack").length = N := by
    rw [arrs_setVar, hr₁.frame_arr _ (by decide)]; exact hσN
  obtain ⟨υ, hr₃, hυ⟩ := RamConvergentBounds.convergent_spec S K N j w u hu0 hu hj hN hw
    (τ.setVar "cf.depth" j) ⟨hlen, hleft, by simp⟩
  have hrPre := hr₁.seq (hr₂.seq hr₃)
  have hυl := value_frame hrPre "recon.lo" l hσl (by decide) (by decide) (by decide)
  have hυu := value_frame hrPre "recon.hi" u hσu (by decide) (by decide) (by decide)
  have hυD := (hrPre.frame_var _ (by decide)).trans hσD
  obtain ⟨ρ, hr₄, hρ⟩ := RamReconstructionCandidate.check_spec (2 ^ w) R D l u
    (RationalReconstruction.convergent u j) hguard hDB (height_mono _ hl hMR) (height_mono _ hu hMR)
    hcr υ ⟨hυl, hυu, hυ, hυD⟩
  exact ⟨ρ, (hr₁.seq (hr₂.seq (hr₃.seq hr₄))).mono (by omega), hρ⟩

end Lax109476Proofs.RamConvergentCandidate

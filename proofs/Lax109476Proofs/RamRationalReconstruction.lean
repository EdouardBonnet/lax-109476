import Lax109476Proofs.RamReconstructionSearch
import Lax109476Proofs.RamBitLength

namespace Lax109476Proofs.RamRationalReconstruction

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RamRationalScalars RamScalarFrame

def prepare : Com := .seq (.assign "bits.v" (.var "recon.hi.d"))
  (.seq RamBitLength.bitLength
    (.assign "recon.limit" (.add (.mul (.var "bits.k") (.lit 2)) (.lit 1))))

def depthBound (S : ℕ) : ℕ := 2 * (S + 1) + 1

def wordWidth (S : ℕ) : ℕ := RamConvergentBounds.wordWidth S (depthBound S)

def instructionBound (S : ℕ) : ℕ :=
  (RamConvergentBounds.instructionBound S (depthBound S) + 156) * depthBound S + 12 * (S + 1) + 22

theorem prepare_spec (B : ℕ) (u : ℚ) (h2 : 2 < B) (hd : u.den < B) (hK : 2 * u.den.size + 1 < B) :
    Spec B (Value "recon.hi" u) prepare
      (fun _ τ => τ.vars "recon.limit" = 2 * u.den.size + 1) (12 * u.den.size + 14) := by
  have hbits := RationalSizeBounds.size_le_self u.den
  have hb := RamBitLength.bitLength_spec B u.den h2 hd
  rintro σ ⟨hval, hn, hσd, hs⟩
  run_vcg [hb]
  all_goals simp_all [mul_comm]
  all_goals omega

def reconstruct : Com := .seq prepare RamReconstructionSearch.search

/-- Exact rational reconstruction scans the logarithmically many continued-
fraction convergents using a fixed program, and returns the first candidate
meeting the interval and denominator checks. -/
theorem reconstruct_spec (S N w D : ℕ) (l u : ℚ) (hu0 : 0 ≤ u)
    (hl : Height l (2 ^ S)) (hu : Height u (2 ^ S)) (hN : depthBound S + 1 ≤ N)
    (hw : wordWidth S ≤ w) (hDB : D < 2 ^ w) :
    Spec (2 ^ w) (fun σ => Value "recon.lo" l σ ∧ Value "recon.hi" u σ ∧
      σ.vars "recon.bound" = D ∧ (σ.arrs "cf.stack").length = N)
      reconstruct (fun _ τ => RamReconstructionRecord.Output (RationalReconstruction.reconstruct l u D) τ)
      (instructionBound S) := by
  let K := 2 * u.den.size + 1
  have hsize : u.den.size ≤ S + 1 := by have := Nat.size_le_size hu.2; rwa [Nat.size_pow] at this
  have hK : K ≤ depthBound S := by dsimp only [K, depthBound]; omega
  have hwK : RamConvergentBounds.wordWidth S K ≤ w := by
    have hm : RamConvergentBounds.wordWidth S K ≤ RamConvergentBounds.wordWidth S (depthBound S) := by
      unfold RamConvergentBounds.wordWidth RamConvergentBounds.exponent RamDecoder.wordWidth
      gcongr
    exact hm.trans hw
  have hKB : K < 2 ^ w := (by unfold wordWidth RamConvergentBounds.wordWidth at hw; omega : K ≤ w).trans_lt
    (Nat.lt_two_pow_self (n := w))
  have h2 : 2 < 2 ^ w := by
    have hp := Nat.pow_le_pow_right (n := 2) (by decide) (show 2 ≤ w by
      unfold wordWidth RamConvergentBounds.wordWidth at hw; omega)
    norm_num at hp; omega
  have hHB : 2 ^ S < 2 ^ w := Nat.pow_lt_pow_right (by decide) (by
    unfold wordWidth RamConvergentBounds.wordWidth RamConvergentBounds.exponent RamDecoder.wordWidth at hw
    unfold depthBound at hw
    nlinarith)
  rintro σ ⟨hσl, hσu, hσD, hσN⟩
  obtain ⟨τ, hr₁, hτK⟩ := prepare_spec (2 ^ w) u h2 (hu.2.trans_lt hHB) hKB σ hσu
  have hτl := value_frame hr₁ "recon.lo" l hσl (by decide) (by decide) (by decide)
  have hτu := value_frame hr₁ "recon.hi" u hσu (by decide) (by decide) (by decide)
  have hτD := (hr₁.frame_var _ (by decide)).trans hσD
  have hτN : (τ.arrs "cf.stack").length = N := by rw [hr₁.frame_arr _ (by decide)]; exact hσN
  obtain ⟨υ, hr₂, hυ⟩ := RamReconstructionSearch.search_spec S K N w D l u hu0 hl hu
    (by omega) hwK hDB τ ⟨hτl, hτu, hτD, hτK, hτN⟩
  have hcost : (RamConvergentBounds.instructionBound S K + 156) * K ≤
      (RamConvergentBounds.instructionBound S (depthBound S) + 156) * depthBound S := by
    unfold RamConvergentBounds.instructionBound RamConvergentBounds.exponent
    gcongr
  refine ⟨υ, (hr₁.seq hr₂).mono (by unfold instructionBound; omega), ?_⟩
  simpa only [K, ReconstructionPrefix.scan_complete] using hυ

end Lax109476Proofs.RamRationalReconstruction

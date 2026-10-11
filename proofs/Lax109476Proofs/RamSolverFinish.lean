import Lax109476Proofs.RamUniformSolverBounds

namespace Lax109476Proofs.RamSolverFinish

open Lax109476.LinearProgram Lax109476.RationalEncoding Lax109476.RationalCertificates
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep IntegerEncoding RamSolverWorkspace EncodingSize

def Input {m n : ℕ} (P : Program ℚ m n) (N : ℕ) (σ : Env) : Prop :=
  RamSolverFrontEnd.Output P σ ∧ Extents "source.A" (m * n) σ ∧
  Extents "source.b" m σ ∧ Extents "source.c" n σ ∧ All m n N σ

def Result {m n : ℕ} (P : Program ℚ m n) (σ τ : Env) : Prop :=
  ∃ certificate : Certificate m n,
    τ.out = σ.out ++ encodeCertificate certificate ∧ IsValidCertificate P certificate

def instructionBound (L : ℕ) : ℕ := 71 * L + 100 +
  RamSolverBranchBounds.instructionBound (RamCertificateSetup.parameter L)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
theorem save_noWrite : RamCertificateSetup.save.NoWrite := by decide

theorem finish_spec (m n N w : ℕ) (P : Program ℚ m n)
    (hw : RamSolverBranchBounds.wordWidth (RamCertificateSetup.parameter (bitSize (encodeProgram P))) ≤ w)
    (hN : RamRationalReconstruction.depthBound (RamRecoverFeasibleSystem.recoveryBits
      (RamCertificateSetup.parameter (bitSize (encodeProgram P)))) + 1 ≤ N) :
    Spec (2 ^ w) (Input P N) (.seq RamCertificateSetup.save RamExactSolverProgram.chooseCertificate)
      (Result P) (instructionBound (bitSize (encodeProgram P))) := by
  let L := bitSize (encodeProgram P)
  let S := RamCertificateSetup.parameter L
  let H := 2 ^ (2 * S)
  have hcells := RamSolverInitialization.cells_bound P
  have hdim : m + n ≤ L := by dsimp only [L]; omega
  have hAraw := (integerProgram_bounds P).1
  have hbraw := (integerProgram_bounds P).2.1
  have hcraw := (integerProgram_bounds P).2.2
  have hLS : L ≤ S := by dsimp only [S, RamCertificateSetup.parameter]; omega
  have hp : 2 ^ (2 * L) ≤ H := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 2 hLS)
  have hA : ∀ i j, ((integerProgram P).A i j).natAbs ≤ H := fun i j => (hAraw i j).trans hp
  have hb : ∀ i, ((integerProgram P).b i).natAbs ≤ H := fun i => (hbraw i).trans hp
  have hc : ∀ j, ((integerProgram P).c j).natAbs ≤ H := fun j => (hcraw j).trans hp
  have hH : 1 ≤ H := Nat.one_le_pow _ _ (by decide)
  have hguards := RamSolverBranchBounds.guards S w hw
  have hSaveGuard : m * n + 2 * S + L + m + n + 8 < 2 ^ w := by
    have hL2 : 2 * L ≤ S := by dsimp only [S, RamCertificateSetup.parameter]; omega
    have hS1 : 1 ≤ S := by dsimp only [S, RamCertificateSetup.parameter]; omega
    have hSS : S ≤ S * S := Nat.le_mul_of_pos_right S (by omega)
    dsimp only [L] at *
    omega
  rintro σ ⟨hσFront, hσA, hσb, hσc, hσAll⟩
  rcases hσFront with ⟨hσP, hσInt, hσvalid, hσbits, hσden, hσinp⟩
  have hσSave : RamCertificateSetup.Input (integerProgram P) L σ :=
    ⟨hσInt.1, hσInt.2.1, hσInt.2.2, hσP.2.2.2.1, hσP.2.2.2.2.1,
      hσP.2.2.2.2.2, hσbits, hσA, hσb, hσc⟩
  obtain ⟨τ, hrSave, hτSource, hτSaved, hτH⟩ := RamCertificateSetup.save_spec (2 ^ w) H m n L
    (integerProgram P) hH hguards.1 hSaveGuard hguards.1 hA hb hc σ hσSave
  have hτContext := RamSolverOriginalContext.of_source (integerProgram P) τ hτSource hτSaved hτH
  have hτAll := all_of_run hrSave m n N hσAll
  obtain ⟨υ, hrChoose, cert, hυout, hvalid⟩ := RamSolverChooseCertificate.choose_spec m n L N w
    (integerProgram P) hdim hw hN hA hb hc τ ⟨hτSource, hτContext, hτAll⟩
  have hvalidOriginal : IsValidCertificate P cert := by
    have hh := hvalid
    rw [integerProgram_eq_scaled] at hh
    exact (certificate_scaled P (programDenominator P) (by
      exact_mod_cast RationalSizeBounds.commonDenominator_pos (programData P)) cert).mp hh
  refine ⟨υ, (hrSave.seq hrChoose).mono ?_, cert, ?_, hvalidOriginal⟩
  · have hcost := Nat.mul_le_mul_left 71 hcells
    dsimp only [instructionBound, L]
    omega
  · simpa only [hrSave.out_eq save_noWrite] using hυout

end Lax109476Proofs.RamSolverFinish

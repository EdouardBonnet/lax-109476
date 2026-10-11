import Lax109476Proofs.RamRecoverFeasibleSystem
import Lax109476Proofs.RamWriteCertificate

namespace Lax109476Proofs.RamRecoverCertificate

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RationalArithmeticBounds IntegerEncoding

def recover (tag : ℕ) : Com := .seq RamRecoverFeasibleSystem.recover (RamWriteCertificate.emit tag)

set_option maxRecDepth 12000 in
theorem recovery_no_write : RamRecoverFeasibleSystem.recover.NoWrite := by decide

set_option maxRecDepth 12000 in
theorem recovery_preserves_dimension : "system.n" ∉ RamRecoverFeasibleSystem.recover.wvars := by decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
theorem recover_spec (m n r s S N w tag : ℕ) (P : Program ℤ m n) (F : Program ℤ r s)
    (makeCertificate : (Fin (s + r) → ℚ) → Certificate m n)
    (hdim : r + s ≤ S) (hw : RamRecoverFeasibleSystem.wordWidth r s S ≤ w)
    (hN : RamRationalReconstruction.depthBound (RamRecoverFeasibleSystem.recoveryBits S) + 1 ≤ N)
    (hA : ∀ i j, (F.A i j).natAbs ≤ 2 ^ (2 * S)) (hb : ∀ i, (F.b i).natAbs ≤ 2 ^ (2 * S))
    (hf : ∃ x, PrimalFeasible (rationalProgram F) x)
    (hvalid : ∀ z, PrimalFeasible (rationalProgram F) (fun j => z (Fin.castAdd r j)) →
      IsValidCertificate (rationalProgram P) (makeCertificate z))
    (hemit : ∀ z, (∀ j, Height (z j) (IntegerCertificates.coordinateCap r s (2 ^ (2 * S)))) → Spec (2 ^ w)
      (fun σ => Represents "point.x" (List.ofFn z) σ ∧ σ.vars "system.n" = s)
      (RamWriteCertificate.emit tag)
      (fun σ τ => τ.out = σ.out ++ encodeCertificate (makeCertificate z)) (35 * s + 10)) :
    Spec (2 ^ w) (RamRecoverFeasibleSystem.Input F S N) (recover tag)
      (fun σ τ => ∃ certificate : Certificate m n,
        τ.out = σ.out ++ encodeCertificate certificate ∧ IsValidCertificate (rationalProgram P) certificate)
      (RamRecoverFeasibleSystem.instructionBound r s S + 35 * s + 10) := by
  intro σ hσ
  obtain ⟨τ, hr₁, z, hτState, hz, hzHeight⟩ := RamRecoverFeasibleSystem.recover_spec r s S N w F
    hdim hw hN hA hb hf σ hσ
  have hτx : Represents "point.x" (List.ofFn z) τ := hτState.1.2.2.1
  have hτn : τ.vars "system.n" = s := (hr₁.frame_var _ recovery_preserves_dimension).trans hσ.1.2.2.2
  obtain ⟨υ, hr₂, hυout⟩ := hemit z hzHeight τ ⟨hτx, hτn⟩
  refine ⟨υ, (hr₁.seq hr₂).mono (by omega), makeCertificate z, ?_, hvalid z hz⟩
  simpa only [hr₁.out_eq recovery_no_write] using hυout

theorem emission_guards (r s S w : ℕ) (hdim : r + s ≤ S)
    (hw : RamRecoverFeasibleSystem.wordWidth r s S ≤ w) :
    2 < 2 ^ w ∧ s < 2 ^ w ∧ IntegerCertificates.coordinateCap r s (2 ^ (2 * S)) < 2 ^ w := by
  have hwCap : RamCoordinateCapBounds.wordWidth S ≤ w := by
    unfold RamRecoverFeasibleSystem.wordWidth at hw; omega
  have hmag := RamCoordinateCapBounds.magnitude_fits r s S w hdim hwCap
  have hs : s ≤ w := by unfold RamRecoverFeasibleSystem.wordWidth at hw; omega
  have h2 : 2 ≤ w := by unfold RamRecoverFeasibleSystem.wordWidth at hw; omega
  have hp : 4 ≤ 2 ^ w := by simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) h2
  refine ⟨by omega, hs.trans_lt (Nat.lt_two_pow_self (n := w)), ?_⟩
  have hle : IntegerCertificates.coordinateCap r s (2 ^ (2 * S)) ≤
      RamCoordinateCap.magnitude r s (2 ^ (2 * S)) := by
    dsimp only [RamCoordinateCap.magnitude]
    exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ 10)
  exact hle.trans_lt hmag

theorem optimal_spec (m n S N w : ℕ) (P : Program ℤ m n)
    (hdim : (m + (n + 2)) + (n + m) ≤ S)
    (hw : RamRecoverFeasibleSystem.wordWidth (m + (n + 2)) (n + m) S ≤ w)
    (hN : RamRationalReconstruction.depthBound (RamRecoverFeasibleSystem.recoveryBits S) + 1 ≤ N)
    (hA : ∀ i j, ((CertificateFamilyPrograms.optimal P).A i j).natAbs ≤ 2 ^ (2 * S))
    (hb : ∀ i, ((CertificateFamilyPrograms.optimal P).b i).natAbs ≤ 2 ^ (2 * S))
    (hf : ∃ x, PrimalFeasible (rationalProgram (CertificateFamilyPrograms.optimal P)) x) :
    Spec (2 ^ w) (RamRecoverFeasibleSystem.Input (CertificateFamilyPrograms.optimal P) S N) (recover 0)
      (fun σ τ => ∃ certificate : Certificate m n,
        τ.out = σ.out ++ encodeCertificate certificate ∧ IsValidCertificate (rationalProgram P) certificate)
      (RamRecoverFeasibleSystem.instructionBound (m + (n + 2)) (n + m) S + 35 * (n + m) + 10) := by
  obtain ⟨h2, hs, hD⟩ := emission_guards _ _ S w hdim hw
  exact recover_spec m n _ _ S N w 0 P _ RamWriteCertificate.optimalCertificate hdim hw hN hA hb hf
    (RamWriteCertificate.optimal_valid P) (fun z hz => RamWriteCertificate.optimal_spec (2 ^ w)
      (IntegerCertificates.coordinateCap _ _ (2 ^ (2 * S))) m n _ z (by omega) hD hs hz)


theorem infeasible_spec (m n S N w : ℕ) (P : Program ℤ m n)
    (hdim : (n + 1) + m ≤ S)
    (hw : RamRecoverFeasibleSystem.wordWidth (n + 1) m S ≤ w)
    (hN : RamRationalReconstruction.depthBound (RamRecoverFeasibleSystem.recoveryBits S) + 1 ≤ N)
    (hA : ∀ i j, ((CertificateFamilyPrograms.infeasible P).A i j).natAbs ≤ 2 ^ (2 * S))
    (hb : ∀ i, ((CertificateFamilyPrograms.infeasible P).b i).natAbs ≤ 2 ^ (2 * S))
    (hf : ∃ x, PrimalFeasible (rationalProgram (CertificateFamilyPrograms.infeasible P)) x) :
    Spec (2 ^ w) (RamRecoverFeasibleSystem.Input (CertificateFamilyPrograms.infeasible P) S N) (recover 1)
      (fun σ τ => ∃ certificate : Certificate m n,
        τ.out = σ.out ++ encodeCertificate certificate ∧ IsValidCertificate (rationalProgram P) certificate)
      (RamRecoverFeasibleSystem.instructionBound (n + 1) m S + 35 * m + 10) := by
  obtain ⟨h2, hs, hD⟩ := emission_guards _ _ S w hdim hw
  exact recover_spec m n _ _ S N w 1 P _ RamWriteCertificate.infeasibleCertificate hdim hw hN hA hb hf
    (RamWriteCertificate.infeasible_valid P) (fun z hz => RamWriteCertificate.infeasible_spec (2 ^ w)
      (IntegerCertificates.coordinateCap _ _ (2 ^ (2 * S))) m n _ z (by omega) hD hs hz)

theorem unbounded_spec (m n S N w : ℕ) (P : Program ℤ m n)
    (hdim : (m + (m + 1)) + (n + n) ≤ S)
    (hw : RamRecoverFeasibleSystem.wordWidth (m + (m + 1)) (n + n) S ≤ w)
    (hN : RamRationalReconstruction.depthBound (RamRecoverFeasibleSystem.recoveryBits S) + 1 ≤ N)
    (hA : ∀ i j, ((CertificateFamilyPrograms.unbounded P).A i j).natAbs ≤ 2 ^ (2 * S))
    (hb : ∀ i, ((CertificateFamilyPrograms.unbounded P).b i).natAbs ≤ 2 ^ (2 * S))
    (hf : ∃ x, PrimalFeasible (rationalProgram (CertificateFamilyPrograms.unbounded P)) x) :
    Spec (2 ^ w) (RamRecoverFeasibleSystem.Input (CertificateFamilyPrograms.unbounded P) S N) (recover 2)
      (fun σ τ => ∃ certificate : Certificate m n,
        τ.out = σ.out ++ encodeCertificate certificate ∧ IsValidCertificate (rationalProgram P) certificate)
      (RamRecoverFeasibleSystem.instructionBound (m + (m + 1)) (n + n) S + 35 * (n + n) + 10) := by
  obtain ⟨h2, hs, hD⟩ := emission_guards _ _ S w hdim hw
  exact recover_spec m n _ _ S N w 2 P _ RamWriteCertificate.unboundedCertificate hdim hw hN hA hb hf
    (RamWriteCertificate.unbounded_valid P) (fun z hz => RamWriteCertificate.unbounded_spec (2 ^ w)
      (IntegerCertificates.coordinateCap _ _ (2 ^ (2 * S))) m n _ z h2 hD hs hz)

end Lax109476Proofs.RamRecoverCertificate

import Lax109476Proofs.RamWriteVector
import Lax109476Proofs.CertificateFamilyPrograms

namespace Lax109476Proofs.RamWriteCertificate

open Lax109476.LinearProgram Lax109476.RationalEncoding Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RationalArithmeticBounds

/-- A literal outcome tag and the nonslack prefix of the recovered point.
The coordinate count is read from the runtime certificate-system metadata. -/
def emit (tag : ℕ) : Com := .seq (.write (.lit tag))
  (.seq (.assign "output.count" (.var "system.n")) (RamWriteVector.writePrefix "point.x"))

theorem prefix_encoding {r s : ℕ} (z : Fin (s + r) → ℚ) :
    ((List.ofFn z).take s).flatMap encodeRational = encodeVector (fun j => z (Fin.castAdd r j)) := by
  rw [List.ofFn_add]
  simp [encodeVector]
  congr 2

theorem emit_spec (B M r s tag : ℕ) (z : Fin (s + r) → ℚ)
    (h1 : 1 < B) (hMB : M < B) (hsB : s < B) (htag : tag < B)
    (hz : ∀ j, Height (z j) M) :
    Spec B (fun σ => Represents "point.x" (List.ofFn z) σ ∧ σ.vars "system.n" = s) (emit tag)
      (fun σ τ => τ.out = σ.out ++ [tag] ++ encodeVector (fun j => z (Fin.castAdd r j)))
      (35 * s + 10) := by
  have hwrite := RamWriteVector.writePrefix_spec B M s "point.x" (List.ofFn z) h1 hMB hsB
    (by simp) (by intro q hq; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq; exact hz j)
  rintro σ ⟨hσx, hσn⟩
  run_vcg [hwrite]
  all_goals clear hwrite
  all_goals simp_all [Represents, arrs_setVar, prefix_encoding, List.append_assoc]

def optimalCertificate {m n r : ℕ} (z : Fin ((n + m) + r) → ℚ) : Certificate m n :=
  .optimal (fun j => z (Fin.castAdd r (Fin.castAdd m j))) (fun i => z (Fin.castAdd r (Fin.natAdd n i)))

def infeasibleCertificate {m n r : ℕ} (z : Fin (m + r) → ℚ) : Certificate m n :=
  .infeasible (fun i => z (Fin.castAdd r i))

def unboundedCertificate {m n r : ℕ} (z : Fin ((n + n) + r) → ℚ) : Certificate m n :=
  .unbounded (fun j => z (Fin.castAdd r (Fin.castAdd n j))) (fun j => z (Fin.castAdd r (Fin.natAdd n j)))

theorem optimal_spec (B M m n r : ℕ) (z : Fin ((n + m) + r) → ℚ)
    (h1 : 1 < B) (hMB : M < B) (hsB : n + m < B) (hz : ∀ j, Height (z j) M) :
    Spec B (fun σ => Represents "point.x" (List.ofFn z) σ ∧ σ.vars "system.n" = n + m) (emit 0)
      (fun σ τ => τ.out = σ.out ++ encodeCertificate (optimalCertificate z : Certificate m n))
      (35 * (n + m) + 10) := by
  apply (emit_spec B M r (n + m) 0 z h1 hMB hsB (by omega) hz).post
  intro σ τ hσ hτ
  simpa only [RamWriteVector.encodeVector_split, encodeCertificate, optimalCertificate, List.append_assoc] using hτ

theorem infeasible_spec (B M m n r : ℕ) (z : Fin (m + r) → ℚ)
    (h1 : 1 < B) (hMB : M < B) (hsB : m < B) (hz : ∀ j, Height (z j) M) :
    Spec B (fun σ => Represents "point.x" (List.ofFn z) σ ∧ σ.vars "system.n" = m) (emit 1)
      (fun σ τ => τ.out = σ.out ++ encodeCertificate (infeasibleCertificate z : Certificate m n))
      (35 * m + 10) := by
  apply (emit_spec B M r m 1 z h1 hMB hsB h1 hz).post
  intro σ τ hσ hτ
  simpa only [encodeCertificate, infeasibleCertificate, List.append_assoc] using hτ

theorem unbounded_spec (B M m n r : ℕ) (z : Fin ((n + n) + r) → ℚ)
    (h2 : 2 < B) (hMB : M < B) (hsB : n + n < B) (hz : ∀ j, Height (z j) M) :
    Spec B (fun σ => Represents "point.x" (List.ofFn z) σ ∧ σ.vars "system.n" = n + n) (emit 2)
      (fun σ τ => τ.out = σ.out ++ encodeCertificate (unboundedCertificate z : Certificate m n))
      (35 * (n + n) + 10) := by
  apply (emit_spec B M r (n + n) 2 z (by omega) hMB hsB h2 hz).post
  intro σ τ hσ hτ
  simpa only [RamWriteVector.encodeVector_split, encodeCertificate, unboundedCertificate, List.append_assoc] using hτ

theorem optimal_valid {m n : ℕ} (P : Program ℤ m n)
    (z : Fin ((n + m) + (m + (n + 2))) → ℚ)
    (hz : PrimalFeasible (IntegerEncoding.rationalProgram (CertificateFamilyPrograms.optimal P))
      (fun j => z (Fin.castAdd _ j))) :
    IsValidCertificate (IntegerEncoding.rationalProgram P) (optimalCertificate z : Certificate m n) :=
  CertificateFamilyPrograms.optimal_valid P _ hz

theorem infeasible_valid {m n : ℕ} (P : Program ℤ m n) (z : Fin (m + (n + 1)) → ℚ)
    (hz : PrimalFeasible (IntegerEncoding.rationalProgram (CertificateFamilyPrograms.infeasible P))
      (fun j => z (Fin.castAdd _ j))) :
    IsValidCertificate (IntegerEncoding.rationalProgram P) (infeasibleCertificate z : Certificate m n) :=
  CertificateFamilyPrograms.infeasible_valid P _ hz

theorem unbounded_valid {m n : ℕ} (P : Program ℤ m n)
    (z : Fin ((n + n) + (m + (m + 1))) → ℚ)
    (hz : PrimalFeasible (IntegerEncoding.rationalProgram (CertificateFamilyPrograms.unbounded P))
      (fun j => z (Fin.castAdd _ j))) :
    IsValidCertificate (IntegerEncoding.rationalProgram P) (unboundedCertificate z : Certificate m n) :=
  CertificateFamilyPrograms.unbounded_valid P _ hz

end Lax109476Proofs.RamWriteCertificate

import Lax109476Proofs.RamCertificateSource
import Lax109476Proofs.RamCopyBlock

namespace Lax109476Proofs.RamCertificateSetup

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamFrame RamEllipsoidStep IntegerEncoding RationalArithmeticBounds

def parameter (L : ℕ) : ℕ := 2 * (L + 4)

def Saved (m n L : ℕ) (σ : Env) : Prop :=
  σ.vars "certificate.m" = m ∧ σ.vars "certificate.n" = n ∧
    σ.vars "certificate.bits" = L ∧ σ.vars "certificate.parameter" = parameter L

def metadata : Com := .seq (.assign "certificate.m" (.var "lp.m"))
  (.seq (.assign "certificate.n" (.var "lp.n"))
  (.seq (.assign "certificate.bits" (.var "input.bits"))
  (.seq (.assign "certificate.parameter" (.mul (.lit 2) (.add (.var "input.bits") (.lit 4))))
  (.seq (.assign "system.H" (.shiftl (.lit 1) (.mul (.lit 2) (.var "certificate.parameter"))))
  (.seq (.assign "source.m" (.var "lp.m")) (.assign "source.n" (.var "lp.n")))))))

theorem metadata_spec (B m n L : ℕ) (hB : 2 * parameter L + L + m + n + 8 < B)
    (hH : 2 ^ (2 * parameter L) < B) :
    Spec B (fun σ => σ.vars "lp.m" = m ∧ σ.vars "lp.n" = n ∧ σ.vars "input.bits" = L) metadata
      (fun _ τ => Saved m n L τ ∧ τ.vars "system.H" = 2 ^ (2 * parameter L) ∧
        τ.vars "source.m" = m ∧ τ.vars "source.n" = n) 22 := by
  have h1 : 1 < B := by omega
  have h2 : 2 < B := by omega
  have h4 : 4 < B := by omega
  have hm : m < B := by omega
  have hn : n < B := by omega
  have hL : L < B := by omega
  have hL4 : L + 4 < B := by omega
  have hp : parameter L < B := by omega
  have hp2 : 2 * parameter L < B := by omega
  rintro σ ⟨hσm, hσn, hσbits⟩
  run_vcg
  all_goals simp_all [Saved, parameter, Bop.apply_shiftl]

def copyCoefficients : Com := .seq (RamCopyBlock.copyBlock "int.A" "source.A" "decode.count")
  (.seq (RamCopyBlock.copyBlock "int.b" "source.b" "lp.m") (RamCopyBlock.copyBlock "int.c" "source.c" "lp.n"))

def Input {m n : ℕ} (P : Program ℤ m n) (L : ℕ) (σ : Env) : Prop :=
  Represents "int.A" (RamMatrixStorage.flatten (rationalProgram P).A) σ ∧
    Represents "int.b" (List.ofFn (rationalProgram P).b) σ ∧
    Represents "int.c" (List.ofFn (rationalProgram P).c) σ ∧
    σ.vars "lp.m" = m ∧ σ.vars "lp.n" = n ∧ σ.vars "decode.count" = m * n ∧ σ.vars "input.bits" = L ∧
    Extents "source.A" (m * n) σ ∧ Extents "source.b" m σ ∧ Extents "source.c" n σ

def save : Com := .seq copyCoefficients metadata

set_option maxHeartbeats 1000000 in
theorem save_spec (B M m n L : ℕ) (P : Program ℤ m n) (hM : 1 ≤ M) (hMB : M < B)
    (hB : m * n + 2 * parameter L + L + m + n + 8 < B) (hH : 2 ^ (2 * parameter L) < B)
    (hA : ∀ i j, (P.A i j).natAbs ≤ M) (hb : ∀ i, (P.b i).natAbs ≤ M)
    (hc : ∀ j, (P.c j).natAbs ≤ M) :
    Spec B (Input P L) save
      (fun _ τ => RamCertificateSource.Data P τ ∧ Saved m n L τ ∧ τ.vars "system.H" = 2 ^ (2 * parameter L))
      (71 * (m * n + m + n) + 100) := by
  have h1 : 1 < B := by omega
  have hAcopy := RamCopyBlock.copyBlock_spec B M (m * n) "int.A" "source.A" "decode.count"
    (fun i => (rationalProgram P).A i.divNat i.modNat) h1 (by omega) hMB
    (fun i => ⟨by simpa [rationalProgram] using hA i.divNat i.modNat, by simpa [rationalProgram] using hM⟩)
    (by simp [RamCopy.Disjoint, RamCopy.suffixes])
  have hbcopy := RamCopyBlock.copyBlock_spec B M m "int.b" "source.b" "lp.m"
    (rationalProgram P).b h1 (by omega) hMB
    (fun i => ⟨by simpa [rationalProgram] using hb i, by simpa [rationalProgram] using hM⟩) (by simp [RamCopy.Disjoint, RamCopy.suffixes])
  have hccopy := RamCopyBlock.copyBlock_spec B M n "int.c" "source.c" "lp.n"
    (rationalProgram P).c h1 (by omega) hMB
    (fun i => ⟨by simpa [rationalProgram] using hc i, by simpa [rationalProgram] using hM⟩) (by simp [RamCopy.Disjoint, RamCopy.suffixes])
  have hmeta := metadata_spec B m n L (by omega) hH
  rintro σ ⟨hσA, hσb, hσc, hσm, hσn, hσcount, hσbits, hσSA, hσSb, hσSc⟩
  obtain ⟨τ, hr₁, hτA, _⟩ := hAcopy σ ⟨hσA, hσSA, hσcount⟩
  have hτb := RamReadBody.represents_frame _ _ hσb hr₁ (by decide)
  have hτc := RamReadBody.represents_frame _ _ hσc hr₁ (by decide)
  have hτm := (hr₁.frame_var "lp.m" (by decide)).trans hσm
  obtain ⟨υ, hr₂, hυb, _⟩ := hbcopy τ
    ⟨hτb, RamAdvanceState.extents_of_run hr₁ "source.b" m hσSb, hτm⟩
  have hυc := RamReadBody.represents_frame _ _ hτc hr₂ (by decide)
  have hυn := ((hr₁.seq hr₂).frame_var "lp.n" (by decide)).trans hσn
  obtain ⟨ξ, hr₃, hξc, _⟩ := hccopy υ
    ⟨hυc, RamAdvanceState.extents_of_run (hr₁.seq hr₂) "source.c" n hσSc, hυn⟩
  have hrCopy := hr₁.seq (hr₂.seq hr₃)
  have hξm := (hrCopy.frame_var "lp.m" (by decide)).trans hσm
  have hξn := (hrCopy.frame_var "lp.n" (by decide)).trans hσn
  have hξbits := (hrCopy.frame_var "input.bits" (by decide)).trans hσbits
  obtain ⟨ρ, hr₄, hρSaved, hρH, hρm, hρn⟩ := hmeta ξ ⟨hξm, hξn, hξbits⟩
  have hρA := RamReadBody.represents_frame _ _ hτA (hr₂.seq (hr₃.seq hr₄)) (by decide)
  have hρb := RamReadBody.represents_frame _ _ hυb (hr₃.seq hr₄) (by decide)
  have hρc := RamReadBody.represents_frame _ _ hξc hr₄ (by decide)
  refine ⟨ρ, (hrCopy.seq hr₄).mono ?_, ⟨hρA, hρb, hρc, hρm, hρn⟩, hρSaved, hρH⟩
  simp only [Nat.mul_add]
  omega

/-- The feasibility routines use `source.m` and `source.n` as scratch fields.
Restore them from the saved input dimensions before building another family. -/
def restore : Com := .seq (.assign "source.m" (.var "certificate.m"))
  (.assign "source.n" (.var "certificate.n"))

theorem restore_spec (B m n : ℕ) (hm : m < B) (hn : n < B) :
    Spec B (fun σ => σ.vars "certificate.m" = m ∧ σ.vars "certificate.n" = n) restore
      (fun _ τ => τ.vars "source.m" = m ∧ τ.vars "source.n" = n) 4 := by
  rintro σ ⟨hσm, hσn⟩
  run_vcg
  all_goals simp_all

end Lax109476Proofs.RamCertificateSetup

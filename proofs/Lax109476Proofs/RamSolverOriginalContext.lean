import Lax109476Proofs.RamSolverWorkspace

namespace Lax109476Proofs.RamSolverOriginalContext

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays IntegerEncoding

def Coefficients {m n : ℕ} (P : Program ℤ m n) (σ : Env) : Prop :=
  Represents "source.A" (RamMatrixStorage.flatten (rationalProgram P).A) σ ∧
  Represents "source.b" (List.ofFn (rationalProgram P).b) σ ∧
  Represents "source.c" (List.ofFn (rationalProgram P).c) σ

def Context {m n : ℕ} (P : Program ℤ m n) (L : ℕ) (σ : Env) : Prop :=
  Coefficients P σ ∧ RamCertificateSetup.Saved m n L σ ∧
  σ.vars "system.H" = 2 ^ (2 * RamCertificateSetup.parameter L)

theorem of_source {m n L : ℕ} (P : Program ℤ m n) (σ : Env)
    (hData : RamCertificateSource.Data P σ) (hSaved : RamCertificateSetup.Saved m n L σ)
    (hH : σ.vars "system.H" = 2 ^ (2 * RamCertificateSetup.parameter L)) : Context P L σ :=
  ⟨⟨hData.1, hData.2.1, hData.2.2.1⟩, hSaved, hH⟩

theorem context_of_run {B k m n L : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ k)
    (P : Program ℤ m n) (hσ : Context P L σ)
    (hv : c.wvars ⊆ RamExactSolverProgram.chooseCertificate.wvars)
    (ha : c.warrs ⊆ RamExactSolverProgram.chooseCertificate.warrs) : Context P L τ := by
  have hs := RamExactSolverProgram.saved_dimension_preserved
  have hc := RamExactSolverProgram.original_coefficients_preserved
  have hfA : ∀ t ∈ RamCopy.suffixes, "source.A" ++ t ∉ c.warrs := by
    intro t ht hmem
    have hh := ha hmem
    simp [RamCopy.suffixes] at ht
    rcases ht with rfl | rfl | rfl
    · exact hc.1 hh
    · exact hc.2.1 hh
    · exact hc.2.2.1 hh
  have hfb : ∀ t ∈ RamCopy.suffixes, "source.b" ++ t ∉ c.warrs := by
    intro t ht hmem
    have hh := ha hmem
    simp [RamCopy.suffixes] at ht
    rcases ht with rfl | rfl | rfl
    · exact hc.2.2.2.1 hh
    · exact hc.2.2.2.2.1 hh
    · exact hc.2.2.2.2.2.1 hh
  have hfc : ∀ t ∈ RamCopy.suffixes, "source.c" ++ t ∉ c.warrs := by
    intro t ht hmem
    have hh := ha hmem
    simp [RamCopy.suffixes] at ht
    rcases ht with rfl | rfl | rfl
    · exact hc.2.2.2.2.2.2.1 hh
    · exact hc.2.2.2.2.2.2.2.1 hh
    · exact hc.2.2.2.2.2.2.2.2 hh
  refine ⟨⟨RamReadBody.represents_frame _ _ hσ.1.1 hr hfA,
    RamReadBody.represents_frame _ _ hσ.1.2.1 hr hfb,
    RamReadBody.represents_frame _ _ hσ.1.2.2 hr hfc⟩, ?_, ?_⟩
  · exact ⟨(hr.frame_var _ (fun h => hs.1 (hv h))).trans hσ.2.1.1,
      (hr.frame_var _ (fun h => hs.2.1 (hv h))).trans hσ.2.1.2.1,
      (hr.frame_var _ (fun h => hs.2.2.1 (hv h))).trans hσ.2.1.2.2.1,
      (hr.frame_var _ (fun h => hs.2.2.2.1 (hv h))).trans hσ.2.1.2.2.2⟩
  · exact (hr.frame_var _ (fun h => hs.2.2.2.2 (hv h))).trans hσ.2.2

theorem restore_spec (B m n L : ℕ) (P : Program ℤ m n) (hm : m < B) (hn : n < B) :
    Spec B (Context P L) RamCertificateSetup.restore
      (fun _ τ => RamCertificateSource.Data P τ ∧ Context P L τ) 4 := by
  intro σ hσ
  obtain ⟨τ, hr, hm', hn'⟩ := RamCertificateSetup.restore_spec B m n hm hn σ
    ⟨hσ.2.1.1, hσ.2.1.2.1⟩
  have hτ := context_of_run hr P hσ
    (by simp [RamCertificateSetup.restore, Com.wvars, RamExactSolverProgram.chooseCertificate,
      RamExactSolverProgram.afterOptimal, RamExactSolverProgram.afterInfeasible, Com.wvars])
    (by simp [RamCertificateSetup.restore, Com.warrs])
  exact ⟨τ, hr, ⟨hτ.1.1, hτ.1.2.1, hτ.1.2.2, hm', hn'⟩, hτ⟩

end Lax109476Proofs.RamSolverOriginalContext

import Lax109476Proofs.RamCertificateSource

namespace Lax109476Proofs.RamCertificateContext

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays

def fields : List String := ["source.m", "source.n", "system.m", "system.n"]

def Context {m n : ℕ} (P : Program ℤ m n) (r s : ℕ) (σ : Env) : Prop :=
  RamCertificateSource.Data P σ ∧ σ.vars "system.m" = r ∧ σ.vars "system.n" = s

theorem context_frame {B z : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ z)
    {m n : ℕ} (P : Program ℤ m n) (r s : ℕ) (hσ : Context P r s σ)
    (hf : ∀ a ∈ fields, a ∉ c.wvars)
    (ha : ∀ a ∈ RamCertificateSource.arrays, ∀ t ∈ RamCopy.suffixes, a ++ t ∉ c.warrs) :
    Context P r s τ := by
  exact ⟨RamCertificateSource.data_frame hr P hσ.1
      (fun a h => hf a (by simp [RamCertificateSource.fields] at h; rcases h with rfl | rfl <;> simp [fields])) ha,
    (hr.frame_var _ (hf _ (by simp [fields]))).trans hσ.2.1,
    (hr.frame_var _ (hf _ (by simp [fields]))).trans hσ.2.2⟩

theorem context_setVar {m n : ℕ} (P : Program ℤ m n) (r s : ℕ) (σ : Env) (v : String) (z : ℕ)
    (hv : v ∉ fields) (hσ : Context P r s σ) : Context P r s (σ.setVar v z) := by
  have hr : v ≠ "system.m" := by intro h; subst v; simp [fields] at hv
  have hs : v ≠ "system.n" := by intro h; subst v; simp [fields] at hv
  exact ⟨RamCertificateSource.data_setVar P σ v z
    (fun h => hv (by simp [RamCertificateSource.fields] at h; rcases h with rfl | rfl <;> simp [fields])) hσ.1,
    by simpa [vars_setVar, Ne.symm hr] using hσ.2.1,
    by simpa [vars_setVar, Ne.symm hs] using hσ.2.2⟩

theorem preserves_context (B : ℕ) {m n : ℕ} (P : Program ℤ m n) (r s : ℕ) (c : Com)
    (hf : ∀ a ∈ fields, a ∉ c.wvars)
    (ha : ∀ a ∈ RamCertificateSource.arrays, ∀ t ∈ RamCopy.suffixes, a ++ t ∉ c.warrs) :
    RamBisectionLoop.preserves B (Context P r s) c := fun hr hσ => context_frame hr P r s hσ hf ha

end Lax109476Proofs.RamCertificateContext

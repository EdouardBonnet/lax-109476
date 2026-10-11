import Lax109476Proofs.RamRecoveryBoundSelector
import Lax109476Proofs.RamBuildVector

namespace Lax109476Proofs.RamRecoveryData

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamRationalScalars RamScalarFrame

def fields : List String := ["point.m", "point.n", "point.k", "bisect.mid.s", "bisect.mid.n", "bisect.mid.d"]

def arrays : List String := ["point.A", "point.b", "point.x"]

def Data {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (k : ℕ) (t : ℚ) (σ : Env) : Prop :=
  Represents "point.A" (RamMatrixStorage.flatten P.A) σ ∧ Represents "point.b" (List.ofFn P.b) σ ∧
    Represents "point.x" (List.ofFn x) σ ∧ σ.vars "point.m" = m ∧ σ.vars "point.n" = n ∧
    σ.vars "point.k" = k ∧ Value "bisect.mid" t σ

theorem data_frame {B z : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ z)
    {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (k : ℕ) (t : ℚ) (hσ : Data P x k t σ)
    (hf : ∀ a ∈ fields, a ∉ c.wvars)
    (ha : ∀ a ∈ arrays, ∀ s ∈ RamCopy.suffixes, a ++ s ∉ c.warrs) : Data P x k t τ := by
  rcases hσ with ⟨hA, hb, hx, hm, hn, hk, ht⟩
  exact ⟨RamReadBody.represents_frame _ _ hA hr (ha _ (by simp [arrays])),
    RamReadBody.represents_frame _ _ hb hr (ha _ (by simp [arrays])),
    RamReadBody.represents_frame _ _ hx hr (ha _ (by simp [arrays])),
    (hr.frame_var _ (hf _ (by simp [fields]))).trans hm,
    (hr.frame_var _ (hf _ (by simp [fields]))).trans hn,
    (hr.frame_var _ (hf _ (by simp [fields]))).trans hk,
    value_frame hr "bisect.mid" t ht (hf _ (by simp [fields])) (hf _ (by simp [fields])) (hf _ (by simp [fields]))⟩

theorem data_setVar {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (k : ℕ) (t : ℚ)
    (σ : Env) (v : String) (z : ℕ) (hv : v ∉ fields) (hσ : Data P x k t σ) :
    Data P x k t (σ.setVar v z) := by
  have hm : v ≠ "point.m" := by intro h; subst v; simp [fields] at hv
  have hn : v ≠ "point.n" := by intro h; subst v; simp [fields] at hv
  have hk : v ≠ "point.k" := by intro h; subst v; simp [fields] at hv
  have hs : v ≠ "bisect.mid.s" := by intro h; subst v; simp [fields] at hv
  have hnum : v ≠ "bisect.mid.n" := by intro h; subst v; simp [fields] at hv
  have hd : v ≠ "bisect.mid.d" := by intro h; subst v; simp [fields] at hv
  simpa [Data, Value, Represents, arrs_setVar, vars_setVar, Ne.symm hm, Ne.symm hn, Ne.symm hk, Ne.symm hs, Ne.symm hnum, Ne.symm hd] using hσ

theorem preserves_data (B : ℕ) {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (k : ℕ) (t : ℚ)
    (c : Com) (hf : ∀ a ∈ fields, a ∉ c.wvars)
    (ha : ∀ a ∈ arrays, ∀ s ∈ RamCopy.suffixes, a ++ s ∉ c.warrs) :
    RamBisectionLoop.preserves B (Data P x k t) c := fun hr hσ => data_frame hr P x k t hσ hf ha

end Lax109476Proofs.RamRecoveryData

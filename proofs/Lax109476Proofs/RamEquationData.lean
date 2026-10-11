import Lax109476Proofs.RamStandardPointRecovery
import Lax109476Proofs.RamResultNegation
import Lax109476Proofs.RamArrayResult

namespace Lax109476Proofs.RamEquationData

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays IntegerEncoding

def fields : List String := ["system.m", "system.n"]
def arrays : List String := ["system.A", "system.b"]

def Data {m n : ℕ} (P : Program ℤ m n) (σ : Env) : Prop :=
  Represents "system.A" (RamMatrixStorage.flatten (rationalProgram P).A) σ ∧
    Represents "system.b" (List.ofFn (rationalProgram P).b) σ ∧
    σ.vars "system.m" = m ∧ σ.vars "system.n" = n

theorem data_frame {B z : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ z)
    {m n : ℕ} (P : Program ℤ m n) (hσ : Data P σ)
    (hf : ∀ a ∈ fields, a ∉ c.wvars)
    (ha : ∀ a ∈ arrays, ∀ s ∈ RamCopy.suffixes, a ++ s ∉ c.warrs) : Data P τ := by
  rcases hσ with ⟨hA, hb, hm, hn⟩
  exact ⟨RamReadBody.represents_frame _ _ hA hr (ha _ (by simp [arrays])),
    RamReadBody.represents_frame _ _ hb hr (ha _ (by simp [arrays])),
    (hr.frame_var _ (hf _ (by simp [fields]))).trans hm,
    (hr.frame_var _ (hf _ (by simp [fields]))).trans hn⟩

theorem data_setVar {m n : ℕ} (P : Program ℤ m n) (σ : Env) (v : String) (z : ℕ)
    (hv : v ∉ fields) (hσ : Data P σ) : Data P (σ.setVar v z) := by
  have hm : v ≠ "system.m" := by intro h; subst v; simp [fields] at hv
  have hn : v ≠ "system.n" := by intro h; subst v; simp [fields] at hv
  simpa [Data, Represents, arrs_setVar, vars_setVar, Ne.symm hm, Ne.symm hn] using hσ

theorem preserves_data (B : ℕ) {m n : ℕ} (P : Program ℤ m n) (c : Com)
    (hf : ∀ a ∈ fields, a ∉ c.wvars)
    (ha : ∀ a ∈ arrays, ∀ s ∈ RamCopy.suffixes, a ++ s ∉ c.warrs) :
    RamBisectionLoop.preserves B (Data P) c := fun hr hσ => data_frame hr P hσ hf ha

end Lax109476Proofs.RamEquationData

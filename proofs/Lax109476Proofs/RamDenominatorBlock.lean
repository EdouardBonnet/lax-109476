import Lax109476Proofs.RamDenominatorProduct

namespace Lax109476Proofs.RamDenominatorBlock

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamDenominatorProduct RamRationalArrays RamFrame RamReadBlock

theorem productArray_wvars (a : String) : (productArray a).wvars = (productArray "").wvars := by rfl

def productBlock (a field : String) : Com := .seq (.assign "vec.n" (.var field)) (productArray a)

theorem productBlock_spec (B D n : ℕ) (a field : String) (v : Fin n → ℚ)
    (hD : 0 < D) (hnB : n < B) (hprod : D * product v < B) :
    Spec B (fun σ => Represents a (List.ofFn v) σ ∧ σ.vars "den.value" = D ∧ σ.vars field = n)
      (productBlock a field)
      (fun σ τ => τ.vars "den.value" = D * product v ∧
        FieldsAgree fields σ τ ∧ τ.arrs = σ.arrs) (13 * n + 8) := by
  have harray := spec_with_fields fields (productArray_spec B D n a v hD hnB hprod)
    (by intro x hx; rw [productArray_wvars]; simp [fields] at hx;
        rcases hx with rfl | rfl | rfl <;> decide) (by rfl)
  rintro σ ⟨hσa, hσD, hσn⟩
  have hr₁ : Run B (.assign "vec.n" (.var field)) σ (σ.setVar "vec.n" n) 2 :=
    Run.assign (by simpa only [hσn] using evalB_var (B := B) (σ := σ) (x := field) (hσn ▸ hnB))
  obtain ⟨τ, hr₂, hτ, hfields, harr⟩ := harray (σ.setVar "vec.n" n) ⟨hσa, hσD, by simp⟩
  refine ⟨τ, (hr₁.seq hr₂).mono (by omega), hτ.2.1, ?_, harr⟩
  intro x hx
  exact (hfields x hx).trans (by simp [fields] at hx; rcases hx with rfl | rfl | rfl <;> simp [Env.setVar])

end Lax109476Proofs.RamDenominatorBlock

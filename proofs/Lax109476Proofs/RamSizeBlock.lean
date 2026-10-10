import Lax109476Proofs.RamEncodedSize

namespace Lax109476Proofs.RamSizeBlock

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamEncodedSize RamRationalArrays RamFrame RationalArithmeticBounds
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding RamReadBlock

theorem countArray_wvars (a : String) : (countArray a).wvars = (countArray "").wvars := by rfl

def countBlock (a field : String) : Com := .seq (.assign "vec.n" (.var field)) (countArray a)

theorem countBlock_spec (B H n t : ℕ) (a field : String) (v : Fin n → ℚ)
    (h2 : 2 < B) (hH : 1 ≤ H) (hHB : H < B) (hnB : n < B)
    (hv : ∀ i, Height (v i) H) (ht : t + bitSize (encodeVector v) < B) :
    Spec B (fun σ => Represents a (List.ofFn v) σ ∧ σ.vars "size.total" = t ∧ σ.vars field = n)
      (countBlock a field)
      (fun σ τ => τ.vars "size.total" = t + bitSize (encodeVector v) ∧
        FieldsAgree fields σ τ ∧ τ.arrs = σ.arrs)
      ((36 * H.size + 61) * n + 8) := by
  have harray := spec_with_fields fields (countArray_spec B H n t a v h2 hH hHB hnB hv ht)
    (by intro x hx; rw [countArray_wvars]; simp [fields] at hx;
        rcases hx with rfl | rfl | rfl <;> decide) (by rfl)
  rintro σ ⟨hσa, hσt, hσn⟩
  have hr₁ : Run B (.assign "vec.n" (.var field)) σ (σ.setVar "vec.n" n) 2 :=
    Run.assign (by simpa only [hσn] using evalB_var (B := B) (σ := σ) (x := field) (hσn ▸ hnB))
  obtain ⟨τ, hr₂, hτ, hfields, harr⟩ := harray (σ.setVar "vec.n" n) ⟨hσa, hσt, by simp⟩
  refine ⟨τ, (hr₁.seq hr₂).mono (by omega), hτ.2.1, ?_, harr⟩
  intro x hx
  exact (hfields x hx).trans (by simp [fields] at hx; rcases hx with rfl | rfl | rfl <;> simp [Env.setVar])

end Lax109476Proofs.RamSizeBlock

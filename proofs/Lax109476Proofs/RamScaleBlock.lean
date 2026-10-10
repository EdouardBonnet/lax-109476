import Lax109476Proofs.RamScaleArray
import Lax109476Proofs.RamReadBlock

namespace Lax109476Proofs.RamScaleBlock

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamScaleArray RamRationalArrays RamFrame RationalArithmeticBounds RamReadBlock

def fields : List String := ["lp.m", "lp.n", "decode.count", "den.value", "input.bits"]

theorem scaleArray_wvars (a b : String) : (scaleArray a b).wvars = (scaleArray "" "").wvars := by rfl

theorem scaleArray_warrs (a b : String) : (scaleArray a b).warrs = (RamReadArray.readArray b).warrs := by rfl

def scaleBlock (a b field : String) : Com := .seq (.assign "vec.n" (.var field)) (scaleArray a b)

theorem scaleBlock_spec (B M n D : ℕ) (a b field : String) (v : Fin n → ℚ)
    (hM : 1 ≤ M) (hnB : n < B) (hB : 2 * M ^ 2 + 3 < B)
    (hv : ∀ i, Height (v i) M) (hD : D ≤ M) (hab : RamCopy.Disjoint a b) :
    Spec B (fun σ => Represents a (List.ofFn v) σ ∧
        (σ.arrs (b ++ ".s")).length = n ∧ (σ.arrs (b ++ ".n")).length = n ∧
        (σ.arrs (b ++ ".d")).length = n ∧ σ.vars field = n ∧ σ.vars "scale.factor" = D)
      (scaleBlock a b field)
      (fun σ τ => Represents b (List.ofFn (scaled v D)) τ ∧
        FieldsAgree fields σ τ ∧ τ.vars "scale.factor" = D ∧
        ∀ c ∉ [b ++ ".s", b ++ ".n", b ++ ".d"], τ.arrs c = σ.arrs c)
      ((72 * M.size + 135) * n + 26) := by
  have harray := spec_with_write_frame fields (scaleArray_spec B M n D a b v hM hnB hB hv hD hab)
    (by
      intro x hx
      rw [scaleArray_wvars]
      simp [fields] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)
  rintro σ ⟨hσa, hσs, hσnum, hσd, hσn, hσD⟩
  have hr₁ : Run B (.assign "vec.n" (.var field)) σ (σ.setVar "vec.n" n) 2 :=
    Run.assign (by simpa only [hσn] using evalB_var (B := B) (σ := σ) (x := field) (hσn ▸ hnB))
  obtain ⟨τ, hr₂, hτ, hfields, harr⟩ := harray (σ.setVar "vec.n" n)
    ⟨hσa, hσs, hσnum, hσd, by simp, hσD⟩
  refine ⟨τ, (hr₁.seq hr₂).mono (by omega), hτ.1, ?_, hτ.2.2.2, ?_⟩
  · intro x hx
    exact (hfields x hx).trans (by
      simp [fields] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [Env.setVar])
  · intro c hc
    apply harr c
    rw [scaleArray_warrs, RamReadBlock.readArray_warrs]
    simp at hc ⊢
    tauto

end Lax109476Proofs.RamScaleBlock

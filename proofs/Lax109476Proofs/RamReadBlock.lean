import Lax109476Proofs.RamReadMatrix

namespace Lax109476Proofs.RamReadBlock

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamReadArray RamRationalArrays RamFrame

def fields : List String := ["lp.m", "lp.n", "decode.count"]

theorem readArray_wvars (a : String) : (readArray a).wvars = (readArray "").wvars := by rfl

theorem readArray_warrs (a : String) : (readArray a).warrs =
    [a ++ ".s", a ++ ".n", a ++ ".d", a ++ ".s", a ++ ".s", a ++ ".n", a ++ ".d"] := by rfl

def readBlock (a field : String) : Com :=
  .seq (.assign "vec.n" (.var field)) (readArray a)

theorem readBlock_spec (B M n v : ℕ) (a field : String) (xs : List ℕ)
    (h2 : 2 < B) (hMB : M < B) (hM : 1 ≤ M) (hnB : n < B)
    (hxB : xs.length < B) (hv : v ≤ 1) (hwords : ∀ z ∈ xs, z ≤ M)
    (hfield : field ∈ fields) :
    Spec B (fun σ => (σ.arrs (a ++ ".s")).length = n ∧
        (σ.arrs (a ++ ".n")).length = n ∧ (σ.arrs (a ++ ".d")).length = n ∧
        σ.inp = xs ∧ σ.vars "input.remaining" = xs.length ∧ σ.vars "input.valid" = v ∧
        σ.InpBounded B ∧ σ.vars field = n)
      (readBlock a field)
      (fun σ τ => Represents a (List.ofFn (values xs v n)) τ ∧ τ.inp = xs.drop (3 * n) ∧
        τ.vars "input.remaining" = (xs.drop (3 * n)).length ∧
        τ.vars "input.valid" = flag xs v n ∧ τ.InpBounded B ∧
        FieldsAgree fields σ τ ∧ ∀ b ∉ [a ++ ".s", a ++ ".n", a ++ ".d"], τ.arrs b = σ.arrs b)
      ((36 * M.size + 115) * n + 26) := by
  have hf : ∀ x ∈ fields, x ∉ (readArray a).wvars := by
    intro x hx; rw [readArray_wvars]
    simp [fields] at hx
    rcases hx with rfl | rfl | rfl <;> decide
  have harray := spec_with_write_frame fields
    (readArray_spec B M n v a xs h2 hMB hM hnB hxB hv hwords) hf
  rintro σ ⟨hσs, hσnum, hσd, hσinp, hσrem, hσvalid, hσbound, hσn⟩
  have hr₁ : Run B (.assign "vec.n" (.var field)) σ (σ.setVar "vec.n" n) 2 :=
    Run.assign (by simpa only [hσn] using evalB_var (B := B) (σ := σ) (x := field) (hσn ▸ hnB))
  obtain ⟨τ, hr₂, hτ, hfields, harrs⟩ := harray (σ.setVar "vec.n" n)
    ⟨hσs, hσnum, hσd, hσinp, hσrem, hσvalid, hr₁.inpBounded hσbound, by simp⟩
  refine ⟨τ, (hr₁.seq hr₂).mono (by omega), hτ.1, hτ.2.1, hτ.2.2.1, hτ.2.2.2.1, hτ.2.2.2.2.1, ?_, ?_⟩
  · intro x hx
    exact (hfields x hx).trans (by simp [fields] at hx; rcases hx with rfl | rfl | rfl <;> simp [Env.setVar])
  · intro b hb
    apply harrs b
    rw [readArray_warrs]
    simp at hb ⊢
    tauto


end Lax109476Proofs.RamReadBlock

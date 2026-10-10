import Lax109476Proofs.RamCopy
import Lax109476Proofs.RamReadBlock
import Lax109476Proofs.RamEllipsoidStep

namespace Lax109476Proofs.RamCopyBlock

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamCopy RamRationalArrays RamEllipsoidStep RationalArithmeticBounds

def copyBlock (a b field : String) : Com :=
  .seq (.assign "vec.n" (.var field)) (copyRationalArray a b)

theorem copyBlock_wvars (a b field : String) :
    (copyBlock a b field).wvars = (copyBlock "" "" "").wvars := by rfl

theorem copyBlock_warrs (a b field : String) :
    (copyBlock a b field).warrs =
      [b ++ ".s", b ++ ".n", b ++ ".d", b ++ ".s", b ++ ".s", b ++ ".n", b ++ ".d"] := by rfl

theorem copyBlock_spec (B M n : ℕ) (a b field : String) (v : Fin n → ℚ)
    (h1 : 1 < B) (hnB : n < B) (hMB : M < B) (hv : ∀ i, Height (v i) M)
    (hab : Disjoint a b) :
    Spec B (fun σ => Represents a (List.ofFn v) σ ∧ Extents b n σ ∧ σ.vars field = n)
      (copyBlock a b field)
      (fun _ τ => Represents b (List.ofFn v) τ ∧ Represents a (List.ofFn v) τ)
      (71 * n + 26) := by
  rintro σ ⟨hσa, hσb, hσn⟩
  have hr₁ : Run B (.assign "vec.n" (.var field)) σ (σ.setVar "vec.n" n) 2 :=
    Run.assign (by simpa only [hσn] using evalB_var (B := B) (σ := σ) (x := field) (hσn ▸ hnB))
  obtain ⟨τ, hr₂, hτ⟩ := copyRationalArray_spec B n M a b v h1 hnB hMB hv hab
    (σ.setVar "vec.n" n)
    ⟨hσa, hσb ".s" (by simp), hσb ".n" (by simp), hσb ".d" (by simp), by simp⟩
  exact ⟨τ, (hr₁.seq hr₂).mono (by omega), hτ.1, hτ.2.1⟩

end Lax109476Proofs.RamCopyBlock

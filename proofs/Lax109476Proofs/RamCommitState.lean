import Lax109476Proofs.RamCopy
import Lax109476Proofs.RamEllipsoidStep

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamCommitState

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamFrame RationalArithmeticBounds RamCopy RamMatrixStorage RamEllipsoidStep

/-- Restore the logical dimension after copying the flattened shape. -/
def commitShape : Com :=
  .seq (.assign "state.savedn" (.var "vec.n"))
    (.seq (.assign "vec.n" (.mul (.var "vec.n") (.var "vec.n")))
      (.seq (copyRationalArray "ell.nextshape" "ell.shape") (.assign "vec.n" (.var "state.savedn"))))

theorem commitShape_spec (B n M : ℕ) (A : Matrix (Fin n) (Fin n) ℚ)
    (h1 : 1 < B) (hnB : n < B) (hnnB : n * n < B) (hMB : M < B)
    (hA : ∀ i j, Height (A i j) M) :
    Spec B (fun σ => Represents "ell.nextshape" (flatten A) σ ∧
        (σ.arrs "ell.shape.s").length = n * n ∧ (σ.arrs "ell.shape.n").length = n * n ∧
        (σ.arrs "ell.shape.d").length = n * n ∧ σ.vars "vec.n" = n)
      commitShape
      (fun _ τ => Represents "ell.shape" (flatten A) τ ∧ Represents "ell.nextshape" (flatten A) τ ∧
        τ.vars "vec.n" = n)
      (71 * (n * n) + 32) := by
  have hv : ∀ k : Fin (n * n), Height (A k.divNat k.modNat) M := fun k => hA k.divNat k.modNat
  have hcopy := spec_with_write_frame ["state.savedn"]
    (copyRationalArray_spec B (n * n) M "ell.nextshape" "ell.shape"
      (fun k => A k.divNat k.modNat) h1 hnnB hMB hv (by simp [RamCopy.Disjoint, RamCopy.suffixes]))
    (by intro x hx; simp at hx; subst x; simp [copyRationalArray, copyLoop, copyStep,
      copyCoordinate, leftToResult, loadLeft, RamRationalArrays.storeReduced,
      RamZeroArray.zeroRationalArray, RamZeroArray.fillConstant, Lib.Fill.put, Com.wvars])
  rintro σ ⟨hσA, hσs, hσn, hσd, hσN⟩
  run_vcg [hcopy]
  all_goals clear hcopy
  all_goals simp_all [flatten, Represents, FieldsAgree]
  all_goals aesop

def commitState : Com := .seq (copyRationalArray "ell.nextcenter" "ell.center") commitShape

theorem copy_center_no_other_writes (b : String)
    (hb : b ∉ ["ell.center.s", "ell.center.n", "ell.center.d"]) :
    b ∉ (copyRationalArray "ell.nextcenter" "ell.center").warrs := by
  simp at hb
  simp [copyRationalArray, copyLoop, copyStep, copyCoordinate, leftToResult, loadLeft,
    RamRationalArrays.storeReduced, RamZeroArray.zeroRationalArray, RamZeroArray.fillConstant,
    Lib.Fill.put, Com.warrs, hb.1, hb.2.1, hb.2.2]

theorem commit_shape_no_other_writes (b : String)
    (hb : b ∉ ["ell.shape.s", "ell.shape.n", "ell.shape.d"]) : b ∉ commitShape.warrs := by
  simp at hb
  simp [commitShape, copyRationalArray, copyLoop, copyStep, copyCoordinate, leftToResult, loadLeft,
    RamRationalArrays.storeReduced, RamZeroArray.zeroRationalArray, RamZeroArray.fillConstant,
    Lib.Fill.put, Com.warrs, hb.1, hb.2.1, hb.2.2]

theorem commitState_spec (B n M : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ)
    (h1 : 1 < B) (hnB : n < B) (hnnB : n * n < B) (hMB : M < B)
    (hA : ∀ i j, Height (A i j) M) (hc : ∀ i, Height (c i) M) :
    Spec B (fun σ => Represents "ell.nextshape" (flatten A) σ ∧
        Represents "ell.nextcenter" (List.ofFn c) σ ∧ Extents "ell.center" n σ ∧
        Extents "ell.shape" (n * n) σ ∧ σ.vars "vec.n" = n)
      commitState
      (fun _ τ => Represents "ell.shape" (flatten A) τ ∧ Represents "ell.center" (List.ofFn c) τ ∧
        Represents "ell.nextshape" (flatten A) τ ∧ Represents "ell.nextcenter" (List.ofFn c) τ ∧
        τ.vars "vec.n" = n)
      (71 * n + 71 * (n * n) + 56) := by
  rintro σ ⟨hσA, hσc, hσcExt, hσAExt, hσn⟩
  obtain ⟨τ, hr₁, hτc, hτnextc, hτn⟩ := copyRationalArray_spec B n M "ell.nextcenter" "ell.center" c
    h1 hnB hMB hc (by simp [RamCopy.Disjoint, RamCopy.suffixes]) σ
    ⟨hσc, hσcExt ".s" (by simp), hσcExt ".n" (by simp), hσcExt ".d" (by simp), hσn⟩
  have hτA := RamEllipsoidUpdate.represents_frame hr₁ "ell.nextshape" _ hσA
    (copy_center_no_other_writes _ (by simp)) (copy_center_no_other_writes _ (by simp))
    (copy_center_no_other_writes _ (by simp))
  have hτAExt := extents_frame hr₁ "ell.shape" (n * n) hσAExt (by
    intro s hs; simp at hs; rcases hs with rfl | rfl | rfl <;> exact copy_center_no_other_writes _ (by simp))
  obtain ⟨υ, hr₂, hυA, hυnextA, hυn⟩ := commitShape_spec B n M A h1 hnB hnnB hMB hA
    τ ⟨hτA, hτAExt ".s" (by simp), hτAExt ".n" (by simp), hτAExt ".d" (by simp), hτn⟩
  have hυc := RamEllipsoidUpdate.represents_frame hr₂ "ell.center" _ hτc
    (commit_shape_no_other_writes _ (by simp)) (commit_shape_no_other_writes _ (by simp))
    (commit_shape_no_other_writes _ (by simp))
  have hυnextc := RamEllipsoidUpdate.represents_frame hr₂ "ell.nextcenter" _ hτnextc
    (commit_shape_no_other_writes _ (by simp)) (commit_shape_no_other_writes _ (by simp))
    (commit_shape_no_other_writes _ (by simp))
  exact ⟨υ, (hr₁.seq hr₂).mono (by omega), hυA, hυc, hυnextA, hυnextc, hυn⟩

end Lax109476Proofs.RamCommitState

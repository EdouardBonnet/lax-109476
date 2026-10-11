import Lax109476Proofs.RamCertificateContext
import Lax109476Proofs.RamBuildVector

namespace Lax109476Proofs.RamCertificateMatrix

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds IntegerEncoding RamEllipsoidStep
open RamCertificateContext

def values {r s : ℕ} (F : Program ℤ r s) : Fin (r * s) → ℚ :=
  fun i => F.A i.divNat i.modNat

def selectCoordinate (selector : Com) : Com := .seq
  (.assign "query.row" (.div (.var "build.i") (.var "system.n")))
  (.seq (.assign "query.col" (.sub (.var "build.i")
    (.mul (.var "query.row") (.var "system.n")))) selector)

set_option maxHeartbeats 1000000 in
theorem selectCoordinate_spec (B m n r s selectorCost : ℕ) (P : Program ℤ m n) (F : Program ℤ r s)
    (selector : Com) (hB : r * s + s + 4 < B)
    (hselector : ∀ i j, Spec B
      (fun σ => RamCertificateSource.Data P σ ∧ σ.vars "query.row" = i.val ∧ σ.vars "query.col" = j.val)
      selector (fun _ τ => RamCertificateSource.Data P τ ∧ FractionOutput (F.A i j : ℚ) τ) selectorCost)
    (hf : ∀ a ∈ fields, a ∉ selector.wvars)
    (ha : ∀ a ∈ RamCertificateSource.arrays, ∀ t ∈ RamCopy.suffixes, a ++ t ∉ selector.warrs)
    (i : Fin (r * s)) :
    Spec B (fun σ => Context P r s σ ∧ σ.vars "build.i" = i.val ∧ σ.vars "build.count" = r * s)
      (selectCoordinate selector) (fun _ τ => Context P r s τ ∧ FractionOutput (values F i) τ)
      (selectorCost + 14) := by
  have hiB : i.val < B := i.isLt.trans (by omega)
  have hs : s < B := by omega
  have hdiv : i.val / s < B := (Nat.div_le_self _ _).trans_lt hiB
  have hmul : (i.val / s) * s < B := (Nat.div_mul_le_self _ _).trans_lt hiB
  have hsub : i.val - (i.val / s) * s < B := (Nat.sub_le _ _).trans_lt hiB
  have hmod : i.val - (i.val / s) * s = i.val % s := by
    simpa [Nat.mul_comm] using (Nat.mod_eq_sub_mul_div (x := i.val) (k := s)).symm
  have hsel := hselector i.divNat i.modNat
  have hbase : Spec B (fun σ => Context P r s σ ∧ σ.vars "build.i" = i.val ∧ σ.vars "build.count" = r * s)
      (selectCoordinate selector) (fun _ τ => FractionOutput (values F i) τ) (selectorCost + 14) := by
    rintro σ ⟨⟨⟨hσA, hσb, hσc, hσm, hσn⟩, hσr, hσs⟩, hσi, hσcount⟩
    run_vcg [hsel]
    all_goals clear hsel
    all_goals simp_all [values, Fin.divNat, Fin.modNat, RamCertificateSource.Data, Represents, arrs_setVar]
    all_goals omega
  intro σ hσ
  obtain ⟨τ, hr, hτ⟩ := hbase σ hσ
  refine ⟨τ, hr, context_frame hr P r s hσ.1 ?_ ?_, hτ⟩
  · intro a ha'
    have haRow : a ≠ "query.row" := by simp [fields] at ha'; rcases ha' with rfl | rfl | rfl | rfl <;> decide
    have haCol : a ≠ "query.col" := by simp [fields] at ha'; rcases ha' with rfl | rfl | rfl | rfl <;> decide
    simp [selectCoordinate, Com.wvars, haRow, haCol, hf a ha']
  · simpa [selectCoordinate, Com.warrs] using ha

def prepare : Com := .assign "build.count" (.mul (.var "system.m") (.var "system.n"))
def matrix (selector : Com) : Com := .seq prepare (RamBuildVector.build "system.A" (selectCoordinate selector))

set_option maxHeartbeats 1000000 in
theorem matrix_spec (B M m n r s selectorCost : ℕ) (P : Program ℤ m n) (F : Program ℤ r s)
    (selector : Com) (hM : 1 ≤ M) (hMB : M < B) (hB : r * s + r + s + 4 < B)
    (hA : ∀ i j, (F.A i j).natAbs ≤ M)
    (hselector : ∀ i j, Spec B
      (fun σ => RamCertificateSource.Data P σ ∧ σ.vars "query.row" = i.val ∧ σ.vars "query.col" = j.val)
      selector (fun _ τ => RamCertificateSource.Data P τ ∧ FractionOutput (F.A i j : ℚ) τ) selectorCost)
    (hf : ∀ a ∈ fields, a ∉ selector.wvars)
    (ha : ∀ a ∈ RamCertificateSource.arrays, ∀ t ∈ RamCopy.suffixes, a ++ t ∉ selector.warrs)
    (hiFrame : "build.i" ∉ selector.wvars) (hnFrame : "build.count" ∉ selector.wvars)
    (htarget : ∀ t ∈ RamCopy.suffixes, "system.A" ++ t ∉ selector.warrs) :
    Spec B (fun σ => Context P r s σ ∧ Extents "system.A" (r * s) σ) (matrix selector)
      (fun _ τ => Context P r s τ ∧ Represents "system.A" (RamMatrixStorage.flatten (rationalProgram F).A) τ)
      ((selectorCost + 70) * (r * s) + 34) := by
  have h1 : 1 < B := by omega
  have hNB : r * s < B := by omega
  have hbuild := RamBuildVector.build_spec B M (r * s) (selectorCost + 14) "system.A" (values F)
    (selectCoordinate selector) (Context P r s) h1 hNB hMB
    (fun i => ⟨by simpa [values] using hA i.divNat i.modNat, by simpa [values] using hM⟩)
    (selectCoordinate_spec B m n r s selectorCost P F selector (by omega) hselector hf ha)
    (by simpa [selectCoordinate, Com.wvars] using hiFrame)
    (by simpa [selectCoordinate, Com.wvars] using hnFrame)
    (by simpa [selectCoordinate, Com.warrs] using htarget)
    (preserves_context B P r s (storeReduced "system.A")
      (by intro a ha'; simp [fields] at ha'; rcases ha' with rfl | rfl | rfl | rfl <;> decide)
      (by
        intro a ha' t ht
        simp [RamCertificateSource.arrays] at ha'
        simp [RamCopy.suffixes] at ht
        rcases ha' with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;> decide))
    (preserves_context B P r s (RamZeroArray.zeroRationalArray "system.A")
      (by intro a ha'; simp [fields] at ha'; rcases ha' with rfl | rfl | rfl | rfl <;> decide)
      (by
        intro a ha' t ht
        simp [RamCertificateSource.arrays] at ha'
        simp [RamCopy.suffixes] at ht
        rcases ha' with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;> decide))
    (fun σ z h => context_setVar P r s σ "build.i" z (by decide) h)
    (fun σ z h => context_setVar P r s σ "vec.i" z (by decide) h)
    (fun σ z h => context_setVar P r s σ "vec.n" z (by decide) h)
  have hmeta : Spec B (fun σ => σ.vars "system.m" = r ∧ σ.vars "system.n" = s) prepare
      (fun _ τ => τ.vars "build.count" = r * s) 4 := by
    rintro σ ⟨hr, hs⟩
    run_vcg
    all_goals simp_all
    all_goals omega
  rintro σ ⟨hσContext, hσtarget⟩
  obtain ⟨τ, hr₁, hτcount⟩ := hmeta σ hσContext.2
  have hτContext := context_frame hr₁ P r s hσContext
    (by intro a ha'; simp [fields] at ha'; rcases ha' with rfl | rfl | rfl | rfl <;> decide)
    (by intro a ha' t ht; simp [prepare, Com.warrs])
  obtain ⟨υ, hr₂, hυContext, hυtarget, hυcount⟩ := hbuild τ
    ⟨hτContext, RamAdvanceState.extents_of_run hr₁ "system.A" (r * s) hσtarget, hτcount⟩
  refine ⟨υ, (hr₁.seq hr₂).mono ?_, hυContext, ?_⟩
  · simp only [Nat.add_assoc, Nat.reduceAdd]; omega
  · exact hυtarget

end Lax109476Proofs.RamCertificateMatrix

import Lax109476Proofs.RamCertificateContext
import Lax109476Proofs.RamBuildVector

namespace Lax109476Proofs.RamCertificateBound

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds IntegerEncoding RamEllipsoidStep
open RamCertificateContext

def selectCoordinate (selector : Com) : Com := .seq (.assign "query.row" (.var "build.i")) selector

theorem selectCoordinate_spec (B m n r s selectorCost : ℕ) (P : Program ℤ m n) (F : Program ℤ r s)
    (selector : Com) (hrB : r < B)
    (hselector : ∀ i, Spec B (fun σ => RamCertificateSource.Data P σ ∧ σ.vars "query.row" = i.val)
      selector (fun _ τ => RamCertificateSource.Data P τ ∧ FractionOutput (F.b i : ℚ) τ) selectorCost)
    (hf : ∀ a ∈ fields, a ∉ selector.wvars) (i : Fin r) :
    Spec B (fun σ => Context P r s σ ∧ σ.vars "build.i" = i.val ∧ σ.vars "build.count" = r)
      (selectCoordinate selector) (fun _ τ => Context P r s τ ∧ FractionOutput (F.b i : ℚ) τ)
      (selectorCost + 2) := by
  rintro σ ⟨hσContext, hσi, hσcount⟩
  have hr₁ : Run B (.assign "query.row" (.var "build.i")) σ (σ.setVar "query.row" i.val) 2 :=
    Run.assign (by simpa only [hσi] using evalB_var (B := B) (σ := σ) (x := "build.i") (hσi ▸ i.isLt.trans hrB))
  have hτContext := context_setVar P r s σ "query.row" i.val (by decide) hσContext
  obtain ⟨υ, hr₂, hυData, hυq⟩ := hselector i (σ.setVar "query.row" i.val) ⟨hτContext.1, by simp⟩
  refine ⟨υ, (hr₁.seq hr₂).mono (by omega), ⟨hυData, ?_, ?_⟩, hυq⟩
  · exact (hr₂.frame_var _ (hf _ (by simp [fields]))).trans hτContext.2.1
  · exact (hr₂.frame_var _ (hf _ (by simp [fields]))).trans hτContext.2.2

def prepare : Com := .assign "build.count" (.var "system.m")
def buildBound (selector : Com) : Com := .seq prepare (RamBuildVector.build "system.b" (selectCoordinate selector))

set_option maxHeartbeats 1000000 in
theorem buildBound_spec (B M m n r s selectorCost : ℕ) (P : Program ℤ m n) (F : Program ℤ r s)
    (selector : Com) (h1 : 1 < B) (hMB : M < B) (hrB : r < B)
    (hb : ∀ i, Height (F.b i : ℚ) M)
    (hselector : ∀ i, Spec B (fun σ => RamCertificateSource.Data P σ ∧ σ.vars "query.row" = i.val)
      selector (fun _ τ => RamCertificateSource.Data P τ ∧ FractionOutput (F.b i : ℚ) τ) selectorCost)
    (hf : ∀ a ∈ fields, a ∉ selector.wvars)
    (hiFrame : "build.i" ∉ selector.wvars) (hnFrame : "build.count" ∉ selector.wvars)
    (htarget : ∀ t ∈ RamCopy.suffixes, "system.b" ++ t ∉ selector.warrs) :
    Spec B (fun σ => Context P r s σ ∧ Extents "system.b" r σ) (buildBound selector)
      (fun _ τ => Context P r s τ ∧ Represents "system.b" (List.ofFn (rationalProgram F).b) τ)
      ((selectorCost + 58) * r + 28) := by
  have hbuild := RamBuildVector.build_spec B M r (selectorCost + 2) "system.b" (rationalProgram F).b
    (selectCoordinate selector) (Context P r s) h1 hrB hMB hb
    (selectCoordinate_spec B m n r s selectorCost P F selector hrB hselector hf)
    (by simpa [selectCoordinate, Com.wvars] using hiFrame)
    (by simpa [selectCoordinate, Com.wvars] using hnFrame)
    (by simpa [selectCoordinate, Com.warrs] using htarget)
    (preserves_context B P r s (storeReduced "system.b")
      (by intro a ha; simp [fields] at ha; rcases ha with rfl | rfl | rfl | rfl <;> decide)
      (by
        intro a ha t ht
        simp [RamCertificateSource.arrays] at ha
        simp [RamCopy.suffixes] at ht
        rcases ha with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;> decide))
    (preserves_context B P r s (RamZeroArray.zeroRationalArray "system.b")
      (by intro a ha; simp [fields] at ha; rcases ha with rfl | rfl | rfl | rfl <;> decide)
      (by
        intro a ha t ht
        simp [RamCertificateSource.arrays] at ha
        simp [RamCopy.suffixes] at ht
        rcases ha with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;> decide))
    (fun σ z h => context_setVar P r s σ "build.i" z (by decide) h)
    (fun σ z h => context_setVar P r s σ "vec.i" z (by decide) h)
    (fun σ z h => context_setVar P r s σ "vec.n" z (by decide) h)
  have hmeta : Spec B (fun σ => σ.vars "system.m" = r) prepare
      (fun _ τ => τ.vars "build.count" = r) 2 := by
    intro σ hr
    refine ⟨σ.setVar "build.count" r, ?_, by simp⟩
    exact Run.assign (by simpa only [hr] using evalB_var (B := B) (σ := σ) (x := "system.m") (hr ▸ hrB))
  rintro σ ⟨hσContext, hσtarget⟩
  obtain ⟨τ, hr₁, hτcount⟩ := hmeta σ hσContext.2.1
  have hτContext := context_frame hr₁ P r s hσContext
    (by intro a ha; simp [fields] at ha; rcases ha with rfl | rfl | rfl | rfl <;> decide)
    (by intro a ha t ht; simp [prepare, Com.warrs])
  obtain ⟨υ, hr₂, hυContext, hυtarget, hυcount⟩ := hbuild τ
    ⟨hτContext, RamAdvanceState.extents_of_run hr₁ "system.b" r hσtarget, hτcount⟩
  exact ⟨υ, (hr₁.seq hr₂).mono (by simp only [Nat.add_assoc, Nat.reduceAdd]; omega), hυContext, hυtarget⟩

end Lax109476Proofs.RamCertificateBound

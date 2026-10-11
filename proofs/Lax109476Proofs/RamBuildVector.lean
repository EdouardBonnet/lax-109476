import Lax109476Proofs.RamBisectionLoop
import Lax109476Proofs.RamReadBody

namespace Lax109476Proofs.RamBuildVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamCenterUpdate RamEllipsoidStep RationalArithmeticBounds

def coordinate (a : String) (selector : Com) : Com := .seq selector
  (.seq (.assign "vec.i" (.var "build.i")) (storeReduced a))

def step (a : String) (selector : Com) : Com := .seq (coordinate a selector)
  (.assign "build.i" (.add (.var "build.i") (.lit 1)))

def Invariant {n : ℕ} (a : String) (v : Fin n → ℚ) (Q : Env → Prop) (σ : Env) : Prop :=
  Q σ ∧ Represents a (filled v (σ.vars "build.i")) σ ∧
    σ.vars "build.i" ≤ n ∧ σ.vars "build.count" = n

set_option maxHeartbeats 800000 in
theorem step_spec (B M n selectorCost : ℕ) (a : String) (v : Fin n → ℚ)
    (selector : Com) (Q : Env → Prop) (h1 : 1 < B) (hnB : n < B) (hMB : M < B)
    (hv : ∀ i, Height (v i) M)
    (hselector : ∀ i : Fin n, Spec B (fun σ => Q σ ∧ σ.vars "build.i" = i.val ∧ σ.vars "build.count" = n)
      selector (fun _ τ => Q τ ∧ FractionOutput (v i) τ) selectorCost)
    (hiFrame : "build.i" ∉ selector.wvars) (hnFrame : "build.count" ∉ selector.wvars)
    (haFrame : ∀ s ∈ RamCopy.suffixes, a ++ s ∉ selector.warrs)
    (hQstore : RamBisectionLoop.preserves B Q (storeReduced a))
    (hQset : ∀ σ t, Q σ → Q (σ.setVar "build.i" t))
    (hQvec : ∀ σ t, Q σ → Q (σ.setVar "vec.i" t)) :
    Spec B (fun σ => Invariant a v Q σ ∧ σ.vars "build.i" < n) (step a selector)
      (fun σ τ => Invariant a v Q τ ∧ τ.vars "build.i" = σ.vars "build.i" + 1)
      (selectorCost + 19) := by
  rintro σ ⟨⟨hσQ, hσa, hσi, hσn⟩, hi⟩
  let i : Fin n := ⟨σ.vars "build.i", hi⟩
  obtain ⟨τ, hr₁, hτQ, hτv⟩ := hselector i σ ⟨hσQ, rfl, hσn⟩
  have hτi : τ.vars "build.i" = i.val := hr₁.frame_var _ hiFrame
  have hτa : Represents a (filled v i.val) τ := RamReadBody.represents_frame _ _ hσa hr₁ haFrame
  have hiB : i.val < B := i.isLt.trans hnB
  have hr₂ : Run B (.assign "vec.i" (.var "build.i")) τ (τ.setVar "vec.i" i.val) 2 :=
    Run.assign (by simpa only [hτi] using evalB_var (B := B) (σ := τ) (x := "build.i") (hτi ▸ hiB))
  have hstore := storeReduced_spec B a (filled v i.val) (v i) i.val
    (by simpa only [filled, List.length_ofFn] using i.isLt) h1 hiB
    ((hv i).1.trans_lt hMB) ((hv i).2.trans_lt hMB)
  obtain ⟨υ, hr₃, hυa⟩ := hstore (τ.setVar "vec.i" i.val)
    ⟨hτa, by simp, by simpa [FractionOutput, vars_setVar] using hτv⟩
  have hυQ : Q υ := hQstore hr₃ (hQvec τ i.val hτQ)
  have hυi : υ.vars "build.i" = i.val :=
    (hr₃.frame_var _ (by simp [storeReduced, Com.wvars])).trans (by simpa using hτi)
  have hsumB : Bop.add.apply (υ.vars "build.i") 1 < B := by simpa [hυi] using lt_of_le_of_lt i.isLt hnB
  have hr₄ : Run B (.assign "build.i" (.add (.var "build.i") (.lit 1))) υ (υ.setVar "build.i" (i.val + 1)) 4 :=
    Run.assign (by simpa only [hυi, Bop.apply_add] using (evalB_bin
      (evalB_var (B := B) (σ := υ) (x := "build.i") (hυi ▸ hiB)) (evalB_lit h1) hsumB))
  have hr := (hr₁.seq (hr₂.seq hr₃)).seq hr₄
  have hfilled : Represents a (filled v (i.val + 1)) υ := by rw [← filled_step]; exact hυa
  refine ⟨_, hr.mono (by omega), ⟨hQset υ (i.val + 1) hυQ, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Represents, arrs_setVar, vars_setVar, ite_true] using hfilled
  · change i.val + 1 ≤ n; exact i.isLt
  · exact (hr.frame_var _ (by simp [Com.wvars, storeReduced, hnFrame])).trans hσn
  · simp [i]

def loop (a : String) (selector : Com) : Com := .seq (.assign "build.i" (.lit 0))
  (.while (.lt (.var "build.i") (.var "build.count")) (step a selector))

theorem loop_spec (B M n selectorCost : ℕ) (a : String) (v : Fin n → ℚ)
    (selector : Com) (Q : Env → Prop) (h1 : 1 < B) (hnB : n < B) (hMB : M < B)
    (hv : ∀ i, Height (v i) M)
    (hselector : ∀ i : Fin n, Spec B (fun σ => Q σ ∧ σ.vars "build.i" = i.val ∧ σ.vars "build.count" = n)
      selector (fun _ τ => Q τ ∧ FractionOutput (v i) τ) selectorCost)
    (hiFrame : "build.i" ∉ selector.wvars) (hnFrame : "build.count" ∉ selector.wvars)
    (haFrame : ∀ s ∈ RamCopy.suffixes, a ++ s ∉ selector.warrs)
    (hQstore : RamBisectionLoop.preserves B Q (storeReduced a))
    (hQset : ∀ σ t, Q σ → Q (σ.setVar "build.i" t))
    (hQvec : ∀ σ t, Q σ → Q (σ.setVar "vec.i" t)) :
    Spec B (fun σ => Q σ ∧ Represents a (List.replicate n 0) σ ∧ σ.vars "build.count" = n)
      (loop a selector) (fun _ τ => Q τ ∧ Represents a (List.ofFn v) τ ∧ τ.vars "build.count" = n)
      ((selectorCost + 23) * n + 6) := by
  have hlo := Spec.forRangeZero "build.i" "build.count" (Invariant a v Q) n (selectorCost + 19) hnB
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2)
    (step_spec B M n selectorCost a v selector Q h1 hnB hMB hv hselector hiFrame hnFrame haFrame hQstore hQset hQvec)
  refine ((hlo.pre ?_).post ?_).mono (by simp only [Nat.add_assoc, Nat.reduceAdd]; omega)
  · rintro σ ⟨hσQ, hσa, hσn⟩
    exact ⟨hQset σ 0 hσQ, by simpa only [Represents, arrs_setVar, vars_setVar, ite_true, filled_zero] using hσa, by simp, by simpa using hσn⟩
  · rintro σ τ _ ⟨hτ, hcounter⟩
    exact ⟨hτ.1, by simpa only [hcounter, filled_done] using hτ.2.1, hτ.2.2.2⟩

def build (a : String) (selector : Com) : Com := .seq (.assign "vec.n" (.var "build.count"))
  (.seq (RamZeroArray.zeroRationalArray a) (loop a selector))

theorem build_spec (B M n selectorCost : ℕ) (a : String) (v : Fin n → ℚ)
    (selector : Com) (Q : Env → Prop) (h1 : 1 < B) (hnB : n < B) (hMB : M < B)
    (hv : ∀ i, Height (v i) M)
    (hselector : ∀ i : Fin n, Spec B (fun σ => Q σ ∧ σ.vars "build.i" = i.val ∧ σ.vars "build.count" = n)
      selector (fun _ τ => Q τ ∧ FractionOutput (v i) τ) selectorCost)
    (hiFrame : "build.i" ∉ selector.wvars) (hnFrame : "build.count" ∉ selector.wvars)
    (haFrame : ∀ s ∈ RamCopy.suffixes, a ++ s ∉ selector.warrs)
    (hQstore : RamBisectionLoop.preserves B Q (storeReduced a))
    (hQzero : RamBisectionLoop.preserves B Q (RamZeroArray.zeroRationalArray a))
    (hQset : ∀ σ t, Q σ → Q (σ.setVar "build.i" t))
    (hQvec : ∀ σ t, Q σ → Q (σ.setVar "vec.i" t))
    (hQlength : ∀ σ t, Q σ → Q (σ.setVar "vec.n" t)) :
    Spec B (fun σ => Q σ ∧ Extents a n σ ∧ σ.vars "build.count" = n)
      (build a selector) (fun _ τ => Q τ ∧ Represents a (List.ofFn v) τ ∧ τ.vars "build.count" = n)
      ((selectorCost + 56) * n + 26) := by
  rintro σ ⟨hσQ, hσa, hσn⟩
  have hr₁ : Run B (.assign "vec.n" (.var "build.count")) σ (σ.setVar "vec.n" n) 2 :=
    Run.assign (by simpa only [hσn] using evalB_var (B := B) (σ := σ) (x := "build.count") (hσn ▸ hnB))
  obtain ⟨τ, hr₂, hτa, hτn, hτframe⟩ := RamZeroArray.zeroRationalArray_spec B n a hnB h1
    (σ.setVar "vec.n" n) ⟨hσa ".s" (by simp), hσa ".n" (by simp), hσa ".d" (by simp), by simp⟩
  have hτQ := hQzero hr₂ (hQlength σ n hσQ)
  have hτcount : τ.vars "build.count" = n :=
    (hr₂.frame_var _ (by simp [RamZeroArray.zeroRationalArray, RamZeroArray.fillConstant, Com.wvars, Lib.Fill.put])).trans
      (by simpa using hσn)
  obtain ⟨υ, hr₃, hυ⟩ := loop_spec B M n selectorCost a v selector Q h1 hnB hMB hv hselector
    hiFrame hnFrame haFrame hQstore hQset hQvec τ ⟨hτQ, hτa, hτcount⟩
  refine ⟨υ, (hr₁.seq (hr₂.seq hr₃)).mono ?_, hυ⟩
  simp only [Nat.add_mul]
  omega

end Lax109476Proofs.RamBuildVector

import Lax109476Proofs.RamCenterUpdate

namespace Lax109476Proofs.RamCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds

def suffixes : List String := [".s", ".n", ".d"]
def Disjoint (a b : String) : Prop := ∀ s ∈ suffixes, ∀ t ∈ suffixes, a ++ s ≠ b ++ t

theorem disjoint_not_mem (a b s : String) (hab : Disjoint a b) (hs : s ∈ suffixes) :
    a ++ s ∉ [b ++ ".s", b ++ ".n", b ++ ".d"] := by
  intro h
  simp at h
  rcases h with h | h | h
  · exact hab s hs ".s" (by simp [suffixes]) h
  · exact hab s hs ".n" (by simp [suffixes]) h
  · exact hab s hs ".d" (by simp [suffixes]) h

def loopFields : List String := ["copy.i", "vec.i", "vec.n"]

def leftToResult : Com :=
  .seq (.assign "rat.s" (.var "left.s"))
    (.seq (.assign "rat.n" (.var "left.n")) (.assign "rat.d" (.var "left.d")))

theorem leftToResult_spec (B : ℕ) (q : ℚ) (h1 : 1 < B)
    (hn : q.num.natAbs < B) (hd : q.den < B) :
    Spec B (LeftOutput q) leftToResult (fun _ τ => FractionOutput q τ) 6 := by
  rintro σ ⟨hσs, hσn, hσd⟩
  have hs : σ.vars "left.s" < B := hσs ▸ (rationalSign_le_one q).trans_lt h1
  run_vcg
  all_goals simp_all [FractionOutput, canonical_fractionValue, rationalSign_le_one]

def copyCoordinate (a b : String) : Com :=
  .seq (.assign "vec.i" (.var "copy.i"))
    (.seq (loadLeft a) (.seq leftToResult (storeReduced b)))

set_option maxHeartbeats 500000 in
theorem copyCoordinate_spec (B M i : ℕ) (a b : String) (xs ys : List ℚ)
    (hi : i < xs.length) (hiy : i < ys.length) (hiB : i < B) (h1 : 1 < B)
    (hMB : M < B) (hq : Height xs[i] M) (hab : Disjoint a b) :
    Spec B (fun σ => Represents a xs σ ∧ Represents b ys σ ∧ σ.vars "copy.i" = i)
      (copyCoordinate a b)
      (fun _ τ => Represents b (ys.set i xs[i]) τ ∧ Represents a xs τ) 30 := by
  have hload := spec_with_fields loopFields
    (loadLeft_spec B a xs i hi h1 hiB (hq.1.trans_lt hMB) (hq.2.trans_lt hMB))
    (by intro x hx; simp [loopFields] at hx; rcases hx with rfl | rfl | rfl <;> simp [loadLeft, Com.wvars])
    (by simp [loadLeft, Com.warrs])
  have hresult := spec_with_fields loopFields
    (leftToResult_spec B xs[i] h1 (hq.1.trans_lt hMB) (hq.2.trans_lt hMB))
    (by intro x hx; simp [loopFields] at hx; rcases hx with rfl | rfl | rfl <;> simp [leftToResult, Com.wvars])
    (by simp [leftToResult, Com.warrs])
  have hstore := spec_with_write_frame loopFields
    (storeReduced_spec B b ys xs[i] i hiy h1 hiB (hq.1.trans_lt hMB) (hq.2.trans_lt hMB))
    (by intro x hx; simp [loopFields] at hx; rcases hx with rfl | rfl | rfl <;> simp [storeReduced, Com.wvars])
  rintro σ ⟨hσa, hσb, hσi⟩
  run_vcg [hload, hresult, hstore]
  all_goals clear hload hresult hstore
  all_goals simp_all [Disjoint, suffixes, LeftOutput, FractionOutput, Represents, FieldsAgree, loopFields,
    storeReduced, Com.warrs]
  all_goals aesop

def CopyInvariant {n : ℕ} (a b : String) (v : Fin n → ℚ) (σ : Env) : Prop :=
  Represents a (List.ofFn v) σ ∧
    Represents b (RamCenterUpdate.filled v (σ.vars "copy.i")) σ ∧
    σ.vars "copy.i" ≤ n ∧ σ.vars "vec.n" = n

def copyStep (a b : String) : Com :=
  .seq (copyCoordinate a b) (.assign "copy.i" (.add (.var "copy.i") (.lit 1)))

theorem copyStep_spec (B n M : ℕ) (a b : String) (v : Fin n → ℚ)
    (h1 : 1 < B) (hnB : n < B) (hMB : M < B) (hv : ∀ i, Height (v i) M) (hab : Disjoint a b) :
    Spec B (fun σ => CopyInvariant a b v σ ∧ σ.vars "copy.i" < n) (copyStep a b)
      (fun σ τ => CopyInvariant a b v τ ∧ τ.vars "copy.i" = σ.vars "copy.i" + 1) 34 := by
  rintro σ ⟨⟨hσa, hσb, hσiN, hσn⟩, hσi⟩
  let i : Fin n := ⟨σ.vars "copy.i", hσi⟩
  have hvi : Height (List.ofFn v)[i.val] M := by simpa using hv i
  obtain ⟨τ, hr₁, hτb, hτa⟩ := copyCoordinate_spec B M i.val a b (List.ofFn v)
    (RamCenterUpdate.filled v i.val) (by simp) (by simp [RamCenterUpdate.filled])
    (i.isLt.trans hnB) h1 hMB hvi hab σ ⟨hσa, hσb, rfl⟩
  have hτi : τ.vars "copy.i" = i.val := hr₁.frame_var _ (by
    simp [copyCoordinate, leftToResult, loadLeft, storeReduced, Com.wvars])
  have hτn : τ.vars "vec.n" = n := (hr₁.frame_var "vec.n" (by
    simp [copyCoordinate, leftToResult, loadLeft, storeReduced, Com.wvars])).trans hσn
  have hτiB : τ.vars "copy.i" < B := hτi ▸ i.isLt.trans hnB
  have hsumB : Bop.add.apply (τ.vars "copy.i") 1 < B := by
    simpa [Bop.apply, hτi] using lt_of_le_of_lt i.isLt hnB
  have hr₂ : Run B (.assign "copy.i" (.add (.var "copy.i") (.lit 1))) τ
      (τ.setVar "copy.i" (i.val + 1)) 4 := by
    exact Run.assign (by simpa [Bop.apply, hτi] using
      (evalB_bin (evalB_var hτiB) (evalB_lit h1) hsumB))
  have hnext : Represents b (RamCenterUpdate.filled v (i.val + 1)) τ := by
    rw [← RamCenterUpdate.filled_step]
    simpa only [List.getElem_ofFn, Fin.eta] using hτb
  refine ⟨_, hr₁.seq hr₂, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Represents, arrs_setVar] using hτa
  · simpa only [Represents, arrs_setVar, vars_setVar, ite_true] using hnext
  · change i.val + 1 ≤ n
    exact i.isLt
  · simpa using hτn
  · simp [i]

def copyLoop (a b : String) : Com :=
  .seq (.assign "copy.i" (.lit 0)) (.while (.lt (.var "copy.i") (.var "vec.n")) (copyStep a b))

theorem copyLoop_spec (B n M : ℕ) (a b : String) (v : Fin n → ℚ)
    (h1 : 1 < B) (hnB : n < B) (hMB : M < B) (hv : ∀ i, Height (v i) M) (hab : Disjoint a b) :
    Spec B (fun σ => Represents a (List.ofFn v) σ ∧ Represents b (List.replicate n 0) σ ∧ σ.vars "vec.n" = n)
      (copyLoop a b)
      (fun _ τ => Represents b (List.ofFn v) τ ∧ Represents a (List.ofFn v) τ ∧ τ.vars "vec.n" = n)
      (38 * n + 6) := by
  have hlo := Spec.forRangeZero "copy.i" "vec.n" (CopyInvariant a b v) n 34 hnB
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2) (copyStep_spec B n M a b v h1 hnB hMB hv hab)
  refine (hlo.pre ?_).post ?_
  · rintro σ ⟨hσa, hσb, hσn⟩
    simp_all [CopyInvariant, Represents, RamCenterUpdate.filled_zero]
  · rintro σ τ _ ⟨hτ, hcounter⟩
    refine ⟨?_, hτ.1, hτ.2.2.2⟩
    simpa only [hcounter, RamCenterUpdate.filled_done] using hτ.2.1

def copyRationalArray (a b : String) : Com := .seq (RamZeroArray.zeroRationalArray b) (copyLoop a b)

theorem copyRationalArray_spec (B n M : ℕ) (a b : String) (v : Fin n → ℚ)
    (h1 : 1 < B) (hnB : n < B) (hMB : M < B) (hv : ∀ i, Height (v i) M) (hab : Disjoint a b) :
    Spec B (fun σ => Represents a (List.ofFn v) σ ∧ (σ.arrs (b ++ ".s")).length = n ∧
        (σ.arrs (b ++ ".n")).length = n ∧ (σ.arrs (b ++ ".d")).length = n ∧ σ.vars "vec.n" = n)
      (copyRationalArray a b)
      (fun _ τ => Represents b (List.ofFn v) τ ∧ Represents a (List.ofFn v) τ ∧ τ.vars "vec.n" = n)
      (71 * n + 24) := by
  rintro σ ⟨hσa, hσs, hσn, hσd, hσN⟩
  obtain ⟨τ, hr₁, hτb, hτN, hτarr⟩ := RamZeroArray.zeroRationalArray_spec B n b hnB h1 σ ⟨hσs, hσn, hσd, hσN⟩
  have hτa : Represents a (List.ofFn v) τ := by
    simpa only [Represents, hτarr (a ++ ".s") (disjoint_not_mem a b _ hab (by simp [suffixes])),
      hτarr (a ++ ".n") (disjoint_not_mem a b _ hab (by simp [suffixes])),
      hτarr (a ++ ".d") (disjoint_not_mem a b _ hab (by simp [suffixes]))] using hσa
  obtain ⟨υ, hr₂, hυ⟩ := copyLoop_spec B n M a b v h1 hnB hMB hv hab τ ⟨hτa, hτb, hτN⟩
  exact ⟨υ, (hr₁.seq hr₂).mono (by omega), hυ⟩

end Lax109476Proofs.RamCopy

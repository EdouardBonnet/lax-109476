import Lax109476Proofs.RamCopy
import Lax109476Proofs.RamMatrixRows

namespace Lax109476Proofs.RamRowCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds RamMatrixRows
open RamCopy RamCenterUpdate RamZeroArray

def loopFields : List String := ["copy.i", "vec.i", "vec.n", "row.base"]

def copyCoordinate (a b : String) : Com := .seq (.assign "vec.i" (.var "copy.i"))
  (.seq (loadRowLeft a) (.seq leftToResult (storeReduced b)))

set_option maxHeartbeats 700000 in
theorem copyCoordinate_spec (B M base i : ℕ) (a b : String) (xs ys : List ℚ)
    (hi : i < xs.length) (hiy : i < ys.length) (hiB : base + i < B) (h1 : 1 < B)
    (hMB : M < B) (hq : Height xs[i] M) (hab : RamCopy.Disjoint a b) :
    Spec B (fun σ => Slice a xs base σ ∧ Represents b ys σ ∧
        σ.vars "copy.i" = i ∧ σ.vars "row.base" = base)
      (copyCoordinate a b)
      (fun _ τ => Represents b (ys.set i xs[i]) τ ∧ Slice a xs base τ) 36 := by
  have hiB' : i < B := by omega
  have hload := spec_with_fields loopFields
    (loadRowLeft_spec B base i a xs hi h1 hiB (hq.1.trans_lt hMB) (hq.2.trans_lt hMB))
    (by intro x hx; simp [loopFields] at hx; rcases hx with rfl | rfl | rfl | rfl <;>
      simp [loadRowLeft, Com.wvars]) (by simp [loadRowLeft, Com.warrs])
  have hresult := spec_with_fields loopFields
    (leftToResult_spec B xs[i] h1 (hq.1.trans_lt hMB) (hq.2.trans_lt hMB))
    (by intro x hx; simp [loopFields] at hx; rcases hx with rfl | rfl | rfl | rfl <;>
      simp [leftToResult, Com.wvars]) (by simp [leftToResult, Com.warrs])
  have hstore := spec_with_write_frame loopFields
    (storeReduced_spec B b ys xs[i] i hiy h1 hiB' (hq.1.trans_lt hMB) (hq.2.trans_lt hMB))
    (by intro x hx; simp [loopFields] at hx; rcases hx with rfl | rfl | rfl | rfl <;>
      simp [storeReduced, Com.wvars])
  rintro σ ⟨hσa, hσb, hσi, hσbase⟩
  run_vcg [hload, hresult, hstore]
  all_goals clear hload hresult hstore
  all_goals simp_all [RamCopy.Disjoint, suffixes, LeftOutput, FractionOutput, Represents,
    Slice, FieldsAgree, loopFields, storeReduced, Com.warrs]
  all_goals aesop

def CopyInvariant {n : ℕ} (a b : String) (v : Fin n → ℚ) (base : ℕ) (σ : Env) : Prop :=
  Slice a (List.ofFn v) base σ ∧ Represents b (filled v (σ.vars "copy.i")) σ ∧
    σ.vars "copy.i" ≤ n ∧ σ.vars "vec.n" = n ∧ σ.vars "row.base" = base

def copyStep (a b : String) : Com := .seq (copyCoordinate a b)
  (.assign "copy.i" (.add (.var "copy.i") (.lit 1)))

theorem copyStep_spec (B n M base : ℕ) (a b : String) (v : Fin n → ℚ)
    (h1 : 1 < B) (hnB : base + n < B) (hMB : M < B)
    (hv : ∀ i, Height (v i) M) (hab : RamCopy.Disjoint a b) :
    Spec B (fun σ => CopyInvariant a b v base σ ∧ σ.vars "copy.i" < n) (copyStep a b)
      (fun σ τ => CopyInvariant a b v base τ ∧ τ.vars "copy.i" = σ.vars "copy.i" + 1) 40 := by
  rintro σ ⟨⟨hσa, hσb, hσiN, hσn, hσbase⟩, hσi⟩
  let i : Fin n := ⟨σ.vars "copy.i", hσi⟩
  have hiB : base + i.val < B := by have := i.isLt; omega
  have hvi : Height (List.ofFn v)[i.val] M := by simpa using hv i
  obtain ⟨τ, hr₁, hτb, hτa⟩ := copyCoordinate_spec B M base i.val a b (List.ofFn v)
    (filled v i.val) (by simp) (by simp [filled]) hiB h1 hMB hvi hab
    σ ⟨hσa, hσb, rfl, hσbase⟩
  have hτi : τ.vars "copy.i" = i.val := hr₁.frame_var _ (by
    simp [copyCoordinate, loadRowLeft, leftToResult, storeReduced, Com.wvars])
  have hτn : τ.vars "vec.n" = n := (hr₁.frame_var _ (by
    simp [copyCoordinate, loadRowLeft, leftToResult, storeReduced, Com.wvars])).trans hσn
  have hτbase : τ.vars "row.base" = base := (hr₁.frame_var _ (by
    simp [copyCoordinate, loadRowLeft, leftToResult, storeReduced, Com.wvars])).trans hσbase
  have hsumB : Bop.add.apply (τ.vars "copy.i") 1 < B := by
    simp only [Bop.apply, hτi]
    have := i.isLt
    omega
  have hiB' : i.val < B := by omega
  have hr₂ : Run B (.assign "copy.i" (.add (.var "copy.i") (.lit 1))) τ
      (τ.setVar "copy.i" (i.val + 1)) 4 := by
    exact Run.assign (by simpa [Bop.apply, hτi] using
      (evalB_bin (evalB_var (hτi ▸ hiB')) (evalB_lit h1) hsumB))
  have hnext : Represents b (filled v (i.val + 1)) τ := by
    rw [← filled_step]
    simpa only [List.getElem_ofFn, Fin.eta] using hτb
  refine ⟨_, hr₁.seq hr₂, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Slice, arrs_setVar] using hτa
  · simpa only [Represents, arrs_setVar, vars_setVar, ite_true] using hnext
  · change i.val + 1 ≤ n
    exact i.isLt
  · simpa using hτn
  · simpa using hτbase
  · simp [i]

def copyLoop (a b : String) : Com := .seq (.assign "copy.i" (.lit 0))
  (.while (.lt (.var "copy.i") (.var "vec.n")) (copyStep a b))

theorem copyLoop_spec (B n M base : ℕ) (a b : String) (v : Fin n → ℚ)
    (h1 : 1 < B) (hnB : base + n < B) (hMB : M < B)
    (hv : ∀ i, Height (v i) M) (hab : RamCopy.Disjoint a b) :
    Spec B (fun σ => Slice a (List.ofFn v) base σ ∧ Represents b (List.replicate n 0) σ ∧
        σ.vars "vec.n" = n ∧ σ.vars "row.base" = base)
      (copyLoop a b)
      (fun _ τ => Represents b (List.ofFn v) τ ∧ Slice a (List.ofFn v) base τ ∧
        τ.vars "vec.n" = n ∧ τ.vars "row.base" = base) (44 * n + 6) := by
  have hnB' : n < B := by omega
  have hlo := Spec.forRangeZero "copy.i" "vec.n" (CopyInvariant a b v base) n 40 hnB'
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2.1)
    (copyStep_spec B n M base a b v h1 hnB hMB hv hab)
  refine (hlo.pre ?_).post ?_
  · rintro σ ⟨ha, hb, hn, hbase⟩
    simp_all [CopyInvariant, Slice, Represents, filled_zero]
  · rintro σ τ _ ⟨hτ, hi⟩
    refine ⟨?_, hτ.1, hτ.2.2.2.1, hτ.2.2.2.2⟩
    simpa only [hi, filled_done] using hτ.2.1

def copyRow (a b : String) : Com := .seq (zeroRationalArray b) (copyLoop a b)

theorem copyRow_spec (B n M base : ℕ) (a b : String) (v : Fin n → ℚ)
    (h1 : 1 < B) (hnB : base + n < B) (hMB : M < B)
    (hv : ∀ i, Height (v i) M) (hab : RamCopy.Disjoint a b) :
    Spec B (fun σ => Slice a (List.ofFn v) base σ ∧ (σ.arrs (b ++ ".s")).length = n ∧
        (σ.arrs (b ++ ".n")).length = n ∧ (σ.arrs (b ++ ".d")).length = n ∧
        σ.vars "vec.n" = n ∧ σ.vars "row.base" = base)
      (copyRow a b)
      (fun _ τ => Represents b (List.ofFn v) τ ∧ Slice a (List.ofFn v) base τ ∧
        τ.vars "vec.n" = n ∧ τ.vars "row.base" = base) (77 * n + 24) := by
  have hnB' : n < B := by omega
  have hz := spec_with_write_frame ["row.base"] (zeroRationalArray_spec B n b hnB' h1)
    (by intro x hx; simp at hx; subst x; simp [zeroRationalArray, fillConstant, Lib.Fill.put, Com.wvars])
  have hc := copyLoop_spec B n M base a b v h1 hnB hMB hv hab
  rintro σ ⟨ha, hs, hnum, hd, hn, hbase⟩
  run_vcg [hz, hc]
  all_goals clear hz hc
  all_goals simp_all [Slice, FieldsAgree, RamCopy.Disjoint, suffixes]
  all_goals aesop

end Lax109476Proofs.RamRowCopy

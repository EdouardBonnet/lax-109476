import Lax109476Proofs.RamPadMatrix

namespace Lax109476Proofs.RamPadBound

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds RamCenterUpdate RamEllipsoidStep

def value {m n : ℕ} (P : Program ℚ m n) (i : Fin (m + 2)) : ℚ :=
  if hi : i.val < m then P.b ⟨i.val, hi⟩ else 0

theorem value_eq {m n : ℕ} (P : Program ℚ m n) (i : Fin (m + 2)) :
    value P i = (FeasibilityPadding.pad P).b i := by
  refine Fin.addCases ?_ ?_ i
  · intro i
    simp [value, FeasibilityPadding.pad, i.isLt]
  · intro i
    simp [value, FeasibilityPadding.pad]

theorem value_height {m n : ℕ} (P : Program ℚ m n) (M : ℕ) (hM : 1 ≤ M)
    (hb : ∀ i, Height (P.b i) M) (i : Fin (m + 2)) : Height (value P i) M := by
  unfold value
  split_ifs
  · exact hb _
  · simpa [Height] using hM

def selectBound : Com := .ite (.lt (.var "pad.k") (.var "source.m"))
  (.seq (.assign "vec.i" (.var "pad.k")) (.seq (loadLeft "query.b") RamCopy.leftToResult))
  (RamPadSelector.constantFraction 0)

set_option maxHeartbeats 600000 in
theorem selectBound_spec (B M m n : ℕ) (P : Program ℚ m n) (i : Fin (m + 2))
    (hM : 1 ≤ M) (hMB : M < B) (hmB : m + 2 < B) (hb : ∀ i, Height (P.b i) M) :
    Spec B (fun σ => Represents "query.b" (List.ofFn P.b) σ ∧
        σ.vars "source.m" = m ∧ σ.vars "pad.k" = i.val)
      selectBound (fun _ τ => FractionOutput (value P i) τ) 21 := by
  have h1 : 1 < B := hM.trans_lt hMB
  have hiB : i.val < B := i.isLt.trans hmB
  have hm : m < B := by omega
  have hzero := RamPadSelector.constantFraction_spec B 0 h1 (by omega)
  rintro σ ⟨hσb, hσm, hσi⟩
  by_cases hi : i.val < m
  · let ii : Fin m := ⟨i.val, hi⟩
    have hq := hb ii
    have hload := loadLeft_spec B "query.b" (List.ofFn P.b) i.val (by simpa using hi)
      h1 hiB (by simpa [ii] using hq.1.trans_lt hMB) (by simpa [ii] using hq.2.trans_lt hMB)
    have hresult := RamCopy.leftToResult_spec B (P.b ii) h1 (hq.1.trans_lt hMB) (hq.2.trans_lt hMB)
    run_vcg [hload, hresult]
    all_goals clear hload hresult
    all_goals simp_all [Represents, value, ii]
  · run_vcg [hzero]
    all_goals simp_all [Represents, value]
    all_goals (try split_ifs) <;> (try simp_all) <;> omega

def padCoordinate : Com := .seq selectBound
  (.seq (.assign "vec.i" (.var "pad.k")) (storeReduced "pad.b"))

set_option maxHeartbeats 600000 in
theorem padCoordinate_spec (B M m n : ℕ) (P : Program ℚ m n) (i : Fin (m + 2))
    (ys : List ℚ) (hy : i.val < ys.length) (hM : 1 ≤ M) (hMB : M < B)
    (hmB : m + 2 < B) (hb : ∀ i, Height (P.b i) M) :
    Spec B (fun σ => Represents "query.b" (List.ofFn P.b) σ ∧ Represents "pad.b" ys σ ∧
        σ.vars "source.m" = m ∧ σ.vars "pad.k" = i.val)
      padCoordinate
      (fun _ τ => Represents "pad.b" (ys.set i.val (value P i)) τ ∧
        Represents "query.b" (List.ofFn P.b) τ ∧ τ.vars "source.m" = m ∧ τ.vars "pad.k" = i.val) 36 := by
  have h1 : 1 < B := hM.trans_lt hMB
  have hiB : i.val < B := i.isLt.trans hmB
  have hq := value_height P M hM hb i
  have hs := spec_with_fields ["source.m", "pad.k"]
    (selectBound_spec B M m n P i hM hMB hmB hb)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> decide) (by rfl)
  have hstore := spec_with_write_frame ["source.m", "pad.k"]
    (storeReduced_spec B "pad.b" ys (value P i) i.val hy h1 hiB
      (hq.1.trans_lt hMB) (hq.2.trans_lt hMB))
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> decide)
  rintro σ ⟨hσb, hσy, hσm, hσi⟩
  run_vcg [hs, hstore]
  all_goals clear hs hstore
  all_goals simp_all [Represents, FieldsAgree, storeReduced, Com.warrs]
  all_goals aesop

def Invariant {m n : ℕ} (P : Program ℚ m n) (σ : Env) : Prop :=
  Represents "query.b" (List.ofFn P.b) σ ∧
    Represents "pad.b" (filled (value P) (σ.vars "pad.k")) σ ∧
    σ.vars "pad.k" ≤ m + 2 ∧ σ.vars "pad.count" = m + 2 ∧ σ.vars "source.m" = m

def padStep : Com := .seq padCoordinate (.assign "pad.k" (.add (.var "pad.k") (.lit 1)))

theorem padStep_spec (B M m n : ℕ) (P : Program ℚ m n) (hM : 1 ≤ M) (hMB : M < B)
    (hmB : m + 2 < B) (hb : ∀ i, Height (P.b i) M) :
    Spec B (fun σ => Invariant P σ ∧ σ.vars "pad.k" < m + 2) padStep
      (fun σ τ => Invariant P τ ∧ τ.vars "pad.k" = σ.vars "pad.k" + 1) 40 := by
  rintro σ ⟨⟨hσb, hσp, hσkN, hσcount, hσm⟩, hσk⟩
  let i : Fin (m + 2) := ⟨σ.vars "pad.k", hσk⟩
  obtain ⟨τ, hr₁, hτp, hτb, hτm, hτi⟩ := padCoordinate_spec B M m n P i
    (filled (value P) i.val) (by simpa only [filled, List.length_ofFn] using i.isLt)
    hM hMB hmB hb σ ⟨hσb, hσp, hσm, rfl⟩
  have hτcount := (hr₁.frame_var "pad.count" (by decide)).trans hσcount
  have h1 : 1 < B := hM.trans_lt hMB
  have hiB : i.val < B := i.isLt.trans hmB
  have hi1B : i.val + 1 < B := lt_of_le_of_lt i.isLt hmB
  have hr₂ : Run B (.assign "pad.k" (.add (.var "pad.k") (.lit 1))) τ
      (τ.setVar "pad.k" (i.val + 1)) 4 := by
    exact Run.assign (by simpa only [hτi, Bop.apply_add] using (evalB_bin
      (evalB_var (B := B) (σ := τ) (x := "pad.k") (hτi ▸ hiB)) (evalB_lit h1)
      (show Bop.add.apply (τ.vars "pad.k") 1 < B by simpa [hτi] using hi1B)))
  have hfilled : Represents "pad.b" (filled (value P) (i.val + 1)) τ := by
    rw [← filled_step]
    exact hτp
  refine ⟨_, hr₁.seq hr₂, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Represents, arrs_setVar] using hτb
  · simpa only [Represents, arrs_setVar, vars_setVar, ite_true] using hfilled
  · change i.val + 1 ≤ m + 2
    exact i.isLt
  · simpa using hτcount
  · simpa using hτm
  · simp [i]

def padLoop : Com := .seq (.assign "pad.k" (.lit 0))
  (.while (.lt (.var "pad.k") (.var "pad.count")) padStep)

theorem padLoop_spec (B M m n : ℕ) (P : Program ℚ m n) (hM : 1 ≤ M) (hMB : M < B)
    (hmB : m + 2 < B) (hb : ∀ i, Height (P.b i) M) :
    Spec B (fun σ => Represents "query.b" (List.ofFn P.b) σ ∧
        Represents "pad.b" (List.replicate (m + 2) 0) σ ∧
        σ.vars "pad.count" = m + 2 ∧ σ.vars "source.m" = m)
      padLoop
      (fun _ τ => Represents "pad.b" (List.ofFn (FeasibilityPadding.pad P).b) τ ∧
        Represents "query.b" (List.ofFn P.b) τ ∧ τ.vars "source.m" = m) (44 * (m + 2) + 6) := by
  have hlo := Spec.forRangeZero "pad.k" "pad.count" (Invariant P) (m + 2) 40 hmB
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2.1) (padStep_spec B M m n P hM hMB hmB hb)
  refine (hlo.pre ?_).post ?_
  · rintro σ ⟨hb, hp, hcount, hm⟩
    simp_all [Invariant, Represents, filled_zero]
  · rintro σ τ _ ⟨hτ, hk⟩
    refine ⟨?_, hτ.1, hτ.2.2.2.2⟩
    have he : List.ofFn (value P) = List.ofFn (FeasibilityPadding.pad P).b := by
      congr 1
      funext i
      exact value_eq P i
    simpa only [hk, filled_done, he] using hτ.2.1

def padBound : Com := .seq (.assign "pad.count" (.add (.var "source.m") (.lit 2)))
  (.seq (.assign "vec.n" (.var "pad.count")) (.seq (RamZeroArray.zeroRationalArray "pad.b") padLoop))

set_option maxHeartbeats 600000 in
theorem padBound_spec (B M m n : ℕ) (P : Program ℚ m n) (hM : 1 ≤ M) (hMB : M < B)
    (hmB : m + 2 < B) (hb : ∀ i, Height (P.b i) M) :
    Spec B (fun σ => Represents "query.b" (List.ofFn P.b) σ ∧ Extents "pad.b" (m + 2) σ ∧
        σ.vars "source.m" = m) padBound
      (fun _ τ => Represents "pad.b" (List.ofFn (FeasibilityPadding.pad P).b) τ ∧
        Represents "query.b" (List.ofFn P.b) τ ∧ τ.vars "source.m" = m) (77 * (m + 2) + 30) := by
  have h1 : 1 < B := hM.trans_lt hMB
  have h2 : 2 < B := by omega
  have hm : m < B := by omega
  have hzero := spec_with_write_frame ["source.m", "pad.count"]
    (RamZeroArray.zeroRationalArray_spec B (m + 2) "pad.b" hmB h1)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> decide)
  have hlo := padLoop_spec B M m n P hM hMB hmB hb
  rintro σ ⟨hσb, hσpad, hσm⟩
  have hs := hσpad ".s" (by simp)
  have hn := hσpad ".n" (by simp)
  have hd := hσpad ".d" (by simp)
  run_vcg [hzero, hlo]
  all_goals clear hzero hlo
  all_goals simp_all [FieldsAgree, Represents, Extents]
  all_goals aesop

end Lax109476Proofs.RamPadBound

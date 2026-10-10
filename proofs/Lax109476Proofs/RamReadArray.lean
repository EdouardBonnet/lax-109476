import Lax109476Proofs.RamReadFraction
import Lax109476Proofs.RamCenterUpdate
import Lax109476Proofs.RamPrimitiveBounds

namespace Lax109476Proofs.RamReadArray

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamReadFraction RamRational RamRationalArrays RamFrame RamCenterUpdate
open RationalArithmeticBounds RamArithmetic

/-- Pure descriptions of the values and flags produced by the uniform loop.
They are specification parameters, not commands or input-dependent code. -/
def flag (xs : List ℕ) (v : ℕ) : ℕ → ℕ
  | 0 => v
  | k + 1 => if WordDecoding.readRational (xs.drop (3 * k)) = none then 0 else flag xs v k

def values (xs : List ℕ) (v n : ℕ) : Fin n → ℚ :=
  fun i => safeValue (xs.drop (3 * i.val)) (flag xs v i.val)

theorem flag_le_one (xs : List ℕ) (v k : ℕ) (hv : v ≤ 1) : flag xs v k ≤ 1 := by
  induction k with
  | zero => exact hv
  | succ k ih => simp only [flag]; split_ifs <;> omega

theorem safeValue_height (xs : List ℕ) (v M : ℕ) (hM : 1 ≤ M)
    (hwords : ∀ a ∈ xs, a ≤ M) : Height (safeValue xs v) M := by
  unfold safeValue
  split_ifs with hv
  · rw [readRational_raw]
    split_ifs with hg
    · simp only [Option.map_some, Option.getD_some]
      exact RamPrimitiveBounds.fractionValue_height _ _ _ M
        (headD_le xs.tail M (fun a ha => hwords a (List.mem_of_mem_tail ha)))
        (headD_le xs.tail.tail M
          (fun a ha => hwords a (List.mem_of_mem_tail (List.mem_of_mem_tail ha)))) hg.2
    · simpa [Height] using hM
  · simpa [Height] using hM

def Invariant (B : ℕ) (a : String) (xs : List ℕ) (v n : ℕ) (σ : Env) : Prop :=
  Represents a (filled (values xs v n) (σ.vars "vec.i")) σ ∧
    σ.inp = xs.drop (3 * σ.vars "vec.i") ∧
    σ.vars "input.remaining" = (xs.drop (3 * σ.vars "vec.i")).length ∧
    σ.vars "input.valid" = flag xs v (σ.vars "vec.i") ∧
    σ.InpBounded B ∧ σ.vars "vec.i" ≤ n ∧ σ.vars "vec.n" = n

def readStep (a : String) : Com := .seq safeFraction
  (.seq (storeReduced a) (.assign "vec.i" (.add (.var "vec.i") (.lit 1))))

theorem readStep_spec (B M n v : ℕ) (a : String) (xs : List ℕ)
    (h2 : 2 < B) (hMB : M < B) (hM : 1 ≤ M) (hnB : n < B)
    (hxB : xs.length < B) (hv : v ≤ 1) (hwords : ∀ z ∈ xs, z ≤ M) :
    Spec B (fun σ => Invariant B a xs v n σ ∧ σ.vars "vec.i" < n) (readStep a)
      (fun σ τ => Invariant B a xs v n τ ∧ τ.vars "vec.i" = σ.vars "vec.i" + 1)
      (36 * M.size + 78) := by
  rintro σ ⟨⟨hσa, hσinp, hσrem, hσvalid, hσbound, hσin, hσn⟩, hσi⟩
  let i : Fin n := ⟨σ.vars "vec.i", hσi⟩
  let tail := xs.drop (3 * i.val)
  have htailB : tail.length < B := by dsimp [tail]; simp only [List.length_drop]; omega
  have htailwords : ∀ z ∈ tail, z ≤ M := by
    intro z hz; exact hwords z (List.mem_of_mem_drop hz)
  obtain ⟨τ, hr₁, hτq, hτinp, hτrem, hτvalid, hτbound⟩ :=
    safeFraction_spec B M tail (flag xs v i.val) h2 htailB (flag_le_one xs v i.val hv)
      hMB htailwords σ ⟨hσinp, hσrem, hσvalid, hσbound⟩
  have hτi : τ.vars "vec.i" = i.val := hr₁.frame_var _ (by decide)
  have hτn : τ.vars "vec.n" = n := (hr₁.frame_var _ (by decide)).trans hσn
  have harr : τ.arrs = σ.arrs := by
    funext b
    exact hr₁.frame_arr b (by
      simp [safeFraction, readFraction, readRawFraction, RamInput.safeRead, validateFraction,
        normalizeFraction, gcdLoop, gcdDoubleStep, gcdStep, zeroResult, Com.warrs])
  have hτa : Represents a (filled (values xs v n) i.val) τ := by
    simpa only [Represents, harr, i] using hσa
  have hq : Height (values xs v n i) M := safeValue_height tail (flag xs v i.val) M hM htailwords
  obtain ⟨υ, hr₂, hυa⟩ := storeReduced_spec B a (filled (values xs v n) i.val)
    (values xs v n i) i.val (by simpa [filled] using i.isLt) (by omega) (i.isLt.trans hnB)
    (hq.1.trans_lt hMB) (hq.2.trans_lt hMB) τ ⟨hτa, hτi, hτq⟩
  have hυi : υ.vars "vec.i" = i.val := (hr₂.frame_var _ (by simp [storeReduced, Com.wvars])).trans hτi
  have hυn : υ.vars "vec.n" = n := (hr₂.frame_var _ (by simp [storeReduced, Com.wvars])).trans hτn
  have hυinp := (hr₂.frame_inp (by simp [storeReduced, Com.reads])).trans hτinp
  have hυrem := (hr₂.frame_var "input.remaining" (by simp [storeReduced, Com.wvars])).trans hτrem
  have hυvalid := (hr₂.frame_var "input.valid" (by simp [storeReduced, Com.wvars])).trans hτvalid
  have hdrop : tail.drop 3 = xs.drop (3 * (i.val + 1)) := by
    dsimp [tail]; rw [List.drop_drop]; congr 1
  have hnext : Represents a (filled (values xs v n) (i.val + 1)) υ := by
    simpa only [filled_step] using hυa
  have he : (Expr.add (.var "vec.i") (.lit 1)).evalB B υ = some (i.val + 1) := by
    simpa only [hυi, Bop.apply_add] using evalB_bin
      (evalB_var (B := B) (σ := υ) (x := "vec.i") (by rw [hυi]; exact i.isLt.trans hnB))
      (evalB_lit (by omega : 1 < B))
      (show Bop.add.apply (υ.vars "vec.i") 1 < B by rw [hυi]; simp only [Bop.apply_add]; omega)
  have hr₃ := Run.assign (x := "vec.i") he
  have hrun := hr₁.seq (hr₂.seq hr₃)
  refine ⟨_, hrun, ⟨?_, ?_, ?_, ?_, hrun.inpBounded hσbound, ?_, ?_⟩, ?_⟩
  · simpa only [Represents, arrs_setVar, vars_setVar, ite_true] using hnext
  · simpa only [Env.setVar, ite_true, hdrop] using hυinp
  · simp only [Env.setVar, ite_true]
    rw [← hdrop, List.length_drop]
    exact hυrem
  · simp only [Env.setVar, ite_true, flag]
    exact hυvalid
  · change i.val + 1 ≤ n; exact i.isLt
  · simpa [Env.setVar] using hυn
  · simp [i]

def readLoop (a : String) : Com := .seq (.assign "vec.i" (.lit 0))
  (.while (.lt (.var "vec.i") (.var "vec.n")) (readStep a))

theorem readLoop_spec (B M n v : ℕ) (a : String) (xs : List ℕ)
    (h2 : 2 < B) (hMB : M < B) (hM : 1 ≤ M) (hnB : n < B)
    (hxB : xs.length < B) (hv : v ≤ 1) (hwords : ∀ z ∈ xs, z ≤ M) :
    Spec B (fun σ => Represents a (List.replicate n 0) σ ∧ σ.inp = xs ∧
        σ.vars "input.remaining" = xs.length ∧ σ.vars "input.valid" = v ∧
        σ.InpBounded B ∧ σ.vars "vec.n" = n)
      (readLoop a)
      (fun _ τ => Represents a (List.ofFn (values xs v n)) τ ∧ τ.inp = xs.drop (3 * n) ∧
        τ.vars "input.remaining" = (xs.drop (3 * n)).length ∧
        τ.vars "input.valid" = flag xs v n ∧ τ.InpBounded B ∧ τ.vars "vec.n" = n)
      ((36 * M.size + 82) * n + 6) := by
  have hlo := Spec.forRangeZero "vec.i" "vec.n" (Invariant B a xs v n) n (36 * M.size + 78)
    hnB (fun _ h => h.2.2.2.2.2.1) (fun _ h => h.2.2.2.2.2.2)
    (readStep_spec B M n v a xs h2 hMB hM hnB hxB hv hwords)
  refine ((hlo.pre ?_).post ?_).mono (by simp only [Nat.add_assoc, Nat.reduceAdd]; omega)
  · rintro σ ⟨hσa, hσinp, hσrem, hσvalid, hσbound, hσn⟩
    clear hlo
    simp_all [Invariant, filled_zero, Represents, Env.setVar, flag, Env.InpBounded]
  · rintro σ τ _ ⟨hτ, hcounter⟩
    rcases hτ with ⟨hτa, hτinp, hτrem, hτvalid, hτbound, hτi, hτn⟩
    exact ⟨by simpa only [hcounter, filled_done] using hτa,
      by simpa only [hcounter] using hτinp, by simpa only [hcounter] using hτrem,
      by simpa only [hcounter] using hτvalid, hτbound, hτn⟩

def readArray (a : String) : Com := .seq (RamZeroArray.zeroRationalArray a) (readLoop a)

theorem readArray_spec (B M n v : ℕ) (a : String) (xs : List ℕ)
    (h2 : 2 < B) (hMB : M < B) (hM : 1 ≤ M) (hnB : n < B)
    (hxB : xs.length < B) (hv : v ≤ 1) (hwords : ∀ z ∈ xs, z ≤ M) :
    Spec B (fun σ => (σ.arrs (a ++ ".s")).length = n ∧
        (σ.arrs (a ++ ".n")).length = n ∧ (σ.arrs (a ++ ".d")).length = n ∧
        σ.inp = xs ∧ σ.vars "input.remaining" = xs.length ∧ σ.vars "input.valid" = v ∧
        σ.InpBounded B ∧ σ.vars "vec.n" = n)
      (readArray a)
      (fun _ τ => Represents a (List.ofFn (values xs v n)) τ ∧ τ.inp = xs.drop (3 * n) ∧
        τ.vars "input.remaining" = (xs.drop (3 * n)).length ∧
        τ.vars "input.valid" = flag xs v n ∧ τ.InpBounded B ∧ τ.vars "vec.n" = n)
      ((36 * M.size + 115) * n + 24) := by
  rintro σ ⟨hσs, hσnum, hσd, hσinp, hσrem, hσvalid, hσbound, hσn⟩
  obtain ⟨τ, hr₁, hτa, hτn, _⟩ := RamZeroArray.zeroRationalArray_spec B n a hnB (by omega)
    σ ⟨hσs, hσnum, hσd, hσn⟩
  have hτinp := (hr₁.frame_inp (by simp [RamZeroArray.zeroRationalArray, RamZeroArray.fillConstant,
    Lib.Fill.put, Com.reads])).trans hσinp
  have hτrem := (hr₁.frame_var "input.remaining" (by simp [RamZeroArray.zeroRationalArray,
    RamZeroArray.fillConstant, Lib.Fill.put, Com.wvars])).trans hσrem
  have hτvalid := (hr₁.frame_var "input.valid" (by simp [RamZeroArray.zeroRationalArray,
    RamZeroArray.fillConstant, Lib.Fill.put, Com.wvars])).trans hσvalid
  obtain ⟨υ, hr₂, hυ⟩ := readLoop_spec B M n v a xs h2 hMB hM hnB hxB hv hwords
    τ ⟨hτa, hτinp, hτrem, hτvalid, hr₁.inpBounded hσbound, hτn⟩
  exact ⟨υ, (hr₁.seq hr₂).mono (by simp only [Nat.add_mul]; omega), hυ⟩

theorem rational_drop (xs : List ℕ) (q : ℚ) (rest : List ℕ)
    (h : WordDecoding.readRational xs = some (q, rest)) : xs.drop 3 = rest := by
  rw [readRational_raw] at h
  split_ifs at h with hg
  exact (Prod.mk.inj (Option.some.inj h)).2

theorem flag_shift (xs : List ℕ) (v k : ℕ) (h : WordDecoding.readRational xs ≠ none) :
    flag (xs.drop 3) v k = flag xs v (k + 1) := by
  induction k with
  | zero => simp [flag, h]
  | succ k ih =>
    simp only [flag, List.drop_drop]
    have he : 3 + 3 * k = 3 * (k + 1) := by omega
    rw [he, ih]
    rfl

theorem readVector_correct (n : ℕ) (xs : List ℕ) (x : Fin n → ℚ) (rest : List ℕ)
    (h : WordDecoding.readVector n xs = some (x, rest)) :
    flag xs 1 n = 1 ∧ values xs 1 n = x ∧ xs.drop (3 * n) = rest := by
  induction n generalizing xs rest with
  | zero =>
    simp only [WordDecoding.readVector, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨rfl, by funext j; exact Fin.elim0 j, by simpa using h.2⟩
  | succ n ih =>
    obtain ⟨⟨q, mid⟩, hq, hx⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨y, tail⟩, hy, he⟩ := Option.bind_eq_some_iff.mp hx
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hflag, hvals, hrest⟩ := ih mid y tail hy
    have hdrop := rational_drop xs q mid hq
    have hne : WordDecoding.readRational xs ≠ none := by rw [hq]; simp
    have hshift := flag_shift xs 1 n hne
    rw [hdrop] at hshift
    refine ⟨hshift.symm.trans hflag, ?_, ?_⟩
    · funext j
      refine Fin.cases ?_ (fun k => ?_) j
      · simp [values, safeValue, flag, hq]
      · change safeValue (xs.drop (3 * (k.val + 1))) (flag xs 1 (k.val + 1)) = y k
        have hd : xs.drop (3 * (k.val + 1)) = mid.drop (3 * k.val) := by
          rw [← hdrop, List.drop_drop]
          congr 1 <;> omega
        have hf := flag_shift xs 1 k.val hne
        rw [hdrop] at hf
        rw [hd, ← hf]
        exact congrFun hvals k
    · rw [← hrest, ← hdrop, List.drop_drop]
      congr 1 <;> omega

/-- A successful functional parse is represented by the actual array loop;
its rows and coordinates may be noncanonical on the incoming tape. -/
theorem readArray_valid_spec (B M n : ℕ) (a : String) (xs : List ℕ) (x : Fin n → ℚ)
    (rest : List ℕ) (h2 : 2 < B) (hMB : M < B) (hM : 1 ≤ M) (hnB : n < B)
    (hxB : xs.length < B) (hwords : ∀ z ∈ xs, z ≤ M)
    (hdecode : WordDecoding.readVector n xs = some (x, rest)) :
    Spec B (fun σ => (σ.arrs (a ++ ".s")).length = n ∧
        (σ.arrs (a ++ ".n")).length = n ∧ (σ.arrs (a ++ ".d")).length = n ∧
        σ.inp = xs ∧ σ.vars "input.remaining" = xs.length ∧ σ.vars "input.valid" = 1 ∧
        σ.InpBounded B ∧ σ.vars "vec.n" = n)
      (readArray a)
      (fun _ τ => Represents a (List.ofFn x) τ ∧ τ.inp = rest ∧
        τ.vars "input.remaining" = rest.length ∧ τ.vars "input.valid" = 1 ∧
        τ.InpBounded B ∧ τ.vars "vec.n" = n)
      ((36 * M.size + 115) * n + 24) := by
  obtain ⟨hf, hv, hr⟩ := readVector_correct n xs x rest hdecode
  simpa only [hf, hv, hr] using readArray_spec B M n 1 a xs h2 hMB hM hnB hxB (by decide) hwords

theorem flag_zero (xs : List ℕ) (k : ℕ) : flag xs 0 k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [flag, ih]

theorem flag_first_failure (xs : List ℕ) (v k : ℕ)
    (h : WordDecoding.readRational xs = none) : flag xs v (k + 1) = 0 := by
  induction k with
  | zero => simp [flag, h]
  | succ k ih =>
    change (if WordDecoding.readRational (xs.drop (3 * (k + 1))) = none then 0 else flag xs v (k + 1)) = 0
    rw [ih]; split_ifs <;> rfl

theorem readVector_exists_of_flag (n : ℕ) (xs : List ℕ) (h : flag xs 1 n = 1) :
    ∃ x rest, WordDecoding.readVector n xs = some (x, rest) := by
  induction n generalizing xs with
  | zero => exact ⟨0, xs, rfl⟩
  | succ n ih =>
    have hne : WordDecoding.readRational xs ≠ none := by
      intro hh; rw [flag_first_failure xs 1 n hh] at h; omega
    obtain ⟨⟨q, mid⟩, hq⟩ := Option.ne_none_iff_exists'.mp hne
    have hdrop := rational_drop xs q mid hq
    have hmid : flag mid 1 n = 1 := by rw [← hdrop, flag_shift xs 1 n hne]; exact h
    obtain ⟨x, rest, hx⟩ := ih mid hmid
    exact ⟨Fin.cons q x, rest, by simp [WordDecoding.readVector, hq, hx]⟩

theorem readVector_none_iff (n : ℕ) (xs : List ℕ) :
    WordDecoding.readVector n xs = none ↔ flag xs 1 n = 0 := by
  constructor
  · intro hnone
    have hle := flag_le_one xs 1 n (by decide)
    by_contra hz
    have hf : flag xs 1 n = 1 := by omega
    obtain ⟨x, rest, hh⟩ := readVector_exists_of_flag n xs hf
    rw [hnone] at hh; contradiction
  · intro hz
    by_contra hn
    obtain ⟨⟨x, rest⟩, hh⟩ := Option.ne_none_iff_exists'.mp hn
    have hf := (readVector_correct n xs x rest hh).1
    omega

end Lax109476Proofs.RamReadArray

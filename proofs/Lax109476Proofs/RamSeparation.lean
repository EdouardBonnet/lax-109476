import Lax109476Proofs.RamMatrixRows
import Lax109476Proofs.RamComparison

open scoped BigOperators

namespace Lax109476Proofs.RamSeparation

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamDotProduct RamMatrixRows RamComparison RationalArithmeticBounds

/-- Compare the accumulated row value with the stored right-hand side. -/
def compareRowRhs (a : String) : Com :=
  .seq (.assign "left.s" (.var "dot.s"))
    (.seq (.assign "left.n" (.var "dot.n"))
      (.seq (.assign "left.d" (.var "dot.d"))
        (.seq (.assign "vec.i" (.var "row.i"))
          (.seq (loadRight a) (.seq compareFraction (.assign "vec.i" (.var "vec.n")))))))

set_option maxHeartbeats 800000 in
theorem compareRowRhs_spec (B M i n : ℕ) (a : String) (bs : List ℚ) (q : ℚ)
    (hi : i < bs.length) (hiB : i < B) (hnB : n < B)
    (hB : 2 * M ^ 2 + 3 < B) (hq : Height q M) (hb : Height bs[i] M) :
    Spec B (fun σ => DotOutput q σ ∧ Represents a bs σ ∧
        σ.vars "row.i" = i ∧ σ.vars "vec.n" = n)
      (compareRowRhs a)
      (fun σ τ => τ.vars "cmp.le" ≤ 1 ∧ (τ.vars "cmp.le" = 1 ↔ q ≤ bs[i]) ∧
        τ.vars "vec.i" = n ∧ τ.arrs = σ.arrs) 59 := by
  have hM : M < B := by nlinarith
  have h1 : 1 < B := by nlinarith
  rintro σ ⟨hqσ, hσb, hσi, hσn⟩
  have hqval := hqσ.1
  have hqnum := hqσ.2.1
  have hqden := hqσ.2.2.1
  have hqs := hqσ.2.2.2.trans_lt h1
  have hqn := hq.1.trans_lt hM
  have hqd := hq.2.trans_lt hM
  have hload := loadRight_frame_spec B a bs i hi h1 hiB
    (hb.1.trans_lt hM) (hb.2.trans_lt hM)
  have hcmp := compareFraction_spec B M (σ.vars "dot.s") q.num.natAbs q.den
    (rationalSign bs[i]) bs[i].num.natAbs bs[i].den hB hqσ.2.2.2
    (rationalSign_le_one _) hq.1 hq.2 hb.1 hb.2 q.den_pos bs[i].den_pos
  have hcframe := spec_with_fields ["vec.n"] hcmp
    (by intro x hx; simp at hx; subst x; simp [compareFraction, Com.wvars])
    (by simp [compareFraction, Com.warrs])
  clear hcmp
  have hlframe := spec_with_fields ["vec.n"] hload
    (by intro x hx; simp at hx; subst x; simp [loadRight, Com.wvars])
    (by simp [loadRight, Com.warrs])
  clear hload
  run_vcg [hlframe, hcframe]
  all_goals clear hlframe hcframe
  all_goals simp_all [DotOutput, Represents, fractionInputs, FieldsAgree, RightOutput,
    canonical_fractionValue]


def evaluateRow (a point rhs : String) : Com :=
  .seq (matrixRowDot a point) (compareRowRhs rhs)

theorem evaluateRow_spec (B m n H : ℕ) (a point rhs : String)
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (c : Fin n → ℚ) (i : Fin m)
    (hH : 1 ≤ H) (hA : ∀ k j, Height (A k j) H) (hb : ∀ k, Height (b k) H)
    (hc : ∀ j, Height (c j) H) (hdims : m + n + m * n + 1 < B)
    (hB : 2 * (cap n H) ^ 2 + 3 < B) :
    Spec B (fun σ => MatrixRows a A σ ∧ Represents point (List.ofFn c) σ ∧
        Represents rhs (List.ofFn b) σ ∧ σ.vars "row.i" = i.val ∧ σ.vars "vec.n" = n)
      (evaluateRow a point rhs)
      (fun σ τ => τ.vars "cmp.le" ≤ 1 ∧
        (τ.vars "cmp.le" = 1 ↔ (∑ j, A i j * c j) ≤ b i) ∧ τ.arrs = σ.arrs)
      (4 + ((144 * (cap n H).size + 216 + 4) * n + 12) + 59) := by
  rintro σ ⟨hσA, hσc, hσb, hσi, hσn⟩
  have hrow := spec_with_fields ["row.i", "vec.n"]
    (matrixRowDot_spec B m n H a point A c i hH hA hc hdims hB)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;>
      simp [matrixRowDot, rowDotProduct, rowDotStep, multiplyRowAt, loadRowLeft, loadRight,
        addToAccumulator, addFraction, multiplyFraction, RamArithmetic.normalizeFraction,
        RamArithmetic.gcdLoop, RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.wvars])
    (by simp [matrixRowDot, rowDotProduct, rowDotStep, multiplyRowAt, loadRowLeft, loadRight,
        addToAccumulator, addFraction, multiplyFraction, RamArithmetic.normalizeFraction,
        RamArithmetic.gcdLoop, RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.warrs])
  obtain ⟨τ, hr₁, ⟨hτq, hτa⟩, hτf, _⟩ := hrow σ ⟨hσA, hσc, hσi, hσn⟩
  have hτb : Represents rhs (List.ofFn b) τ := by simpa only [Represents, hτa] using hσb
  have hτi : τ.vars "row.i" = i.val := (hτf _ (by simp)).trans hσi
  have hτn : τ.vars "vec.n" = n := (hτf _ (by simp)).trans hσn
  have hsum : Height (∑ j, A i j * c j) (cap n H) := by
    rw [← prefix_ofFn]
    apply prefix_height _ _ n H n hH (by simp) (by simp) le_rfl
    · intro q hq; simp only [List.mem_ofFn] at hq; obtain ⟨j, rfl⟩ := hq; exact hA i j
    · intro q hq; simp only [List.mem_ofFn] at hq; obtain ⟨j, rfl⟩ := hq; exact hc j
  have hib : i.val < B := by have := i.isLt; omega
  have hnb : n < B := by omega
  have hbi : Height (List.ofFn b)[i.val] (cap n H) := by
    simpa using height_mono _ (hb i) (cap_ge n H hH).2
  obtain ⟨υ, hr₂, hυflag, hυq, _, hυa⟩ := compareRowRhs_spec B (cap n H) i.val n rhs
    (List.ofFn b) (∑ j, A i j * c j) (by simp) hib hnb hB hsum hbi
    τ ⟨hτq, hτb, hτi, hτn⟩
  refine ⟨υ, hr₁.seq hr₂, hυflag, ?_, hυa.trans hτa⟩
  simpa using hυq

def foundBefore (p : ℕ → Bool) (m k : ℕ) : ℕ := ((List.range k).find? p).getD m

theorem foundBefore_zero (p : ℕ → Bool) (m : ℕ) : foundBefore p m 0 = m := by
  simp [foundBefore]

theorem foundBefore_le (p : ℕ → Bool) (m k : ℕ) (hk : k ≤ m) : foundBefore p m k ≤ m := by
  unfold foundBefore
  cases hf : (List.range k).find? p with
  | none => simp
  | some j =>
    have hj := List.mem_of_find?_eq_some hf
    simp only [List.mem_range] at hj
    simp only [Option.getD_some]
    omega

theorem foundBefore_succ (p : ℕ → Bool) (m k : ℕ) (hk : k < m) :
    foundBefore p m (k + 1) =
      if foundBefore p m k = m ∧ p k = true then k else foundBefore p m k := by
  unfold foundBefore
  rw [List.range_succ, List.find?_append]
  cases hf : (List.range k).find? p with
  | none => simp; split <;> simp_all
  | some j =>
    have hj := List.mem_of_find?_eq_some hf
    simp only [List.mem_range] at hj
    have hne : j ≠ m := by omega
    simp [hne]

def violationPred {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (c : Fin n → ℚ) (k : ℕ) : Bool :=
  if hk : k < m then decide (b ⟨k, hk⟩ < ∑ j, A ⟨k, hk⟩ j * c j) else false

theorem violationPred_val {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) (c : Fin n → ℚ) (i : Fin m) :
    violationPred A b c i.val = decide (b i < ∑ j, A i j * c j) := by
  simp [violationPred, i.isLt]

theorem finRange_values (m : ℕ) : (List.finRange m).map Fin.val = List.range m := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

/-- The numeric sentinel encoding is the same first violated row used by
mathematical separation. -/
theorem foundBefore_integer {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℚ) (c : Fin n → ℚ) :
    foundBefore (violationPred (fun i j => (A i j : ℚ)) b c) m m =
      ((RationalSeparation.firstViolation A b c).map Fin.val).getD m := by
  unfold foundBefore
  rw [← finRange_values, List.find?_map]
  congr 1
  congr 1
  unfold RationalSeparation.firstViolation
  congr 1
  funext i
  exact violationPred_val _ _ _ i

def recordViolation : Com :=
  .seq (.ite (.eq (.var "cmp.le") (.lit 0))
    (.ite (.eq (.var "row.first") (.var "row.m"))
      (.assign "row.first" (.var "row.i")) .skip) .skip)
    (.assign "row.i" (.add (.var "row.i") (.lit 1)))

theorem recordViolation_spec (B flag first i m : ℕ) (hf : flag ≤ 1) (hfirst : first ≤ m)
    (hi : i < m) (hmB : m < B) (h1 : 1 < B) :
    Spec B (fun σ => σ.vars "cmp.le" = flag ∧ σ.vars "row.first" = first ∧
        σ.vars "row.i" = i ∧ σ.vars "row.m" = m)
      recordViolation
      (fun _ τ => τ.vars "row.first" = (if flag = 0 ∧ first = m then i else first) ∧
        τ.vars "row.i" = i + 1) 16 := by
  have hfB := hf.trans_lt h1
  have hfirstB := hfirst.trans_lt hmB
  have hiB : i < B := hi.trans hmB
  have hi1B : i + 1 < B := lt_of_le_of_lt (by omega) hmB
  rintro σ ⟨hσf, hσfirst, hσi, hσm⟩
  run_vcg
  all_goals simp_all


def scanStep (a point rhs : String) : Com := .seq (evaluateRow a point rhs) recordViolation

def rowCost (n H : ℕ) : ℕ := 4 + ((144 * (cap n H).size + 216 + 4) * n + 12) + 59

def ScanInvariant {m n : ℕ} (a point rhs : String) (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) (c : Fin n → ℚ) (σ : Env) : Prop :=
  MatrixRows a A σ ∧ Represents point (List.ofFn c) σ ∧ Represents rhs (List.ofFn b) σ ∧
    σ.vars "row.i" ≤ m ∧ σ.vars "row.m" = m ∧ σ.vars "vec.n" = n ∧
    σ.vars "row.first" = foundBefore (violationPred A b c) m (σ.vars "row.i")

theorem scanStep_spec (B m n H : ℕ) (a point rhs : String)
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (c : Fin n → ℚ)
    (hH : 1 ≤ H) (hA : ∀ k j, Height (A k j) H) (hb : ∀ k, Height (b k) H)
    (hc : ∀ j, Height (c j) H) (hdims : m + n + m * n + 1 < B)
    (hB : 2 * (cap n H) ^ 2 + 3 < B) :
    Spec B (fun σ => ScanInvariant a point rhs A b c σ ∧ σ.vars "row.i" < m)
      (scanStep a point rhs)
      (fun σ τ => ScanInvariant a point rhs A b c τ ∧ τ.vars "row.i" = σ.vars "row.i" + 1)
      (rowCost n H + 16) := by
  rintro σ ⟨⟨hσA, hσc, hσb, hσim, hσm, hσn, hσfirst⟩, hσi⟩
  let i : Fin m := ⟨σ.vars "row.i", hσi⟩
  have heval := spec_with_fields ["row.i", "row.m", "vec.n", "row.first"]
    (evaluateRow_spec B m n H a point rhs A b c i hH hA hb hc hdims hB)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl <;>
      simp [evaluateRow, matrixRowDot, rowDotProduct, rowDotStep, multiplyRowAt, loadRowLeft,
        loadRight, addToAccumulator, compareRowRhs, compareFraction, addFraction, multiplyFraction,
        RamArithmetic.normalizeFraction, RamArithmetic.gcdLoop, RamArithmetic.gcdDoubleStep,
        RamArithmetic.gcdStep, Com.wvars])
    (by simp [evaluateRow, matrixRowDot, rowDotProduct, rowDotStep, multiplyRowAt, loadRowLeft,
        loadRight, addToAccumulator, compareRowRhs, compareFraction, addFraction, multiplyFraction,
        RamArithmetic.normalizeFraction, RamArithmetic.gcdLoop, RamArithmetic.gcdDoubleStep,
        RamArithmetic.gcdStep, Com.warrs])
  obtain ⟨τ, hr₁, ⟨hτflag, hτq, hτa⟩, hτfields, _⟩ :=
    heval σ ⟨hσA, hσc, hσb, rfl, hσn⟩
  have hτi : τ.vars "row.i" = i.val := hτfields _ (by simp)
  have hτm : τ.vars "row.m" = m := (hτfields _ (by simp)).trans hσm
  have hτn : τ.vars "vec.n" = n := (hτfields _ (by simp)).trans hσn
  have hτfirst : τ.vars "row.first" = foundBefore (violationPred A b c) m i.val :=
    (hτfields _ (by simp)).trans hσfirst
  have hmB : m < B := by omega
  have h1 : 1 < B := by nlinarith
  have hfirst := foundBefore_le (violationPred A b c) m i.val i.isLt.le
  have hrec := spec_with_fields ["row.m", "vec.n"]
    (recordViolation_spec B (τ.vars "cmp.le") (foundBefore (violationPred A b c) m i.val)
      i.val m hτflag hfirst i.isLt hmB h1)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;>
      simp [recordViolation, Com.wvars]) (by simp [recordViolation, Com.warrs])
  obtain ⟨υ, hr₂, ⟨hυfirst, hυi⟩, hυfields, hυa⟩ := hrec τ ⟨rfl, hτfirst, hτi, hτm⟩
  have hflag : τ.vars "cmp.le" = 0 ↔ violationPred A b c i.val = true := by
    rw [violationPred_val, decide_eq_true_eq]
    constructor
    · intro hf
      by_contra h
      have hh := hτq.mpr (le_of_not_gt h)
      omega
    · intro hv
      by_contra h
      have hh : τ.vars "cmp.le" = 1 := by omega
      exact (not_lt_of_ge (hτq.mp hh)) hv
  have hnew : υ.vars "row.first" = foundBefore (violationPred A b c) m (i.val + 1) := by
    rw [hυfirst, foundBefore_succ _ _ _ i.isLt]
    simp only [hflag, and_comm]
  refine ⟨υ, hr₁.seq hr₂, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hυi⟩
  · simpa only [MatrixRows, Slice, hυa, hτa] using hσA
  · simpa only [Represents, hυa, hτa] using hσc
  · simpa only [Represents, hυa, hτa] using hσb
  · rw [hυi]; exact i.isLt
  · exact (hυfields _ (by simp)).trans hτm
  · exact (hυfields _ (by simp)).trans hτn
  · rw [hυi]; exact hnew

def separateRows (a point rhs : String) : Com :=
  .seq (.assign "row.first" (.var "row.m"))
    (.seq (.assign "row.i" (.lit 0))
      (.while (.lt (.var "row.i") (.var "row.m")) (scanStep a point rhs)))

theorem separateRows_spec (B m n H : ℕ) (a point rhs : String)
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (c : Fin n → ℚ)
    (hH : 1 ≤ H) (hA : ∀ k j, Height (A k j) H) (hb : ∀ k, Height (b k) H)
    (hc : ∀ j, Height (c j) H) (hdims : m + n + m * n + 1 < B)
    (hB : 2 * (cap n H) ^ 2 + 3 < B) :
    Spec B (fun σ => MatrixRows a A σ ∧ Represents point (List.ofFn c) σ ∧
        Represents rhs (List.ofFn b) σ ∧ σ.vars "row.m" = m ∧ σ.vars "vec.n" = n)
      (separateRows a point rhs)
      (fun _ τ => τ.vars "row.first" = foundBefore (violationPred A b c) m m ∧
        MatrixRows a A τ ∧ Represents point (List.ofFn c) τ ∧ Represents rhs (List.ofFn b) τ)
      ((rowCost n H + 16 + 4) * m + 8) := by
  have hmB : m < B := by omega
  have hlo := Spec.forRangeZero "row.i" "row.m" (ScanInvariant a point rhs A b c) m
    (rowCost n H + 16) hmB (fun _ h => h.2.2.2.1) (fun _ h => h.2.2.2.2.1)
    (scanStep_spec B m n H a point rhs A b c hH hA hb hc hdims hB)
  rintro σ ⟨hσA, hσc, hσb, hσm, hσn⟩
  run_vcg [hlo]
  all_goals clear hlo
  all_goals simp_all [ScanInvariant, foundBefore_zero, MatrixRows, Slice, Represents]

theorem rowCost_polynomial (n H : ℕ) :
    rowCost n H ≤ (144 * ((n + 1) * (2 * H.size + 3) + 1) + 220) * n + 75 := by
  have hc := Nat.mul_le_mul_left 144 (cap_size n H)
  have hn := Nat.mul_le_mul_right n (Nat.add_le_add_right hc 220)
  unfold rowCost
  convert Nat.add_le_add_right hn 75 using 1
  ring

theorem separateRows_cost_polynomial (m n H : ℕ) :
    (rowCost n H + 16 + 4) * m + 8 ≤
      ((144 * ((n + 1) * (2 * H.size + 3) + 1) + 220) * n + 95) * m + 8 := by
  have hr := Nat.add_le_add_right (rowCost_polynomial n H) 20
  convert Nat.add_le_add_right (Nat.mul_le_mul_right m hr) 8 using 1

theorem separateRows_integer_spec (B m n H : ℕ) (a point rhs : String)
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ) (c : Fin n → ℚ)
    (hH : 1 ≤ H) (hA : ∀ k j, (A k j).natAbs ≤ H) (hb : ∀ k, Height (b k) H)
    (hc : ∀ j, Height (c j) H) (hdims : m + n + m * n + 1 < B)
    (hB : 2 * (cap n H) ^ 2 + 3 < B) :
    Spec B (fun σ => MatrixRows a (fun i j => (A i j : ℚ)) σ ∧
        Represents point (List.ofFn c) σ ∧ Represents rhs (List.ofFn b) σ ∧
        σ.vars "row.m" = m ∧ σ.vars "vec.n" = n)
      (separateRows a point rhs)
      (fun σ τ => τ.vars "row.first" =
        ((RationalSeparation.firstViolation A b c).map Fin.val).getD m ∧ τ.arrs = σ.arrs)
      ((rowCost n H + 16 + 4) * m + 8) := by
  have hAH : ∀ k j, Height (A k j : ℚ) H := by
    intro k j
    simpa [Height] using And.intro (hA k j) hH
  have hsep := spec_with_fields []
    (separateRows_spec B m n H a point rhs (fun i j => (A i j : ℚ)) b c
      hH hAH hb hc hdims hB) (by simp) (by
      simp [separateRows, scanStep, recordViolation, evaluateRow, matrixRowDot, rowDotProduct,
        rowDotStep, multiplyRowAt, loadRowLeft, loadRight, addToAccumulator, compareRowRhs,
        compareFraction, addFraction, multiplyFraction, RamArithmetic.normalizeFraction,
        RamArithmetic.gcdLoop, RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.warrs])
  intro σ hσ
  obtain ⟨τ, hr, hτ, _, ha⟩ := hsep σ hσ
  refine ⟨τ, hr, ?_, ha⟩
  rw [hτ.1, foundBefore_integer]

end Lax109476Proofs.RamSeparation

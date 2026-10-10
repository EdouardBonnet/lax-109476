import Lax109476Proofs.RamMatrixRows
import Lax109476Proofs.RamZeroArray

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamMatrixVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamDotProduct RamMatrixRows RationalArithmeticBounds

def storeDotAtRow (a : String) : Com :=
  .seq (.assign "rat.s" (.var "dot.s"))
    (.seq (.assign "rat.n" (.var "dot.n"))
      (.seq (.assign "rat.d" (.var "dot.d"))
        (.seq (.assign "vec.i" (.var "row.i")) (storeReduced a))))

theorem storeDotAtRow_basic_spec (B i : ℕ) (a : String) (qs : List ℚ) (q : ℚ)
    (hi : i < qs.length) (hiB : i < B) (hB : 1 < B)
    (hn : q.num.natAbs < B) (hd : q.den < B) :
    Spec B (fun σ => Represents a qs σ ∧ DotOutput q σ ∧ σ.vars "row.i" = i)
      (storeDotAtRow a) (fun _ τ => Represents a (qs.set i q) τ) 21 := by
  rintro σ ⟨hσa, hσq, hσi⟩
  have hsB := hσq.2.2.2.trans_lt hB
  have hnum := hσq.2.1
  have hden := hσq.2.2.1
  have hstore := storeReduced_spec B a qs q i hi hB hiB hn hd
  run_vcg [hstore]
  all_goals clear hstore
  all_goals simp_all [Represents, FractionOutput, DotOutput]

theorem storeDotAtRow_spec (B i : ℕ) (a : String) (qs : List ℚ) (q : ℚ)
    (hi : i < qs.length) (hiB : i < B) (hB : 1 < B)
    (hn : q.num.natAbs < B) (hd : q.den < B) :
    Spec B (fun σ => Represents a qs σ ∧ DotOutput q σ ∧ σ.vars "row.i" = i)
      (storeDotAtRow a)
      (fun σ τ => Represents a (qs.set i q) τ ∧
        FieldsAgree ["row.i", "row.m", "vec.n"] σ τ ∧
        ∀ b ∉ [a ++ ".s", a ++ ".n", a ++ ".d"], τ.arrs b = σ.arrs b) 21 := by
  intro σ hσ
  obtain ⟨τ, hr, hτ⟩ := storeDotAtRow_basic_spec B i a qs q hi hiB hB hn hd σ hσ
  refine ⟨τ, hr, hτ, ?_, ?_⟩
  · intro x hx
    apply hr.frame_var
    simp at hx
    rcases hx with rfl | rfl | rfl <;> simp [storeDotAtRow, storeReduced, Com.wvars]
  · intro b hb
    apply hr.frame_arr
    simpa [storeDotAtRow, storeReduced, Com.warrs] using hb

def filled {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (c : Fin n → ℚ) (k : ℕ) : List ℚ :=
  List.ofFn (fun i => if i.val < k then ∑ j, A i j * c j else 0)

theorem filled_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (c : Fin n → ℚ) :
    filled A c 0 = List.replicate m 0 := by simp [filled]

theorem filled_done {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (c : Fin n → ℚ) :
    filled A c m = List.ofFn (A *ᵥ c) := by
  unfold filled
  congr 1
  funext i
  simp [i.isLt, Matrix.mulVec, _root_.dotProduct]

theorem filled_step {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (c : Fin n → ℚ) (i : Fin m) :
    (filled A c i.val).set i.val (∑ j, A i j * c j) = filled A c (i.val + 1) := by
  apply List.ext_getElem
  · simp [filled]
  · intro k hk hk'
    have hkm : k < m := by simpa [filled] using hk'
    rw [List.getElem_set]
    by_cases hki : i.val = k
    · have hfin : i = (⟨k, hkm⟩ : Fin m) := Fin.ext hki
      simp [filled, hfin]
    · have hnext : k < i.val + 1 ↔ k < i.val := by omega
      simp only [hki, ↓reduceIte, filled, List.getElem_ofFn]
      change (if k < i.val then ∑ j, A ⟨k, hkm⟩ j * c j else 0) =
        (if k < i.val + 1 then ∑ j, A ⟨k, hkm⟩ j * c j else 0)
      simp only [hnext]

def matrixVectorStep : Com :=
  .seq (matrixRowDot "ell.shape" "ell.normal")
    (.seq (storeDotAtRow "ell.u") (.assign "row.i" (.add (.var "row.i") (.lit 1))))

def VectorInvariant (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (σ : Env) : Prop :=
  MatrixRows "ell.shape" A σ ∧ Represents "ell.normal" (List.ofFn c) σ ∧
    Represents "ell.u" (filled A c (σ.vars "row.i")) σ ∧ σ.vars "row.i" ≤ n ∧
    σ.vars "row.m" = n ∧ σ.vars "vec.n" = n

theorem matrixVectorStep_spec (B n H : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ)
    (hH : 1 ≤ H) (hA : ∀ k j, Height (A k j) H) (hc : ∀ j, Height (c j) H)
    (hdims : n + n + n * n + 1 < B) (hB : 2 * (cap n H) ^ 2 + 3 < B) :
    Spec B (fun σ => VectorInvariant n A c σ ∧ σ.vars "row.i" < n)
      matrixVectorStep
      (fun σ τ => VectorInvariant n A c τ ∧ τ.vars "row.i" = σ.vars "row.i" + 1)
      (4 + ((144 * (cap n H).size + 216 + 4) * n + 12) + 21 + 4) := by
  rintro σ ⟨⟨hσA, hσc, hσu, hσin, hσm, hσn⟩, hσi⟩
  let i : Fin n := ⟨σ.vars "row.i", hσi⟩
  have hrow := spec_with_fields ["row.i", "row.m", "vec.n"]
    (matrixRowDot_spec B n n H "ell.shape" "ell.normal" A c i hH hA hc hdims hB)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;>
      simp [matrixRowDot, rowDotProduct, rowDotStep, multiplyRowAt, loadRowLeft, loadRight,
        addToAccumulator, addFraction, multiplyFraction, RamArithmetic.normalizeFraction,
        RamArithmetic.gcdLoop, RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.wvars])
    (by simp [matrixRowDot, rowDotProduct, rowDotStep, multiplyRowAt, loadRowLeft, loadRight,
        addToAccumulator, addFraction, multiplyFraction, RamArithmetic.normalizeFraction,
        RamArithmetic.gcdLoop, RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.warrs])
  obtain ⟨τ, hr₁, ⟨hτq, hτa⟩, hτfields, _⟩ := hrow σ ⟨hσA, hσc, rfl, hσn⟩
  have hτu : Represents "ell.u" (filled A c i.val) τ := by
    simpa only [Represents, hτa] using hσu
  have hτi : τ.vars "row.i" = i.val := hτfields _ (by simp)
  have hsum : Height (∑ j, A i j * c j) (cap n H) := by
    rw [← prefix_ofFn]
    apply prefix_height _ _ n H n hH (by simp) (by simp) le_rfl
    · intro q hq; simp only [List.mem_ofFn] at hq; obtain ⟨j, rfl⟩ := hq; exact hA i j
    · intro q hq; simp only [List.mem_ofFn] at hq; obtain ⟨j, rfl⟩ := hq; exact hc j
  have hcapB : cap n H < B := by nlinarith
  have hiB : i.val < B := by have := i.isLt; omega
  have h1 : 1 < B := by nlinarith
  obtain ⟨υ, hr₂, hυu, hυfields, hυarr⟩ := storeDotAtRow_spec B i.val "ell.u"
    (filled A c i.val) (∑ j, A i j * c j) (by simp [filled]) hiB h1
    (hsum.1.trans_lt hcapB) (hsum.2.trans_lt hcapB) τ ⟨hτu, hτq, hτi⟩
  have hυi : υ.vars "row.i" = i.val := (hυfields _ (by simp)).trans hτi
  have hnB : n < B := by omega
  have hi1B : i.val + 1 < B := lt_of_le_of_lt (by have := i.isLt; omega) hnB
  have hυiB : υ.vars "row.i" < B := hυi ▸ hiB
  have hsumB : Bop.add.apply (υ.vars "row.i") 1 < B := by simpa [Bop.apply, hυi] using hi1B
  have hr₃ : Run B (.assign "row.i" (.add (.var "row.i") (.lit 1))) υ
      (υ.setVar "row.i" (i.val + 1)) 4 := by
    exact Run.assign (by simpa [Bop.apply, hυi] using
      (evalB_bin (evalB_var hυiB) (evalB_lit h1) hsumB))
  have hυA : MatrixRows "ell.shape" A υ := by
    simpa only [MatrixRows, Slice, hυarr ("ell.shape" ++ ".s") (by decide),
      hυarr ("ell.shape" ++ ".n") (by decide), hυarr ("ell.shape" ++ ".d") (by decide), hτa] using hσA
  have hυc : Represents "ell.normal" (List.ofFn c) υ := by
    simpa only [Represents, hυarr ("ell.normal" ++ ".s") (by decide),
      hυarr ("ell.normal" ++ ".n") (by decide), hυarr ("ell.normal" ++ ".d") (by decide), hτa] using hσc
  have hυm : υ.vars "row.m" = n :=
    (hυfields _ (by simp)).trans ((hτfields _ (by simp)).trans hσm)
  have hυn : υ.vars "vec.n" = n :=
    (hυfields _ (by simp)).trans ((hτfields _ (by simp)).trans hσn)
  refine ⟨_, (hr₁.seq (hr₂.seq hr₃)).mono (by omega), ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [MatrixRows, Slice, arrs_setVar] using hυA
  · simpa only [Represents, arrs_setVar] using hυc
  · simpa only [Represents, arrs_setVar, vars_setVar, ite_true, filled_step] using hυu
  · change i.val + 1 ≤ n
    exact i.isLt
  · simpa using hυm
  · simpa using hυn
  · simp [i]

def ellipsoidMulVec : Com :=
  .seq (.assign "row.m" (.var "vec.n"))
    (.seq (.assign "row.i" (.lit 0))
      (.while (.lt (.var "row.i") (.var "row.m")) matrixVectorStep))

theorem ellipsoidMulVec_spec (B n H : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ)
    (hH : 1 ≤ H) (hA : ∀ k j, Height (A k j) H) (hc : ∀ j, Height (c j) H)
    (hdims : n + n + n * n + 1 < B) (hB : 2 * (cap n H) ^ 2 + 3 < B) :
    Spec B (fun σ => MatrixRows "ell.shape" A σ ∧ Represents "ell.normal" (List.ofFn c) σ ∧
        Represents "ell.u" (List.replicate n 0) σ ∧ σ.vars "vec.n" = n)
      ellipsoidMulVec
      (fun _ τ => Represents "ell.u" (List.ofFn (A *ᵥ c)) τ ∧ MatrixRows "ell.shape" A τ ∧
        Represents "ell.normal" (List.ofFn c) τ ∧ τ.vars "vec.n" = n)
      (((4 + ((144 * (cap n H).size + 216 + 4) * n + 12) + 21 + 4) + 4) * n + 8) := by
  have hnB : n < B := by omega
  have hlo := Spec.forRangeZero "row.i" "row.m" (VectorInvariant n A c) n
    (4 + ((144 * (cap n H).size + 216 + 4) * n + 12) + 21 + 4) hnB
    (fun _ h => h.2.2.2.1) (fun _ h => h.2.2.2.2.1)
    (matrixVectorStep_spec B n H A c hH hA hc hdims hB)
  rintro σ ⟨hσA, hσc, hσu, hσn⟩
  run_vcg [hlo]
  all_goals clear hlo
  all_goals simp_all [VectorInvariant, MatrixRows, Slice, Represents, filled_zero, filled_done]

def ellipsoidMulVecInitialized : Com := .seq (RamZeroArray.zeroRationalArray "ell.u") ellipsoidMulVec

theorem ellipsoidMulVecInitialized_spec (B n H : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ)
    (hH : 1 ≤ H) (hA : ∀ k j, Height (A k j) H) (hc : ∀ j, Height (c j) H)
    (hdims : n + n + n * n + 1 < B) (hB : 2 * (cap n H) ^ 2 + 3 < B) :
    Spec B (fun σ => MatrixRows "ell.shape" A σ ∧ Represents "ell.normal" (List.ofFn c) σ ∧
        (σ.arrs "ell.u.s").length = n ∧ (σ.arrs "ell.u.n").length = n ∧
        (σ.arrs "ell.u.d").length = n ∧ σ.vars "vec.n" = n)
      ellipsoidMulVecInitialized
      (fun _ τ => Represents "ell.u" (List.ofFn (A *ᵥ c)) τ ∧ MatrixRows "ell.shape" A τ ∧
        Represents "ell.normal" (List.ofFn c) τ ∧ τ.vars "vec.n" = n)
      (33 * n + 18 + (((4 + ((144 * (cap n H).size + 216 + 4) * n + 12) + 21 + 4) + 4) * n + 8)) := by
  have hnB : n < B := by omega
  have h1 : 1 < B := by nlinarith
  rintro σ ⟨hσA, hσc, hσus, hσun, hσud, hσn⟩
  obtain ⟨τ, hr₁, hτu, hτn, hτa⟩ := RamZeroArray.zeroRationalArray_spec B n "ell.u" hnB h1
    σ ⟨hσus, hσun, hσud, hσn⟩
  have hτA : MatrixRows "ell.shape" A τ := by
    simpa only [MatrixRows, Slice, hτa ("ell.shape" ++ ".s") (by decide),
      hτa ("ell.shape" ++ ".n") (by decide), hτa ("ell.shape" ++ ".d") (by decide)] using hσA
  have hτc : Represents "ell.normal" (List.ofFn c) τ := by
    simpa only [Represents, hτa ("ell.normal" ++ ".s") (by decide),
      hτa ("ell.normal" ++ ".n") (by decide), hτa ("ell.normal" ++ ".d") (by decide)] using hσc
  obtain ⟨υ, hr₂, hυ⟩ := ellipsoidMulVec_spec B n H A c hH hA hc hdims hB τ ⟨hτA, hτc, hτu, hτn⟩
  exact ⟨υ, hr₁.seq hr₂, hυ⟩

theorem ellipsoidMulVec_cost_polynomial (n H : ℕ) :
    33 * n + 18 + (((4 + ((144 * (cap n H).size + 216 + 4) * n + 12) + 21 + 4) + 4) * n + 8) ≤
      (144 * ((n + 1) * (2 * H.size + 3) + 1) + 220) * n ^ 2 + 78 * n + 26 := by
  have hm := Nat.mul_le_mul_right (n * n)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 144 (cap_size n H)) 220)
  convert Nat.add_le_add_right hm (78 * n + 26) using 1 <;> ring

theorem mulVec_height (n H : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ)
    (hH : 1 ≤ H) (hA : ∀ k j, Height (A k j) H) (hc : ∀ j, Height (c j) H) (i : Fin n) :
    Height ((A *ᵥ c) i) (cap n H) := by
  change Height (∑ j, A i j * c j) (cap n H)
  rw [← prefix_ofFn]
  apply prefix_height _ _ n H n hH (by simp) (by simp) le_rfl
  · intro q hq; simp only [List.mem_ofFn] at hq; obtain ⟨j, rfl⟩ := hq; exact hA i j
  · intro q hq; simp only [List.mem_ofFn] at hq; obtain ⟨j, rfl⟩ := hq; exact hc j

end Lax109476Proofs.RamMatrixVector

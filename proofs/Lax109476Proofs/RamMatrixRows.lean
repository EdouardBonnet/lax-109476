import Lax109476Proofs.RationalSeparation
import Lax109476Proofs.RamRationalArrays
import Lax109476Proofs.RamDotProduct

open scoped BigOperators

namespace Lax109476Proofs.RamMatrixRows

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamFrame RamRational RamPrimitiveBounds RamDotProduct RationalArithmeticBounds

/-- A row occupies a bounded slice of three arrays. The arrays may contain
other rows before or after this slice. -/
def Slice (a : String) (qs : List ℚ) (base : ℕ) (σ : Env) : Prop :=
  base + qs.length ≤ (σ.arrs (a ++ ".s")).length ∧
  base + qs.length ≤ (σ.arrs (a ++ ".n")).length ∧
  base + qs.length ≤ (σ.arrs (a ++ ".d")).length ∧
  (∀ i (hi : i < qs.length), (σ.arrs (a ++ ".s")).getD (base + i) 0 = rationalSign qs[i]) ∧
  (∀ i (hi : i < qs.length), (σ.arrs (a ++ ".n")).getD (base + i) 0 = qs[i].num.natAbs) ∧
  (∀ i (hi : i < qs.length), (σ.arrs (a ++ ".d")).getD (base + i) 0 = qs[i].den)

theorem slice_of_represents (a : String) (qs : List ℚ) (σ : Env)
    (h : Represents a qs σ) : Slice a qs 0 σ := by
  rcases h with ⟨hs, hn, hd⟩
  simp only [Slice, hs, hn, hd, List.length_map, Nat.zero_add]
  exact ⟨le_rfl, le_rfl, le_rfl, fun i hi => map_getD _ _ _ hi,
    fun i hi => map_getD _ _ _ hi, fun i hi => map_getD _ _ _ hi⟩

def loadRowLeft (a : String) : Com :=
  .seq (.assign "left.s" (.get (a ++ ".s") (.add (.var "row.base") (.var "vec.i"))))
    (.seq (.assign "left.n" (.get (a ++ ".n") (.add (.var "row.base") (.var "vec.i"))))
      (.assign "left.d" (.get (a ++ ".d") (.add (.var "row.base") (.var "vec.i")))))

theorem loadRowLeft_spec (B base i : ℕ) (a : String) (qs : List ℚ) (hi : i < qs.length)
    (hB : 1 < B) (hiB : base + i < B)
    (hn : qs[i].num.natAbs < B) (hd : qs[i].den < B) :
    Spec B (fun σ => Slice a qs base σ ∧ σ.vars "row.base" = base ∧ σ.vars "vec.i" = i)
      (loadRowLeft a) (fun _ τ => LeftOutput qs[i] τ) 15 := by
  rintro σ ⟨⟨hsl, hnl, hdl, hsg, hng, hdg⟩, hbase, hidx⟩
  have hsB := (rationalSign_le_one qs[i]).trans_lt hB
  have hbaseB : base < B := by omega
  have hidxB : i < B := by omega
  have hsl' : base + i < (σ.arrs (a ++ ".s")).length := by omega
  have hnl' : base + i < (σ.arrs (a ++ ".n")).length := by omega
  have hdl' : base + i < (σ.arrs (a ++ ".d")).length := by omega
  have hs := hsg i hi
  have hn' := hng i hi
  have hd' := hdg i hi
  clear hsg hng hdg
  run_vcg
  all_goals simp_all [LeftOutput]

theorem slice_of_sublist (a : String) (qs : List ℚ) (base n : ℕ) (σ : Env)
    (h : Represents a qs σ) (hlen : base + n ≤ qs.length) :
    Slice a ((qs.drop base).take n) base σ := by
  rcases h with ⟨hs, hn, hd⟩
  have hrow : ((qs.drop base).take n).length = n := by simp; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hs, hrow] using hlen
  · simpa [hn, hrow] using hlen
  · simpa [hd, hrow] using hlen
  · intro i hi
    have hix : base + i < qs.length := by rw [hrow] at hi; omega
    rw [hs, map_getD _ _ _ hix]
    congr 1
    simp
  · intro i hi
    have hix : base + i < qs.length := by rw [hrow] at hi; omega
    rw [hn, map_getD _ _ _ hix]
    congr 1
    simp
  · intro i hi
    have hix : base + i < qs.length := by rw [hrow] at hi; omega
    rw [hd, map_getD _ _ _ hix]
    congr 1
    simp

def multiplyRowAt (a b : String) : Com :=
  .seq (loadRowLeft a) (.seq (loadRight b) multiplyFraction)

theorem multiplyRowAt_spec (B M base i : ℕ) (a b : String) (xs ys : List ℚ)
    (hix : i < xs.length) (hiy : i < ys.length) (hiB : base + i < B)
    (hB : 2 * M ^ 2 + 3 < B) (hx : Height xs[i] M) (hy : Height ys[i] M) :
    Spec B (fun σ => Slice a xs base σ ∧ Represents b ys σ ∧
        σ.vars "row.base" = base ∧ σ.vars "vec.i" = i)
      (multiplyRowAt a b) (fun _ τ => FractionOutput (xs[i] * ys[i]) τ)
      (72 * M.size + 88) := by
  have hM : M < B := by nlinarith
  have h1 : 1 < B := by nlinarith
  have hii : i < B := by omega
  rintro σ ⟨hσx, hσy, hσbase, hσi⟩
  have hload := spec_with_fields ["vec.i"]
    (loadRowLeft_spec B base i a xs hix h1 hiB (hx.1.trans_lt hM) (hx.2.trans_lt hM))
    (by intro x hx; simp at hx; subst x; simp [loadRowLeft, Com.wvars])
    (by simp [loadRowLeft, Com.warrs])
  obtain ⟨τ, hr₁, hτx, hτf, hτa⟩ := hload σ ⟨hσx, hσbase, hσi⟩
  have hτy : Represents b ys τ := by simpa only [Represents, hτa] using hσy
  have hτi : τ.vars "vec.i" = i := (hτf _ (by simp)).trans hσi
  obtain ⟨υ, hr₂, hυy, hυi, hυa, hυs, hυn, hυd⟩ := loadRight_frame_spec B b ys i hiy h1 hii
    (hy.1.trans_lt hM) (hy.2.trans_lt hM) τ ⟨hτy, hτi⟩
  have hυx : LeftOutput xs[i] υ := by simpa only [LeftOutput, hυs, hυn, hυd] using hτx
  obtain ⟨ρ, hr₃, hρ⟩ := multiplyFraction_uniform_spec B M
    (rationalSign xs[i]) xs[i].num.natAbs xs[i].den
    (rationalSign ys[i]) ys[i].num.natAbs ys[i].den hB
    (rationalSign_le_one _) (rationalSign_le_one _) hx.1 hx.2 hy.1 hy.2 xs[i].den_pos ys[i].den_pos
    υ ⟨hυx.1, hυx.2.1, hυx.2.2, hυy.1, hυy.2.1, hυy.2.2⟩
  refine ⟨ρ, (hr₁.seq (hr₂.seq hr₃)).mono (by omega), ?_⟩
  simpa only [canonical_fractionValue] using hρ

def rowFields : List String := ["dot.s", "dot.n", "dot.d", "vec.i", "vec.n", "row.base"]

theorem multiplyRowAt_frame_spec (B M base i : ℕ) (a b : String) (xs ys : List ℚ)
    (hix : i < xs.length) (hiy : i < ys.length) (hiB : base + i < B)
    (hB : 2 * M ^ 2 + 3 < B) (hx : Height xs[i] M) (hy : Height ys[i] M) :
    Spec B (fun σ => Slice a xs base σ ∧ Represents b ys σ ∧
        σ.vars "row.base" = base ∧ σ.vars "vec.i" = i)
      (multiplyRowAt a b) (fun σ τ => FractionOutput (xs[i] * ys[i]) τ ∧
        FieldsAgree rowFields σ τ ∧ τ.arrs = σ.arrs) (72 * M.size + 88) := by
  apply spec_with_fields rowFields
    (multiplyRowAt_spec B M base i a b xs ys hix hiy hiB hB hx hy)
  · intro x hx
    simp [rowFields] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [multiplyRowAt, loadRowLeft, loadRight, multiplyFraction, RamArithmetic.normalizeFraction,
      RamArithmetic.gcdLoop, RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.wvars]
  · simp [multiplyRowAt, loadRowLeft, loadRight, multiplyFraction, RamArithmetic.normalizeFraction,
      RamArithmetic.gcdLoop, RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.warrs]

def rowDotStep (a b : String) : Com := .seq (multiplyRowAt a b) addToAccumulator

def RowInvariant (a b : String) (xs ys : List ℚ) (base n : ℕ) (σ : Env) : Prop :=
  Slice a xs base σ ∧ Represents b ys σ ∧ σ.vars "vec.i" ≤ n ∧
    σ.vars "vec.n" = n ∧ σ.vars "row.base" = base ∧
    DotOutput (prefixValue xs ys (σ.vars "vec.i")) σ

theorem rowDotStep_spec (B base n H : ℕ) (a b : String) (xs ys : List ℚ)
    (hx : xs.length = n) (hy : ys.length = n) (hH : 1 ≤ H)
    (hxs : ∀ q ∈ xs, Height q H) (hys : ∀ q ∈ ys, Height q H)
    (hnB : base + n < B) (hB : 2 * (cap n H) ^ 2 + 3 < B) :
    Spec B (fun σ => RowInvariant a b xs ys base n σ ∧ σ.vars "vec.i" < n)
      (rowDotStep a b)
      (fun σ τ => RowInvariant a b xs ys base n τ ∧ τ.vars "vec.i" = σ.vars "vec.i" + 1)
      (144 * (cap n H).size + 216) := by
  rintro σ ⟨⟨hσx, hσy, hσin, hσn, hσbase, hσq⟩, hσi⟩
  let i := σ.vars "vec.i"
  have hix : i < xs.length := by dsimp [i]; omega
  have hiy : i < ys.length := by dsimp [i]; omega
  have hcap := cap_ge n H hH
  have hxq := hxs _ (List.getElem_mem hix)
  have hyq := hys _ (List.getElem_mem hiy)
  have hprefix := prefix_height xs ys n H i hH hx hy hσin hxs hys
  have hproduct := height_mono _ (height_mul _ _ H H hxq hyq) hcap.1
  obtain ⟨τ, hr₁, hτp, hτf, hτa⟩ := multiplyRowAt_frame_spec B (cap n H) base i a b xs ys hix hiy
    (by dsimp [i]; omega) hB (height_mono _ hxq hcap.2) (height_mono _ hyq hcap.2)
    σ ⟨hσx, hσy, hσbase, rfl⟩
  have hτi : τ.vars "vec.i" = i := hτf _ (by simp [rowFields])
  have hτn : τ.vars "vec.n" = σ.vars "vec.n" := hτf _ (by simp [rowFields])
  have hτbase : τ.vars "row.base" = base := (hτf _ (by simp [rowFields])).trans hσbase
  have hτq : DotOutput (prefixValue xs ys i) τ := by
    simpa only [DotOutput, hτf "dot.s" (by simp [rowFields]),
      hτf "dot.n" (by simp [rowFields]), hτf "dot.d" (by simp [rowFields])] using hσq
  obtain ⟨υ, hr₂, hυq, hυi, hυn, hυa⟩ := addToAccumulator_spec B (cap n H) i
    (prefixValue xs ys i) (xs[i] * ys[i]) hB hprefix hproduct
    (by dsimp [i]; omega) τ ⟨hτq, hτp, hτi⟩
  have hυbase : υ.vars "row.base" = base :=
    (hr₂.frame_var "row.base" (by
      simp [addToAccumulator, addFraction, RamArithmetic.normalizeFraction,
        RamArithmetic.gcdLoop, RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.wvars])).trans hτbase
  have hsum : prefixValue xs ys (i + 1) = prefixValue xs ys i + xs[i] * ys[i] := by
    rw [prefix_succ]
    simp [List.getD_eq_getElem?_getD, hix, hiy]
  refine ⟨υ, (hr₁.seq hr₂).mono (by omega), ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, hυbase, ?_⟩, hυi⟩
  · simpa only [Slice, hυa, hτa] using hσx
  · simpa only [Represents, hυa, hτa] using hσy
  · rw [hυi]; dsimp [i]; omega
  · rw [hυn, hτn, hσn]
  · rw [hυi, hsum]; exact hυq

def rowDotProduct (a b : String) : Com :=
  .seq (.assign "dot.s" (.lit 0))
    (.seq (.assign "dot.n" (.lit 0))
      (.seq (.assign "dot.d" (.lit 1))
        (.seq (.assign "vec.i" (.lit 0))
          (.while (.lt (.var "vec.i") (.var "vec.n")) (rowDotStep a b)))))

theorem rowDotProduct_spec (B base n H : ℕ) (a b : String) (xs ys : List ℚ)
    (hx : xs.length = n) (hy : ys.length = n) (hH : 1 ≤ H)
    (hxs : ∀ q ∈ xs, Height q H) (hys : ∀ q ∈ ys, Height q H)
    (hnB : base + n < B) (hB : 2 * (cap n H) ^ 2 + 3 < B) :
    Spec B (fun σ => Slice a xs base σ ∧ Represents b ys σ ∧
        σ.vars "row.base" = base ∧ σ.vars "vec.n" = n)
      (rowDotProduct a b)
      (fun _ τ => DotOutput (prefixValue xs ys n) τ ∧ Slice a xs base τ ∧
        Represents b ys τ ∧ τ.vars "vec.i" = n ∧ τ.vars "vec.n" = n ∧
        τ.vars "row.base" = base)
      ((144 * (cap n H).size + 216 + 4) * n + 12) := by
  have hn : n < B := by omega
  have hlo := Spec.forRangeZero "vec.i" "vec.n" (RowInvariant a b xs ys base n) n
    (144 * (cap n H).size + 216) hn
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2.1)
    (rowDotStep_spec B base n H a b xs ys hx hy hH hxs hys hnB hB)
  have h1 : 1 < B := by nlinarith
  rintro σ ⟨hσx, hσy, hσbase, hσn⟩
  run_vcg [hlo]
  all_goals clear hlo
  all_goals simp_all [RowInvariant, DotOutput, Slice, Represents, prefix_zero, fractionValue]
  all_goals first | omega | aesop

theorem rowDotProduct_frame_spec (B base n H : ℕ) (a b : String) (xs ys : List ℚ)
    (hx : xs.length = n) (hy : ys.length = n) (hH : 1 ≤ H)
    (hxs : ∀ q ∈ xs, Height q H) (hys : ∀ q ∈ ys, Height q H)
    (hnB : base + n < B) (hB : 2 * (cap n H) ^ 2 + 3 < B) :
    Spec B (fun σ => Slice a xs base σ ∧ Represents b ys σ ∧
        σ.vars "row.base" = base ∧ σ.vars "vec.n" = n)
      (rowDotProduct a b)
      (fun σ τ => DotOutput (prefixValue xs ys n) τ ∧ τ.arrs = σ.arrs)
      ((144 * (cap n H).size + 216 + 4) * n + 12) := by
  have h := spec_with_fields []
    (rowDotProduct_spec B base n H a b xs ys hx hy hH hxs hys hnB hB)
    (by simp) (by
      simp [rowDotProduct, rowDotStep, multiplyRowAt, loadRowLeft, loadRight, addToAccumulator,
        addFraction, multiplyFraction, RamArithmetic.normalizeFraction, RamArithmetic.gcdLoop,
        RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.warrs])
  intro σ hσ
  obtain ⟨τ, hr, hq, _, ha⟩ := h σ hσ
  exact ⟨τ, hr, hq.1, ha⟩

/-- Row-major representation; every row has its explicit bounded slice. -/
def MatrixRows {m n : ℕ} (a : String) (A : Matrix (Fin m) (Fin n) ℚ) (σ : Env) : Prop :=
  ∀ i, Slice a (List.ofFn (A i)) (i.val * n) σ

def matrixRowDot (a b : String) : Com :=
  .seq (.assign "row.base" (.mul (.var "row.i") (.var "vec.n"))) (rowDotProduct a b)

theorem matrixRowDot_spec (B m n H : ℕ) (a b : String)
    (A : Matrix (Fin m) (Fin n) ℚ) (c : Fin n → ℚ) (i : Fin m)
    (hH : 1 ≤ H) (hA : ∀ k j, Height (A k j) H) (hc : ∀ j, Height (c j) H)
    (hdims : m + n + m * n + 1 < B) (hB : 2 * (cap n H) ^ 2 + 3 < B) :
    Spec B (fun σ => MatrixRows a A σ ∧ Represents b (List.ofFn c) σ ∧
        σ.vars "row.i" = i.val ∧ σ.vars "vec.n" = n)
      (matrixRowDot a b)
      (fun σ τ => DotOutput (∑ j, A i j * c j) τ ∧ τ.arrs = σ.arrs)
      (4 + ((144 * (cap n H).size + 216 + 4) * n + 12)) := by
  have hindex : i.val * n + n < B := by
    have hmul := Nat.mul_le_mul_right n (by omega : i.val + 1 ≤ m)
    nlinarith
  have hiB : i.val < B := by have := i.isLt; omega
  have hnB : n < B := by omega
  have hbaseB : i.val * n < B := by omega
  have hxs : ∀ q ∈ List.ofFn (A i), Height q H := by
    intro q hq
    simp only [List.mem_ofFn] at hq
    obtain ⟨j, rfl⟩ := hq
    exact hA i j
  have hys : ∀ q ∈ List.ofFn c, Height q H := by
    intro q hq
    simp only [List.mem_ofFn] at hq
    obtain ⟨j, rfl⟩ := hq
    exact hc j
  have hrow := rowDotProduct_frame_spec B (i.val * n) n H a b (List.ofFn (A i))
    (List.ofFn c) (by simp) (by simp) hH hxs hys hindex hB
  rintro σ ⟨hσA, hσc, hσi, hσn⟩
  have hslice := hσA i
  clear hσA
  run_vcg [hrow]
  all_goals clear hrow
  all_goals simp_all [prefix_ofFn, Slice]
  all_goals first | omega | aesop

end Lax109476Proofs.RamMatrixRows

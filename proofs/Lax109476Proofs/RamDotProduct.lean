import Lax109476Proofs.RamRationalArrays
import Lax109476Proofs.RamPrimitiveBounds
import Lax109476Proofs.RamFrame

open scoped BigOperators

namespace Lax109476Proofs.RamDotProduct

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamPrimitiveBounds RamFrame RationalArithmeticBounds

def prefixValue (xs ys : List ℚ) (k : ℕ) : ℚ :=
  ∑ i ∈ Finset.range k, xs.getD i 0 * ys.getD i 0

theorem prefix_zero (xs ys : List ℚ) : prefixValue xs ys 0 = 0 := by simp [prefixValue]

theorem prefix_succ (xs ys : List ℚ) (k : ℕ) :
    prefixValue xs ys (k + 1) = prefixValue xs ys k + xs.getD k 0 * ys.getD k 0 := by
  simp [prefixValue, Finset.sum_range_succ]

def cap (n H : ℕ) : ℕ := (2 * (H * H)) ^ (n + 1)

theorem cap_ge (n H : ℕ) (hH : 1 ≤ H) : H * H ≤ cap n H ∧ H ≤ cap n H := by
  have hb : 1 ≤ 2 * (H * H) := by nlinarith
  have hp := le_self_pow hb (by omega : n + 1 ≠ 0)
  change H * H ≤ (2 * (H * H)) ^ (n + 1) ∧ H ≤ (2 * (H * H)) ^ (n + 1)
  constructor <;> nlinarith

theorem prefix_height (xs ys : List ℚ) (n H k : ℕ) (hH : 1 ≤ H)
    (hx : xs.length = n) (hy : ys.length = n) (hk : k ≤ n)
    (hxs : ∀ q ∈ xs, Height q H) (hys : ∀ q ∈ ys, Height q H) :
    Height (prefixValue xs ys k) (cap n H) := by
  have hf : ∀ i ∈ Finset.range k, Height (xs.getD i 0 * ys.getD i 0) (H * H) := by
    intro i hi
    have hix : i < xs.length := by have h := Finset.mem_range.mp hi; omega
    have hiy : i < ys.length := by have h := Finset.mem_range.mp hi; omega
    have hxq : xs.getD i 0 = xs[i] := by simp [List.getD_eq_getElem?_getD, hix]
    have hyq : ys.getD i 0 = ys[i] := by simp [List.getD_eq_getElem?_getD, hiy]
    rw [hxq, hyq]
    exact height_mul _ _ H H (hxs _ (List.getElem_mem hix)) (hys _ (List.getElem_mem hiy))
  have hs := height_sum (Finset.range k) (fun i => xs.getD i 0 * ys.getD i 0) (H * H) hf
  simp only [Finset.card_range] at hs
  exact height_mono _ hs (Nat.pow_le_pow_right (by nlinarith) (by omega))

def multiplyAt (a b : String) : Com :=
  .seq (loadLeft a) (.seq (loadRight b) multiplyFraction)

theorem multiplyAt_spec (B M : ℕ) (a b : String) (xs ys : List ℚ) (i : ℕ)
    (hix : i < xs.length) (hiy : i < ys.length) (hiB : i < B)
    (hB : 2 * M ^ 2 + 3 < B) (hx : Height xs[i] M) (hy : Height ys[i] M) :
    Spec B (fun σ => Represents a xs σ ∧ Represents b ys σ ∧ σ.vars "vec.i" = i)
      (multiplyAt a b) (fun _ τ => FractionOutput (xs[i] * ys[i]) τ)
      (72 * M.size + 82) := by
  have hM : M < B := by nlinarith
  have h1 : 1 < B := by nlinarith
  rintro σ ⟨hσx, hσy, hσi⟩
  obtain ⟨τ, hr₁, hτx, hτi, hτa⟩ := loadLeft_frame_spec B a xs i hix h1 hiB
    (hx.1.trans_lt hM) (hx.2.trans_lt hM) σ ⟨hσx, hσi⟩
  have hτy : Represents b ys τ := by simpa only [Represents, hτa] using hσy
  obtain ⟨υ, hr₂, hυy, hυi, hυa, hυs, hυn, hυd⟩ := loadRight_frame_spec B b ys i hiy h1 hiB
    (hy.1.trans_lt hM) (hy.2.trans_lt hM) τ ⟨hτy, hτi⟩
  have hυx : LeftOutput xs[i] υ := by simpa only [LeftOutput, hυs, hυn, hυd] using hτx
  obtain ⟨ρ, hr₃, hρ⟩ := multiplyFraction_uniform_spec B M
    (rationalSign xs[i]) xs[i].num.natAbs xs[i].den
    (rationalSign ys[i]) ys[i].num.natAbs ys[i].den hB
    (rationalSign_le_one _) (rationalSign_le_one _) hx.1 hx.2 hy.1 hy.2 xs[i].den_pos ys[i].den_pos
    υ ⟨hυx.1, hυx.2.1, hυx.2.2, hυy.1, hυy.2.1, hυy.2.2⟩
  refine ⟨ρ, (hr₁.seq (hr₂.seq hr₃)).mono (by omega), ?_⟩
  simpa only [canonical_fractionValue] using hρ

def loopFields : List String := ["dot.s", "dot.n", "dot.d", "vec.i", "vec.n"]

theorem multiplyAt_frame_spec (B M : ℕ) (a b : String) (xs ys : List ℚ) (i : ℕ)
    (hix : i < xs.length) (hiy : i < ys.length) (hiB : i < B)
    (hB : 2 * M ^ 2 + 3 < B) (hx : Height xs[i] M) (hy : Height ys[i] M) :
    Spec B (fun σ => Represents a xs σ ∧ Represents b ys σ ∧ σ.vars "vec.i" = i)
      (multiplyAt a b) (fun σ τ => FractionOutput (xs[i] * ys[i]) τ ∧
        FieldsAgree loopFields σ τ ∧ τ.arrs = σ.arrs) (72 * M.size + 82) := by
  apply spec_with_fields loopFields (multiplyAt_spec B M a b xs ys i hix hiy hiB hB hx hy)
  · intro x hx
    simp [loopFields] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    all_goals simp [multiplyAt, loadLeft, loadRight, multiplyFraction, RamArithmetic.normalizeFraction,
      RamArithmetic.gcdLoop, RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.wvars]
  · simp [multiplyAt, loadLeft, loadRight, multiplyFraction, RamArithmetic.normalizeFraction,
      RamArithmetic.gcdLoop, RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.warrs]

def DotOutput (q : ℚ) (σ : Env) : Prop :=
  fractionValue (σ.vars "dot.s") (σ.vars "dot.n") (σ.vars "dot.d") = q ∧
    σ.vars "dot.n" = q.num.natAbs ∧ σ.vars "dot.d" = q.den ∧ σ.vars "dot.s" ≤ 1

def addToAccumulator : Com :=
  .seq (.assign "right.s" (.var "rat.s")) (.seq (.assign "right.n" (.var "rat.n")) (.seq (.assign "right.d" (.var "rat.d")) (.seq (.assign "left.s" (.var "dot.s")) (.seq (.assign "left.n" (.var "dot.n")) (.seq (.assign "left.d" (.var "dot.d")) (.seq (addFraction) (.seq (.assign "dot.s" (.var "rat.s")) (.seq (.assign "dot.n" (.var "rat.n")) (.seq (.assign "dot.d" (.var "rat.d")) (.assign "vec.i" (.add (.var "vec.i") (.lit 1))))))))))))

set_option maxHeartbeats 800000 in
theorem addToAccumulator_spec (B M i : ℕ) (q r : ℚ)
    (hB : 2 * M ^ 2 + 3 < B) (hq : Height q M) (hr : Height r M)
    (hi : i + 1 < B) :
    Spec B (fun σ => DotOutput q σ ∧ FractionOutput r σ ∧ σ.vars "vec.i" = i)
      addToAccumulator
      (fun σ τ => DotOutput (q + r) τ ∧ τ.vars "vec.i" = i + 1 ∧
        τ.vars "vec.n" = σ.vars "vec.n" ∧ τ.arrs = σ.arrs)
      (72 * M.size + 128) := by
  have hM : M < B := by nlinarith
  have h1 : 1 < B := by nlinarith
  rintro σ ⟨hqσ, hrσ, hiσ⟩
  have hqval := hqσ.1
  have hrval := hrσ.1
  have hadd := addFraction_uniform_spec B M (σ.vars "dot.s") q.num.natAbs q.den
    (σ.vars "rat.s") r.num.natAbs r.den hB hqσ.2.2.2 hrσ.2.2.2
    hq.1 hq.2 hr.1 hr.2 q.den_pos r.den_pos
  have hframe := spec_with_fields ["vec.i", "vec.n"] hadd
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;>
        simp [addFraction, RamArithmetic.normalizeFraction, RamArithmetic.gcdLoop,
          RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.wvars])
    (by simp [addFraction, RamArithmetic.normalizeFraction, RamArithmetic.gcdLoop,
          RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.warrs])
  have hqnum := hqσ.2.1
  have hqden := hqσ.2.2.1
  have hrnum := hrσ.2.1
  have hrden := hrσ.2.2.1
  have hqs := hqσ.2.2.2.trans_lt h1
  have hrs := hrσ.2.2.2.trans_lt h1
  have hqn := hq.1.trans_lt hM
  have hqd := hq.2.trans_lt hM
  have hrn := hr.1.trans_lt hM
  have hrd := hr.2.trans_lt hM
  have hsum := height_add q r M M hq hr
  have hsumN : (q + r).num.natAbs < B := hsum.1.trans_lt (by nlinarith)
  have hsumD : (q + r).den < B := hsum.2.trans_lt (by nlinarith)
  clear hadd
  run_vcg [hframe]
  all_goals clear hframe
  all_goals simp_all [DotOutput, FractionOutput, FieldsAgree, fractionInputs]
  all_goals first | omega | aesop

def dotStep (a b : String) : Com := .seq (multiplyAt a b) addToAccumulator

def LoopInvariant (a b : String) (xs ys : List ℚ) (n : ℕ) (σ : Env) : Prop :=
  Represents a xs σ ∧ Represents b ys σ ∧ σ.vars "vec.i" ≤ n ∧
    σ.vars "vec.n" = n ∧ DotOutput (prefixValue xs ys (σ.vars "vec.i")) σ

theorem dotStep_spec (B n H : ℕ) (a b : String) (xs ys : List ℚ)
    (hx : xs.length = n) (hy : ys.length = n) (hH : 1 ≤ H)
    (hxs : ∀ q ∈ xs, Height q H) (hys : ∀ q ∈ ys, Height q H)
    (hnB : n < B) (hB : 2 * (cap n H) ^ 2 + 3 < B) :
    Spec B (fun σ => LoopInvariant a b xs ys n σ ∧ σ.vars "vec.i" < n)
      (dotStep a b)
      (fun σ τ => LoopInvariant a b xs ys n τ ∧ τ.vars "vec.i" = σ.vars "vec.i" + 1)
      (144 * (cap n H).size + 210) := by
  rintro σ ⟨⟨hσx, hσy, hσin, hσn, hσq⟩, hσi⟩
  let i := σ.vars "vec.i"
  have hix : i < xs.length := by dsimp [i]; omega
  have hiy : i < ys.length := by dsimp [i]; omega
  have hcap := cap_ge n H hH
  have hxq := hxs _ (List.getElem_mem hix)
  have hyq := hys _ (List.getElem_mem hiy)
  have hprefix := prefix_height xs ys n H i hH hx hy hσin hxs hys
  have hproduct := height_mono _ (height_mul _ _ H H hxq hyq) hcap.1
  obtain ⟨τ, hr₁, hτp, hτf, hτa⟩ := multiplyAt_frame_spec B (cap n H) a b xs ys i hix hiy
    (hσi.trans hnB) hB (height_mono _ hxq hcap.2) (height_mono _ hyq hcap.2)
    σ ⟨hσx, hσy, rfl⟩
  have hτi : τ.vars "vec.i" = i := hτf _ (by simp [loopFields])
  have hτn : τ.vars "vec.n" = σ.vars "vec.n" := hτf _ (by simp [loopFields])
  have hτq : DotOutput (prefixValue xs ys i) τ := by
    simpa only [DotOutput, hτf "dot.s" (by simp [loopFields]),
      hτf "dot.n" (by simp [loopFields]), hτf "dot.d" (by simp [loopFields])] using hσq
  obtain ⟨υ, hr₂, hυq, hυi, hυn, hυa⟩ := addToAccumulator_spec B (cap n H) i
    (prefixValue xs ys i) (xs[i] * ys[i]) hB hprefix hproduct
    (lt_of_le_of_lt (by dsimp [i]; omega) hnB) τ ⟨hτq, hτp, hτi⟩
  have hsum : prefixValue xs ys (i + 1) = prefixValue xs ys i + xs[i] * ys[i] := by
    rw [prefix_succ]
    simp [List.getD_eq_getElem?_getD, hix, hiy]
  refine ⟨υ, (hr₁.seq hr₂).mono (by omega), ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hυi⟩
  · simpa only [Represents, hυa, hτa] using hσx
  · simpa only [Represents, hυa, hτa] using hσy
  · rw [hυi]; dsimp [i]; omega
  · rw [hυn, hτn, hσn]
  · rw [hυi, hsum]; exact hυq

def dotProduct (a b : String) : Com :=
  .seq (.assign "dot.s" (.lit 0))
    (.seq (.assign "dot.n" (.lit 0))
      (.seq (.assign "dot.d" (.lit 1))
        (.seq (.assign "vec.i" (.lit 0))
          (.while (.lt (.var "vec.i") (.var "vec.n")) (dotStep a b)))))

theorem dotProduct_spec (B n H : ℕ) (a b : String) (xs ys : List ℚ)
    (hx : xs.length = n) (hy : ys.length = n) (hH : 1 ≤ H)
    (hxs : ∀ q ∈ xs, Height q H) (hys : ∀ q ∈ ys, Height q H)
    (hnB : n < B) (hB : 2 * (cap n H) ^ 2 + 3 < B) :
    Spec B (fun σ => Represents a xs σ ∧ Represents b ys σ ∧ σ.vars "vec.n" = n)
      (dotProduct a b)
      (fun _ τ => DotOutput (prefixValue xs ys n) τ ∧ Represents a xs τ ∧
        Represents b ys τ ∧ τ.vars "vec.i" = n ∧ τ.vars "vec.n" = n)
      ((144 * (cap n H).size + 210 + 4) * n + 12) := by
  have hlo := Spec.forRangeZero "vec.i" "vec.n" (LoopInvariant a b xs ys n) n
    (144 * (cap n H).size + 210) hnB
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2.1)
    (dotStep_spec B n H a b xs ys hx hy hH hxs hys hnB hB)
  have h1 : 1 < B := by nlinarith
  rintro σ ⟨hσx, hσy, hσn⟩
  run_vcg [hlo]
  all_goals clear hlo
  all_goals simp_all [LoopInvariant, DotOutput, Represents, prefix_zero, fractionValue]
  all_goals first | omega | aesop

theorem cap_size (n H : ℕ) : (cap n H).size ≤ (n + 1) * (2 * H.size + 3) + 1 := by
  have hh := RationalSizeBounds.size_mul_le H H
  have ht := RationalSizeBounds.size_mul_le 2 (H * H)
  have hp := RationalSizeBounds.size_pow_le (2 * (H * H)) (n + 1)
  have htwo : Nat.size 2 = 2 := by decide
  have hb : (2 * (H * H)).size ≤ 2 * H.size + 3 := by omega
  have hm := Nat.mul_le_mul_left (n + 1) hb
  dsimp [cap]
  omega

theorem dotProduct_cost_polynomial (n H : ℕ) :
    (144 * (cap n H).size + 210 + 4) * n + 12 ≤
      (144 * ((n + 1) * (2 * H.size + 3) + 1) + 214) * n + 12 := by
  have hm := Nat.mul_le_mul_left 144 (cap_size n H)
  have hn := Nat.mul_le_mul_right n (Nat.add_le_add_right hm 214)
  convert Nat.add_le_add_right hn 12 using 1

theorem prefix_ofFn (n : ℕ) (x y : Fin n → ℚ) :
    prefixValue (List.ofFn x) (List.ofFn y) n = ∑ i, x i * y i := by
  rw [Finset.sum_fin_eq_sum_range]
  unfold prefixValue
  apply Finset.sum_congr rfl
  intro i hi
  have hin := Finset.mem_range.mp hi
  simp [List.getD_eq_getElem?_getD, hin]

end Lax109476Proofs.RamDotProduct

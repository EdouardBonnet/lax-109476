import Lax109476Proofs.RamBitLength
import Lax109476Proofs.RamReadBlock

namespace Lax109476Proofs.RamEncodedSize

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding
open RamBitLength RamFrame RamRationalArrays RationalArithmeticBounds EncodingSize

/-- Count the registered word encoding, including its separator. -/
def countWord (x : String) : Com := .seq (.assign "bits.v" (.var x))
  (.seq bitLength (.assign "size.total" (.add (.add (.var "size.total") (.var "bits.k")) (.lit 1))))

theorem countWord_spec (B a t : ℕ) (x : String) (h2 : 2 < B) (ha : a < B)
    (ht : t + a.size + 1 < B) :
    Spec B (fun σ => σ.vars x = a ∧ σ.vars "size.total" = t) (countWord x)
      (fun _ τ => τ.vars "size.total" = t + a.size + 1) (12 * a.size + 14) := by
  have htB : t < B := by omega
  have haddB : t + a.size < B := by omega
  have hsizeB : a.size < B := by omega
  have hbits := spec_with_fields ["size.total"] (bitLength_spec B a h2 ha)
    (by intro y hy; simp at hy; subst y; decide) (by decide)
  rintro σ ⟨hσx, hσt⟩
  run_vcg [hbits]
  all_goals clear hbits
  all_goals simp_all [FieldsAgree]
  all_goals omega

def countFraction : Com := .seq (countWord "left.s")
  (.seq (countWord "left.n") (countWord "left.d"))

theorem rational_bits (q : ℚ) : bitSize (encodeRational q) =
    (rationalSign q).size + q.num.natAbs.size + q.den.size + 3 := by
  simp only [encodeRational, rationalSign, bitSize_cons, bitSize_nil]
  omega

theorem countFraction_spec (B H t : ℕ) (q : ℚ) (h2 : 2 < B) (hH : 1 ≤ H)
    (hHB : H < B) (hq : Height q H) (ht : t + bitSize (encodeRational q) < B) :
    Spec B (fun σ => LeftOutput q σ ∧ σ.vars "size.total" = t) countFraction
      (fun _ τ => LeftOutput q τ ∧ τ.vars "size.total" = t + bitSize (encodeRational q))
      (36 * H.size + 42) := by
  have hsH := (rationalSign_le_one q).trans hH
  have hsB := hsH.trans_lt hHB
  have hnB := hq.1.trans_lt hHB
  have hdB := hq.2.trans_lt hHB
  have hbits := rational_bits q
  rintro σ ⟨⟨hσs, hσn, hσd⟩, hσt⟩
  obtain ⟨τ, hr₁, hτt⟩ := countWord_spec B (rationalSign q) t "left.s" h2 hsB (by omega)
    σ ⟨hσs, hσt⟩
  have hτn := (hr₁.frame_var "left.n" (by decide)).trans hσn
  have hτd := (hr₁.frame_var "left.d" (by decide)).trans hσd
  obtain ⟨υ, hr₂, hυt⟩ := countWord_spec B q.num.natAbs (t + (rationalSign q).size + 1)
    "left.n" h2 hnB (by omega) τ ⟨hτn, hτt⟩
  have hυd := (hr₂.frame_var "left.d" (by decide)).trans hτd
  obtain ⟨ξ, hr₃, hξt⟩ := countWord_spec B q.den
    (t + (rationalSign q).size + 1 + q.num.natAbs.size + 1) "left.d" h2 hdB (by omega)
      υ ⟨hυd, hυt⟩
  have hrun := hr₁.seq (hr₂.seq hr₃)
  have hss := Nat.size_le_size hsH
  have hns := Nat.size_le_size hq.1
  have hds := Nat.size_le_size hq.2
  refine ⟨ξ, hrun.mono (by omega), ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (hrun.frame_var "left.s" (by decide)).trans hσs
  · exact (hrun.frame_var "left.n" (by decide)).trans hσn
  · exact (hrun.frame_var "left.d" (by decide)).trans hσd
  · omega

def prefixBits {n : ℕ} (v : Fin n → ℚ) (k : ℕ) : ℕ :=
  bitSize ((List.ofFn v).take k |>.flatMap encodeRational)

theorem prefix_zero {n : ℕ} (v : Fin n → ℚ) : prefixBits v 0 = 0 := rfl

theorem prefix_done {n : ℕ} (v : Fin n → ℚ) : prefixBits v n = bitSize (encodeVector v) := by
  unfold prefixBits encodeVector
  rw [show (List.ofFn v).take n = List.ofFn v from
    by simpa only [List.length_ofFn] using List.take_length (l := List.ofFn v)]

theorem prefix_step {n : ℕ} (v : Fin n → ℚ) (i : Fin n) :
    prefixBits v (i.val + 1) = prefixBits v i.val + bitSize (encodeRational (v i)) := by
  have hi : i.val < (List.ofFn v).length := by simp
  unfold prefixBits
  rw [← List.take_concat_get hi]
  simp [List.concat_eq_append, List.flatMap_append, bitSize_append, bitSize_nil]

theorem prefix_le {n : ℕ} (v : Fin n → ℚ) (k : ℕ) :
    prefixBits v k ≤ bitSize (encodeVector v) := by
  have he : prefixBits v k + bitSize ((List.ofFn v).drop k |>.flatMap encodeRational) =
      bitSize (encodeVector v) := by
    rw [prefixBits, ← bitSize_append, ← List.flatMap_append, List.take_append_drop]
    rfl
  omega

def Invariant (a : String) {n : ℕ} (v : Fin n → ℚ) (t : ℕ) (σ : Env) : Prop :=
  Represents a (List.ofFn v) σ ∧ σ.vars "size.total" = t + prefixBits v (σ.vars "size.i") ∧
    σ.vars "size.i" ≤ n ∧ σ.vars "vec.n" = n

def countStep (a : String) : Com := .seq (.assign "vec.i" (.var "size.i"))
  (.seq (loadLeft a) (.seq countFraction (.assign "size.i" (.add (.var "size.i") (.lit 1)))))

theorem countStep_warrs (a : String) : (countStep a).warrs = [] := by rfl

theorem countStep_spec (B H n t : ℕ) (a : String) (v : Fin n → ℚ)
    (h2 : 2 < B) (hH : 1 ≤ H) (hHB : H < B) (hnB : n < B)
    (hv : ∀ i, Height (v i) H) (ht : t + bitSize (encodeVector v) < B) :
    Spec B (fun σ => Invariant a v t σ ∧ σ.vars "size.i" < n) (countStep a)
      (fun σ τ => Invariant a v t τ ∧ τ.vars "size.i" = σ.vars "size.i" + 1)
      (36 * H.size + 57) := by
  rintro σ ⟨⟨hσa, hσt, hσiN, hσn⟩, hσi⟩
  let i : Fin n := ⟨σ.vars "size.i", hσi⟩
  have hiB : i.val < B := i.isLt.trans hnB
  have hr₁ : Run B (.assign "vec.i" (.var "size.i")) σ (σ.setVar "vec.i" i.val) 2 :=
    Run.assign (by simpa only [i] using evalB_var (B := B) (σ := σ) (x := "size.i") hiB)
  obtain ⟨τ, hr₂, hτq⟩ := loadLeft_spec B a (List.ofFn v) i.val (by simp) (by omega) hiB
    (by simpa using (hv i).1.trans_lt hHB) (by simpa using (hv i).2.trans_lt hHB)
    (σ.setVar "vec.i" i.val) ⟨hσa, by simp⟩
  have hτq' : LeftOutput (v i) τ := by simpa only [List.getElem_ofFn, Fin.eta] using hτq
  have hτt : τ.vars "size.total" = t + prefixBits v i.val :=
    (hr₂.frame_var _ (by simp [loadLeft, Com.wvars])).trans hσt
  have htcoord : t + prefixBits v i.val + bitSize (encodeRational (v i)) < B := by
    have hh := prefix_le v (i.val + 1)
    rw [prefix_step] at hh
    omega
  obtain ⟨υ, hr₃, hυq, hυt⟩ := countFraction_spec B H (t + prefixBits v i.val) (v i)
    h2 hH hHB (hv i) htcoord τ ⟨hτq', hτt⟩
  have hpre := hr₁.seq (hr₂.seq hr₃)
  have hυi : υ.vars "size.i" = i.val := hpre.frame_var _ (by simp [loadLeft,
    countFraction, countWord, bitLength, bitLengthLoop, bitLengthStep, Com.wvars])
  have hυn : υ.vars "vec.n" = n := (hpre.frame_var _ (by simp [loadLeft,
    countFraction, countWord, bitLength, bitLengthLoop, bitLengthStep, Com.wvars])).trans hσn
  have he : (Expr.add (.var "size.i") (.lit 1)).evalB B υ = some (i.val + 1) := by
    simpa only [hυi, Bop.apply_add] using evalB_bin
      (evalB_var (B := B) (σ := υ) (x := "size.i") (by rw [hυi]; exact hiB))
      (evalB_lit (by omega : 1 < B))
      (show Bop.add.apply (υ.vars "size.i") 1 < B by rw [hυi]; simp only [Bop.apply_add]; omega)
  have hr₄ := Run.assign (x := "size.i") he
  have hrun := hr₁.seq (hr₂.seq (hr₃.seq hr₄))
  have harrs : (υ.setVar "size.i" (i.val + 1)).arrs = σ.arrs := by
    funext b
    exact hrun.frame_arr b (by change b ∉ (countStep a).warrs; rw [countStep_warrs]; simp)
  refine ⟨_, hrun.mono (by simp only [Expr.size]; omega), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Represents, harrs] using hσa
  · simp only [vars_setVar, ite_true, show "size.total" ≠ "size.i" by decide, ite_false]
    rw [prefix_step]
    omega
  · change i.val + 1 ≤ n; exact i.isLt
  · simpa [Env.setVar] using hυn
  · simp [i]

def countArray (a : String) : Com := .seq (.assign "size.i" (.lit 0))
  (.while (.lt (.var "size.i") (.var "vec.n")) (countStep a))

theorem countArray_spec (B H n t : ℕ) (a : String) (v : Fin n → ℚ)
    (h2 : 2 < B) (hH : 1 ≤ H) (hHB : H < B) (hnB : n < B)
    (hv : ∀ i, Height (v i) H) (ht : t + bitSize (encodeVector v) < B) :
    Spec B (fun σ => Represents a (List.ofFn v) σ ∧ σ.vars "size.total" = t ∧ σ.vars "vec.n" = n)
      (countArray a)
      (fun _ τ => Represents a (List.ofFn v) τ ∧
        τ.vars "size.total" = t + bitSize (encodeVector v) ∧ τ.vars "vec.n" = n)
      ((36 * H.size + 61) * n + 6) := by
  have hlo := Spec.forRangeZero "size.i" "vec.n" (Invariant a v t) n (36 * H.size + 57) hnB
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2)
    (countStep_spec B H n t a v h2 hH hHB hnB hv ht)
  refine ((hlo.pre ?_).post ?_).mono (by simp only [Nat.add_assoc, Nat.reduceAdd]; omega)
  · rintro σ ⟨hσa, hσt, hσn⟩
    clear hlo
    simp_all [Invariant, prefix_zero, Represents, Env.setVar]
  · rintro σ τ _ ⟨hτ, hcounter⟩
    exact ⟨hτ.1, by simpa only [hcounter, prefix_done] using hτ.2.1, hτ.2.2.2⟩

end Lax109476Proofs.RamEncodedSize

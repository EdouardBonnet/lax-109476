import Lax109476Proofs.RamMatrixVector

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamEllipsoidForm

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamDotProduct RamMatrixRows RamMatrixVector
open RationalArithmeticBounds

def FormOutput (q : ℚ) (σ : Env) : Prop :=
  fractionValue (σ.vars "ell.form.s") (σ.vars "ell.form.n") (σ.vars "ell.form.d") = q ∧
    σ.vars "ell.form.n" = q.num.natAbs ∧ σ.vars "ell.form.d" = q.den ∧ σ.vars "ell.form.s" ≤ 1

def saveForm : Com :=
  .seq (.assign "ell.form.s" (.var "dot.s"))
    (.seq (.assign "ell.form.n" (.var "dot.n")) (.assign "ell.form.d" (.var "dot.d")))

theorem saveForm_spec (B : ℕ) (q : ℚ) (h1 : 1 < B)
    (hn : q.num.natAbs < B) (hd : q.den < B) :
    Spec B (DotOutput q) saveForm (fun σ τ => FormOutput q τ ∧ τ.arrs = σ.arrs) 6 := by
  rintro σ ⟨hσq, hσn, hσd, hσs⟩
  have hsB := hσs.trans_lt h1
  run_vcg
  all_goals simp_all [FormOutput]

def formHeight (n H : ℕ) : ℕ := cap n (cap n H)

theorem formHeight_ge (n H : ℕ) (hH : 1 ≤ H) : cap n H ≤ formHeight n H := by
  have hcap := (cap_ge n H hH).2
  exact (cap_ge n (cap n H) (hH.trans hcap)).2

theorem formHeight_size (n H : ℕ) :
    (formHeight n H).size ≤
      (n + 1) * (2 * ((n + 1) * (2 * H.size + 3) + 1) + 3) + 1 := by
  have hc := cap_size n H
  have hf := cap_size n (cap n H)
  have hm := Nat.mul_le_mul_left (n + 1) (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hc) 3)
  unfold formHeight
  omega

def ellipsoidForm : Com :=
  .seq ellipsoidMulVecInitialized (.seq (RamDotProduct.dotProduct "ell.normal" "ell.u") saveForm)

theorem ellipsoidForm_spec (B n H : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (a : Fin n → ℚ)
    (hH : 1 ≤ H) (hA : ∀ k j, Height (A k j) H) (ha : ∀ j, Height (a j) H)
    (hdims : n + n + n * n + 1 < B) (hB : 2 * (formHeight n H) ^ 2 + 3 < B) :
    Spec B (fun σ => MatrixRows "ell.shape" A σ ∧ Represents "ell.normal" (List.ofFn a) σ ∧
        (σ.arrs "ell.u.s").length = n ∧ (σ.arrs "ell.u.n").length = n ∧
        (σ.arrs "ell.u.d").length = n ∧ σ.vars "vec.n" = n)
      ellipsoidForm
      (fun _ τ => FormOutput (a ⬝ᵥ (A *ᵥ a)) τ ∧
        Represents "ell.u" (List.ofFn (A *ᵥ a)) τ ∧ MatrixRows "ell.shape" A τ ∧
        Represents "ell.normal" (List.ofFn a) τ ∧ τ.vars "vec.n" = n)
      (33 * n + 18 + (((4 + ((144 * (cap n H).size + 216 + 4) * n + 12) + 21 + 4) + 4) * n + 8) +
        (((144 * (formHeight n H).size + 210 + 4) * n + 12) + 6)) := by
  have hcap := (cap_ge n H hH).2
  have hform := formHeight_ge n H hH
  have hcapB : cap n H < B := by nlinarith
  have hfB : formHeight n H < B := by nlinarith
  have hB₁ : 2 * (cap n H) ^ 2 + 3 < B := by nlinarith
  have hnB : n < B := by omega
  have h1 : 1 < B := by nlinarith
  rintro σ hσ
  obtain ⟨τ, hr₁, hτu, hτA, hτa, hτn⟩ := ellipsoidMulVecInitialized_spec B n H A a hH hA ha
    hdims hB₁ σ hσ
  have hn : (List.ofFn a).length = n := by simp
  have hu : (List.ofFn (A *ᵥ a)).length = n := by simp
  have han : ∀ q ∈ List.ofFn a, Height q (cap n H) := by
    intro q hq; simp only [List.mem_ofFn] at hq; obtain ⟨j, rfl⟩ := hq
    exact height_mono _ (ha j) hcap
  have hun : ∀ q ∈ List.ofFn (A *ᵥ a), Height q (cap n H) := by
    intro q hq; simp only [List.mem_ofFn] at hq; obtain ⟨j, rfl⟩ := hq
    exact mulVec_height n H A a hH hA ha j
  obtain ⟨υ, hr₂, hυq, _, _, _, _⟩ := dotProduct_spec B n (cap n H) "ell.normal" "ell.u"
    (List.ofFn a) (List.ofFn (A *ᵥ a)) hn hu (hH.trans hcap) han hun hnB hB
    τ ⟨hτa, hτu, hτn⟩
  have hformq : Height (a ⬝ᵥ (A *ᵥ a)) (formHeight n H) := by
    change Height (∑ j, a j * (A *ᵥ a) j) (formHeight n H)
    rw [← prefix_ofFn]
    exact prefix_height _ _ n (cap n H) n (hH.trans hcap) hn hu le_rfl han hun
  have hυform : DotOutput (a ⬝ᵥ (A *ᵥ a)) υ := by
    simpa only [prefix_ofFn, _root_.dotProduct] using hυq
  obtain ⟨ρ, hr₃, hρ, _⟩ := saveForm_spec B (a ⬝ᵥ (A *ᵥ a)) h1
    (hformq.1.trans_lt hfB) (hformq.2.trans_lt hfB) υ hυform
  have hυarr : υ.arrs = τ.arrs := by
    funext b
    exact hr₂.frame_arr b (by
      simp [RamDotProduct.dotProduct, dotStep, multiplyAt, loadLeft, loadRight, addToAccumulator,
        multiplyFraction, addFraction, RamArithmetic.normalizeFraction, RamArithmetic.gcdLoop,
        RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.warrs])
  have hρarr : ρ.arrs = υ.arrs := by
    funext b
    exact hr₃.frame_arr b (by simp [saveForm, Com.warrs])
  have hυn : υ.vars "vec.n" = n :=
    (hr₂.frame_var "vec.n" (by
      simp [RamDotProduct.dotProduct, dotStep, multiplyAt, loadLeft, loadRight, addToAccumulator,
        multiplyFraction, addFraction, RamArithmetic.normalizeFraction, RamArithmetic.gcdLoop,
        RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.wvars])).trans hτn
  have hρn : ρ.vars "vec.n" = n := (hr₃.frame_var "vec.n" (by simp [saveForm, Com.wvars])).trans hυn
  refine ⟨ρ, hr₁.seq (hr₂.seq hr₃), hρ, ?_, ?_, ?_, hρn⟩
  · simpa only [Represents, hρarr, hυarr] using hτu
  · simpa only [MatrixRows, Slice, hρarr, hυarr] using hτA
  · simpa only [Represents, hρarr, hυarr] using hτa

theorem ellipsoidForm_cost_polynomial (n H : ℕ) :
    33 * n + 18 + (((4 + ((144 * (cap n H).size + 216 + 4) * n + 12) + 21 + 4) + 4) * n + 8) +
      (((144 * (formHeight n H).size + 210 + 4) * n + 12) + 6) ≤
    (144 * ((n + 1) * (2 * H.size + 3) + 1) + 220) * n ^ 2 +
      (144 * ((n + 1) * (2 * ((n + 1) * (2 * H.size + 3) + 1) + 3) + 1) + 292) * n + 44 := by
  have hd := Nat.add_le_add_right
    (Nat.mul_le_mul_right n (Nat.add_le_add_right (Nat.mul_le_mul_left 144 (formHeight_size n H)) 214)) 18
  convert Nat.add_le_add (ellipsoidMulVec_cost_polynomial n H) hd using 1
  ring

end Lax109476Proofs.RamEllipsoidForm

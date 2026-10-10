/-
Adapted from Jyotirmoy Bhattacharya, farkas_lean, revision
30c319dd52ca89cfa82a68352b1f39f4f3026fc2.
https://github.com/jmoy/farkas_lean

Copyright 2026 Jyotirmoy Bhattacharya

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the “Software”), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
-/
import Lax109476.FourierMotzkin
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Lax109476Proofs.Elimination.FourierMotzkin

open Matrix
/-
A theorem of the alternative.

Either Ax <= b has a solution, or
y >=0, y'A = 0, y'b < 0 has a solution.

We prove it using our Fourier-Motzkin elimination theorem.
-/

namespace Lax109476Proofs.Elimination

local notation "F" => ℝ
variable {m : Type} [Fintype m]

/-!
## Definitions using Matrix Operations
A is an m × n matrix.
`A.mulVec x` is matrix-vector multiplication (Ax).
`vecMul y A` is vector-matrix multiplication (y^T A).
-/

def Farkas1Primal {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) : Prop :=
  ∃ x : Fin n → F, A.mulVec x ≤  b

def Farkas1Dual {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) : Prop :=
  ∃ y : m → F, (∀ j, 0 ≤ y j) ∧ (y ᵥ* A = 0) ∧ (y ⬝ᵥ b < 0)

private theorem liftDual_of_fourierMotzkin {κ : Type*} [Fintype κ] {n : ℕ}
    (A : Matrix m (Fin (n + 1)) F) (b : m → F) (M : Matrix κ m F)
    (hM_last : ∀ i, (M * A) i (Fin.last n) = 0)
    (hMt_nonneg : ∀ i j, 0 ≤ (M.transpose) i j)
  (y' : κ → F)
  (hy'_nonneg : ∀ j, 0 ≤ y' j)
  (hy'_Ared : y' ᵥ* (M * (A.submatrix id Fin.castSucc)) = 0)
  (hy'_bred : y' ⬝ᵥ M.mulVec b < 0) :
  let y : m → F := M.transpose.mulVec y'
  (∀ j, 0 ≤ y j) ∧ (y ᵥ* A = 0) ∧ (y ⬝ᵥ b < 0) := by
  have hy_nonneg : ∀ j, 0 ≤ (M.transpose.mulVec y') j := by
    intro j
    simpa [Matrix.mulVec] using dotProduct_nonneg_of_nonneg (hMt_nonneg j) hy'_nonneg
  have hy'_Acast : y' ᵥ* ((M * A).submatrix id Fin.castSucc) = 0 := by
    have hAred_eq : M * (A.submatrix id Fin.castSucc) = (M * A).submatrix id Fin.castSucc := by
      simpa using
        (submatrix_mul M A id id Fin.castSucc Function.bijective_id).symm
    simpa [hAred_eq] using hy'_Ared
  have hy'_MA : y' ᵥ* (M * A) = 0 := by
    ext j
    refine Fin.lastCases ?_ ?_ j
    · simp [Matrix.vecMul, dotProduct, hM_last]
    · intro k
      simpa [Matrix.vecMul, dotProduct] using congr_fun hy'_Acast k
  have hyA : (M.transpose.mulVec y') ᵥ* A = 0 := by
    calc
      (M.transpose.mulVec y') ᵥ* A = (y' ᵥ* M) ᵥ* A := by
        rw [Matrix.mulVec_transpose]
      _ = y' ᵥ* (M * A) := by
        rw [Matrix.vecMul_vecMul]
      _ = 0 := hy'_MA
  have hyb : (M.transpose.mulVec y') ⬝ᵥ b < 0 := by
    calc
      (M.transpose.mulVec y') ⬝ᵥ b = (y' ᵥ* M) ⬝ᵥ b := by
        rw [Matrix.mulVec_transpose]
      _ = y' ⬝ᵥ M.mulVec b := by
        symm
        simpa using Matrix.dotProduct_mulVec y' M b
      _ < 0 := hy'_bred
  simpa using
    (show (∀ j, 0 ≤ (M.transpose.mulVec y') j) ∧
        ((M.transpose.mulVec y') ᵥ* A = 0) ∧ ((M.transpose.mulVec y') ⬝ᵥ b < 0) from
      ⟨hy_nonneg, hyA, hyb⟩)

/-!
## Farkas' Lemma
-/

theorem Farkas1Exhaust {n : ℕ} (A : Matrix m (Fin n) F) (b : m → F) :
  Farkas1Primal A b ∨ Farkas1Dual A b := by
  induction n generalizing m b with
  | zero =>
      by_cases hb : 0 ≤ b
      · left
        refine ⟨Fin.elim0, ?_⟩
        simpa [Matrix.mulVec] using hb
      · right
        have hbi : ∃ i : m, b i < 0 := by
          by_contra hbi
          apply hb
          intro i
          by_contra hnonneg
          exact hbi ⟨i, lt_of_not_ge hnonneg⟩
        rcases hbi with ⟨i, hbi⟩
        classical
        let y : m → F := fun j => if j = i then 1 else 0
        refine ⟨y, ?_, ?_, ?_⟩
        · intro j
          by_cases hji : j = i <;> simp [y, hji]
        · ext j
          exact j.elim0
        · have hyb : y ⬝ᵥ b = b i := by
            simp [y, dotProduct]
          rw [hyb]
          exact hbi
  | succ n ih =>
      by_cases hP : Farkas1Primal A b
      · exact Or.inl hP
      · right
        rcases Lax109476.FourierMotzkin.exists_elimination m n A b with ⟨κ, _, M, hM_nonneg, hM_last, hFM⟩
        let Ared : Matrix κ (Fin n) F := M * (A.submatrix id Fin.castSucc)
        let bred : κ → F := M.mulVec b
        have hFM' : Farkas1Primal A b ↔ Farkas1Primal (m := κ) Ared bred := by
          simpa [Farkas1Primal, Ared, bred] using hFM
        have hred_noPrimal : ¬ Farkas1Primal (m := κ) Ared bred := by
          intro h
          exact hP (hFM'.2 h)
        have hred_exhaust : Farkas1Primal (m := κ) Ared bred ∨ Farkas1Dual (m := κ) Ared bred :=
          ih (m := κ) (A := Ared) (b := bred)
        have hred_dual : Farkas1Dual (m := κ) Ared bred := by
          cases hred_exhaust with
          | inl h => exact False.elim (hred_noPrimal h)
          | inr h => exact h
        rcases hred_dual with ⟨y', hy'_nonneg, hy'_Ared, hy'_bred⟩
        have hMt_nonneg : ∀ i j, 0 ≤ (M.transpose) i j := by
          intro i j
          simpa [Matrix.transpose_apply] using hM_nonneg j i
        have hdual_lift : Farkas1Dual A b := by
          refine ⟨M.transpose.mulVec y', ?_⟩
          simpa [Ared, bred] using
            (liftDual_of_fourierMotzkin A b M hM_last hMt_nonneg y' hy'_nonneg hy'_Ared hy'_bred)
        exact hdual_lift
end Lax109476Proofs.Elimination

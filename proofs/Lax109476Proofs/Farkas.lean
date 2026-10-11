import Lax109476Proofs.Elimination.Farkas1
import Lax109476.FarkasLemma
import Mathlib.Tactic

open scoped BigOperators

namespace Lax109476Proofs.Farkas

open Lax109476.LinearProgram Lax109476.FarkasCertificate

/--
---
conclusion: Lax109476.FourierMotzkin.exists_elimination
---
Partition the rows according to the sign of the eliminated variable's
coefficient. Combine every positive row with every negative row using
nonnegative multipliers, and retain the zero rows. A finite family of
compatible lower and upper bounds admits a witness for the removed variable,
for each fixed solution of the reduced system. Reconstruction keeps all
retained coordinates unchanged, giving the pointwise projection equivalence.

# Attribution

Adapted from Jyotirmoy Bhattacharya's MIT-licensed `farkas_lean`, revision
30c319dd52ca89cfa82a68352b1f39f4f3026fc2. The adapted files retain the
copyright and license notices.
-/
theorem fourier_motzkin :
    ∀ (m : Type) [Fintype m] (n : ℕ)
      (A : Matrix m (Fin (n + 1)) ℝ) (b : m → ℝ),
      ∃ κ : Type, ∃ _ : Fintype κ, ∃ M : Matrix κ m ℝ,
        (∀ i j, 0 ≤ M i j) ∧
        (∀ i, (M * A) i (Fin.last n) = 0) ∧
        (∀ x' : Fin n → ℝ,
          (M * (A.submatrix id Fin.castSucc)).mulVec x' ≤ M.mulVec b ↔
            ∃ t : ℝ, A.mulVec (Fin.lastCases t x') ≤ b) := by
  intro m _ n A b
  exact Lax109476Proofs.Elimination.Fourier_Motzkin A b

private def augmentedMatrix {m n : ℕ} (P : Program ℝ m n) :
    Matrix (Fin m ⊕ Fin n) (Fin n) ℝ :=
  Sum.elim P.A (fun k j => if k = j then -1 else 0)

private def augmentedBound {m n : ℕ} (P : Program ℝ m n) :
    (Fin m ⊕ Fin n) → ℝ := Sum.elim P.b (fun _ => 0)

/--
---
conclusion: Lax109476.FarkasLemma.exists_infeasibility_certificate
---
Add the inequalities $-x_j\le0$ to the rows of $Ax\le b$ and apply the
unrestricted-variable alternative proved by induction with Fourier–Motzkin
elimination. Split its nonnegative multipliers into original-row and
nonnegativity-row components. The zero column equations give $A^T y\ge0$;
the negative weighted bound is exactly $b^T y<0$.

# Attribution

The induction and multiplier lifting adapt Jyotirmoy Bhattacharya's
MIT-licensed `farkas_lean`. The conversion to the submission's nonnegative
primal convention is supplied here.
-/
theorem farkas_certificate_exists :
    ∀ (m n : ℕ) (P : Program ℝ m n), ¬ IsFeasible P →
      ∃ y : Fin m → ℝ, IsInfeasibilityCertificate P y := by
  intro m n P hP
  classical
  have hno : ¬ Lax109476Proofs.Elimination.Farkas1Primal
      (augmentedMatrix P) (augmentedBound P) := by
    rintro ⟨x, hx⟩
    apply hP
    refine ⟨x, ?_, ?_⟩
    · intro j
      have hj := hx (.inr j)
      simp [augmentedMatrix, augmentedBound, Matrix.mulVec, dotProduct] at hj
      linarith
    · intro i
      exact hx (.inl i)
  rcases Lax109476Proofs.Elimination.Farkas1Exhaust
      (augmentedMatrix P) (augmentedBound P) with hp | ⟨y, hy, hA, hb⟩
  · exact False.elim (hno hp)
  · refine ⟨fun i => y (.inl i), fun i => hy (.inl i), ?_, ?_⟩
    · intro j
      have heq := congr_fun hA j
      simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type,
        augmentedMatrix, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply] at heq
      have hsum : (∑ k, y (Sum.inr k) * (if k = j then (-1 : ℝ) else 0)) =
          -y (.inr j) := by simp
      rw [hsum] at heq
      have hid : columnValue P (fun i => y (.inl i)) j =
          ∑ i, y (.inl i) * P.A i j := by
        simp only [columnValue, mul_comm]
      rw [hid]
      linarith [hy (.inr j)]
    · simpa [dualValue, dotProduct, Fintype.sum_sum_type,
        augmentedBound, mul_comm] using hb

end Lax109476Proofs.Farkas

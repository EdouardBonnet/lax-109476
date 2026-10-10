import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/-!
---
title: Fourier–Motzkin elimination
type: theorem
---
One variable can be eliminated from a finite system of real linear
inequalities by nonnegative combinations of its rows. Pair each row with
positive coefficient of the eliminated variable with each row with negative
coefficient, and retain the rows with zero coefficient. The resulting finite
system is feasible exactly when the original system is feasible.

# Formalization notes

The variables in this elimination step are unrestricted. Nonnegative
variables are represented by additional inequalities when deriving Farkas'
lemma. The matrix $M$ gives the nonnegative row combinations. Its last
column in $MA$ is zero, and the remaining columns describe the reduced
system. This is an algebraic elimination theorem, with no polynomial-time
claim: repeated elimination may produce exponentially many inequalities.
-/

namespace Lax109476.FourierMotzkin

/-- Eliminate the last variable using nonnegative row combinations. -/
axiom exists_elimination :
  ∀ (m : Type) [Fintype m] (n : ℕ)
    (A : Matrix m (Fin (n + 1)) ℝ) (b : m → ℝ),
    ∃ κ : Type, ∃ _ : Fintype κ, ∃ M : Matrix κ m ℝ,
      (∀ i j, 0 ≤ M i j) ∧
      (∀ i, (M * A) i (Fin.last n) = 0) ∧
      ((∃ x : Fin (n + 1) → ℝ, A.mulVec x ≤ b) ↔
        ∃ x' : Fin n → ℝ,
          (M * (A.submatrix id Fin.castSucc)).mulVec x' ≤ M.mulVec b)

end Lax109476.FourierMotzkin

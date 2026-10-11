import Lax109476Proofs.CoordinateOptimization
import Lax109476Proofs.LexicographicMinima
import Lax109476Proofs.RamMatrixStorage
import Lax109476Proofs.RationalArithmeticBounds

namespace Lax109476Proofs.RecoveryQueryEntries

open Lax109476.LinearProgram CoordinateOptimization LexicographicMinima RationalArithmeticBounds

def entry {m n : ℕ} (P : Program ℚ m n) (k : ℕ)
    (i : Fin ((m + (n + n)) + 1)) (j : Fin n) : ℚ :=
  if hi : i.val < m then P.A ⟨i.val, hi⟩ j
  else if i.val < m + n then
    if i.val - m < k ∧ j.val = i.val - m then 1 else 0
  else if i.val < m + n + n then
    if i.val - m - n < k ∧ j.val = i.val - m - n then -1 else 0
  else if j.val = k then 1 else 0

def bound {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (k : ℕ) (t : ℚ)
    (i : Fin ((m + (n + n)) + 1)) : ℚ :=
  if hi : i.val < m then P.b ⟨i.val, hi⟩
  else if hi : i.val < m + n then
    if i.val - m < k then x ⟨i.val - m, by omega⟩ else 0
  else if hi : i.val < m + n + n then
    if i.val - m - n < k then -x ⟨i.val - m - n, by omega⟩ else 0
  else t

theorem entry_eq {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (k : ℕ) (hk : k < n)
    (t : ℚ) (i : Fin ((m + (n + n)) + 1)) (j : Fin n) :
    entry P k i j = (coordinateCut (fixedPrefix P x k) ⟨k, hk⟩ t).A i j := by
  refine Fin.addCases ?_ ?_ i
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      simp [-Fin.natAdd_eq_addNat, entry, coordinateCut, fixedPrefix, i.isLt]
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro i
        have hi : m + i.val < m + n := by omega
        by_cases hik : i.val < k <;> by_cases hji : j.val = i.val <;>
          simp [-Fin.natAdd_eq_addNat, entry, coordinateCut, fixedPrefix, hi, Fin.ext_iff, hik, hji]
      · intro i
        have hi : ¬ m + (n + i.val) < m + n := by omega
        have hi' : m + (n + i.val) < m + n + n := by omega
        by_cases hik : i.val < k <;> by_cases hji : j.val = i.val <;>
          simp [-Fin.natAdd_eq_addNat, entry, coordinateCut, fixedPrefix, hi, hi', Fin.ext_iff, Nat.add_assoc, hik, hji]
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [-Fin.natAdd_eq_addNat, entry, coordinateCut, fixedPrefix, Fin.ext_iff, Nat.add_assoc]

theorem bound_eq {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (k : ℕ) (hk : k < n)
    (t : ℚ) (i : Fin ((m + (n + n)) + 1)) :
    bound P x k t i = (coordinateCut (fixedPrefix P x k) ⟨k, hk⟩ t).b i := by
  refine Fin.addCases ?_ ?_ i
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      simp [-Fin.natAdd_eq_addNat, bound, coordinateCut, fixedPrefix, i.isLt]
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro i
        have hi : m + i.val < m + n := by omega
        simp [-Fin.natAdd_eq_addNat, bound, coordinateCut, fixedPrefix, hi]
      · intro i
        have hi : ¬ m + (n + i.val) < m + n := by omega
        have hi' : m + (n + i.val) < m + n + n := by omega
        simp [-Fin.natAdd_eq_addNat, bound, coordinateCut, fixedPrefix, hi, hi', Nat.add_assoc]
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [-Fin.natAdd_eq_addNat, bound, coordinateCut, fixedPrefix, Nat.add_assoc]

theorem entry_height {m n : ℕ} (P : Program ℚ m n) (k M : ℕ) (hM : 1 ≤ M)
    (hA : ∀ i j, Height (P.A i j) M) (i : Fin ((m + (n + n)) + 1)) (j : Fin n) :
    Height (entry P k i j) M := by
  unfold entry
  split_ifs
  · exact hA _ _
  all_goals simp_all [Height]

theorem bound_height {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (k M : ℕ) (t : ℚ)
    (hM : 1 ≤ M) (hb : ∀ i, Height (P.b i) M) (hx : ∀ j, Height (x j) M) (ht : Height t M)
    (i : Fin ((m + (n + n)) + 1)) : Height (bound P x k t i) M := by
  unfold bound
  split_ifs
  · exact hb _
  · exact hx _
  · exact height_mono _ height_zero hM
  · exact height_neg _ _ (hx _)
  · exact height_mono _ height_zero hM
  · exact ht

end Lax109476Proofs.RecoveryQueryEntries

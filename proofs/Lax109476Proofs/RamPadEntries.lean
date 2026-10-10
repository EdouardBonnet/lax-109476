import Lax109476Proofs.FeasibilityPadding
import Lax109476Proofs.RamMatrixStorage
import Lax109476Proofs.RationalArithmeticBounds

namespace Lax109476Proofs.RamPadEntries

open Lax109476.LinearProgram FeasibilityPadding RationalArithmeticBounds

def entry {m n : ℕ} (P : Program ℚ m n) (i : Fin (m + 2)) (j : Fin (n + 2)) : ℚ :=
  if hi : i.val < m then
    if hj : j.val < n then P.A ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
  else if n ≤ j.val then if i.val - m = j.val - n then 1 else 0 else 0

theorem entry_eq {m n : ℕ} (P : Program ℚ m n) (i : Fin (m + 2)) (j : Fin (n + 2)) :
    entry P i j = (pad P).A i j := by
  refine Fin.addCases ?_ ?_ i
  · intro i
    refine Fin.addCases ?_ ?_ j
    · intro j
      simp [entry, pad, i.isLt, j.isLt]
    · intro j
      have hj : ¬ (Fin.natAdd n j).val < n := by simp
      simp [entry, pad, i.isLt, hj]
  · intro i
    have hi : ¬ (Fin.natAdd m i).val < m := by simp
    refine Fin.addCases ?_ ?_ j
    · intro j
      have hj : ¬ n ≤ (Fin.castAdd 2 j).val := by simpa using Nat.not_le.mpr j.isLt
      simp [entry, pad, hi, hj]
    · intro j
      simp [entry, pad, hi, Fin.ext_iff]

def values {m n : ℕ} (P : Program ℚ m n) : Fin ((m + 2) * (n + 2)) → ℚ :=
  fun k => entry P k.divNat k.modNat

theorem values_eq {m n : ℕ} (P : Program ℚ m n) :
    List.ofFn (values P) = RamMatrixStorage.flatten (pad P).A := by
  unfold RamMatrixStorage.flatten values
  congr 1
  funext k
  exact entry_eq P k.divNat k.modNat

theorem entry_height {m n : ℕ} (P : Program ℚ m n) (M : ℕ) (hM : 1 ≤ M)
    (hA : ∀ i j, Height (P.A i j) M) (i : Fin (m + 2)) (j : Fin (n + 2)) :
    Height (entry P i j) M := by
  unfold entry
  split_ifs with hi hj hnonneg heq
  · exact hA _ _
  all_goals simp_all [Height]

end Lax109476Proofs.RamPadEntries

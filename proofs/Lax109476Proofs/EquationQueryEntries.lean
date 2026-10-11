import Lax109476Proofs.RamStandardPointRecovery
import Lax109476Proofs.IntegerPointRecovery

namespace Lax109476Proofs.EquationQueryEntries

open Lax109476.LinearProgram
open IntegerPointRecovery RamStandardPointRecovery RationalArithmeticBounds

def slackEntry {m n : ℕ} (P : Program ℤ m n) (i : Fin m) (j : Fin (n + m)) : ℚ :=
  if hj : j.val < n then (P.A i ⟨j.val, hj⟩ : ℚ)
  else if j.val - n = i.val then 1 else 0

def entry {m n : ℕ} (P : Program ℤ m n) (i : Fin (m + m)) (j : Fin (n + m)) : ℚ :=
  if hi : i.val < m then slackEntry P ⟨i.val, hi⟩ j
  else -slackEntry P ⟨i.val - m, by omega⟩ j

def bound {m n : ℕ} (P : Program ℤ m n) (i : Fin (m + m)) : ℚ :=
  if hi : i.val < m then (P.b ⟨i.val, hi⟩ : ℚ)
  else -(P.b ⟨i.val - m, by omega⟩ : ℚ)

theorem slackEntry_eq {m n : ℕ} (P : Program ℤ m n) (i : Fin m) (j : Fin (n + m)) :
    slackEntry P i j = (slackMatrix P i j : ℚ) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp [slackEntry, slackMatrix, Fin.addCases_left, j.isLt]
  · have hj : ¬n + j.val < n := by omega
    have he : j.val = i.val ↔ j = i := Fin.ext_iff.symm
    simp [-Fin.natAdd_eq_addNat, slackEntry, slackMatrix, hj, he]

theorem entry_eq {m n : ℕ} (P : Program ℤ m n) (i : Fin (m + m)) (j : Fin (n + m)) :
    entry P i j = (program (slackMatrix P) P.b).A i j := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · have he : entry P (Fin.castAdd m i) j = (slackMatrix P i j : ℚ) := by
      simpa [entry, i.isLt] using slackEntry_eq P i j
    rw [he]
    change _ = Fin.addCases (motive := fun _ : Fin (m + m) => Fin (n + m) → ℚ)
      (fun i j => (slackMatrix P i j : ℚ)) (fun i j => -(slackMatrix P i j : ℚ)) (Fin.castAdd m i) j
    rw [Fin.addCases_left (motive := fun _ : Fin (m + m) => Fin (n + m) → ℚ)]
  · have hi : ¬m + i.val < m := by omega
    have he : entry P (Fin.natAdd m i) j = -(slackMatrix P i j : ℚ) := by
      simpa [-Fin.natAdd_eq_addNat, entry, hi] using congrArg Neg.neg (slackEntry_eq P i j)
    rw [he]
    change _ = Fin.addCases (motive := fun _ : Fin (m + m) => Fin (n + m) → ℚ)
      (fun i j => (slackMatrix P i j : ℚ)) (fun i j => -(slackMatrix P i j : ℚ)) (Fin.natAdd m i) j
    rw [Fin.addCases_right (motive := fun _ : Fin (m + m) => Fin (n + m) → ℚ)]

theorem bound_eq {m n : ℕ} (P : Program ℤ m n) (i : Fin (m + m)) :
    bound P i = (program (slackMatrix P) P.b).b i := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [bound, program, LexicographicMinima.equationProgram, i.isLt]
  · have hi : ¬m + i.val < m := by omega
    simp [-Fin.natAdd_eq_addNat, bound, program, LexicographicMinima.equationProgram, hi]

theorem entry_height {m n : ℕ} (P : Program ℤ m n) (M : ℕ) (hM : 1 ≤ M)
    (hA : ∀ i j, (P.A i j).natAbs ≤ M) (i : Fin (m + m)) (j : Fin (n + m)) : Height (entry P i j) M := by
  have hs : ∀ r : Fin m, Height (slackEntry P r j) M := by
    intro r
    unfold slackEntry
    split_ifs with hj he
    · exact ⟨by simpa using hA r ⟨j.val, hj⟩, by simpa using hM⟩
    · exact height_nat 1 M hM hM
    · exact height_mono 0 height_zero (by omega)
  unfold entry
  split_ifs
  · exact hs _
  · exact height_neg _ _ (hs _)

theorem bound_height {m n : ℕ} (P : Program ℤ m n) (M : ℕ) (hM : 1 ≤ M)
    (hb : ∀ i, (P.b i).natAbs ≤ M) (i : Fin (m + m)) : Height (bound P i) M := by
  have hs : ∀ r : Fin m, Height (P.b r : ℚ) M := fun r =>
    ⟨by simpa using hb r, by simpa using hM⟩
  unfold bound
  split_ifs
  · exact hs _
  · exact height_neg _ _ (hs _)

end Lax109476Proofs.EquationQueryEntries

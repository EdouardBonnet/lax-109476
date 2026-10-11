import Lax109476Proofs.CertificateFamilyEntries

namespace Lax109476Proofs.CertificateFamilyHeight

open Lax109476.LinearProgram
open CertificateFamilyPrograms CertificateFamilyEntries

theorem optimal_A_bound {m n : ℕ} (P : Program ℤ m n) (M : ℕ)
    (hA : ∀ i j, (P.A i j).natAbs ≤ M) (hb : ∀ i, (P.b i).natAbs ≤ M)
    (hc : ∀ j, (P.c j).natAbs ≤ M) : ∀ i j, ((optimal P).A i j).natAbs ≤ M := by
  intro i j
  rw [← pairEntry_eq]
  unfold pairEntry
  split_ifs <;> simp_all [Int.natAbs_neg]

theorem optimal_b_bound {m n : ℕ} (P : Program ℤ m n) (M : ℕ)
    (hb : ∀ i, (P.b i).natAbs ≤ M) (hc : ∀ j, (P.c j).natAbs ≤ M) :
    ∀ i, ((optimal P).b i).natAbs ≤ M := by
  intro i
  rw [← pairRhs_eq]
  unfold pairRhs
  split_ifs <;> simp_all [Int.natAbs_neg]

theorem infeasible_A_bound {m n : ℕ} (P : Program ℤ m n) (M : ℕ)
    (hA : ∀ i j, (P.A i j).natAbs ≤ M) (hb : ∀ i, (P.b i).natAbs ≤ M) :
    ∀ i j, ((infeasible P).A i j).natAbs ≤ M := by
  intro i j
  rw [← farkasEntry_eq]
  unfold farkasEntry
  split_ifs <;> simp_all [Int.natAbs_neg]

theorem infeasible_b_bound {m n : ℕ} (P : Program ℤ m n) (M : ℕ) (hM : 1 ≤ M) :
    ∀ i, ((infeasible P).b i).natAbs ≤ M := by
  intro i
  rw [← farkasRhs_eq]
  unfold farkasRhs
  split_ifs <;> simp_all

theorem unbounded_A_bound {m n : ℕ} (P : Program ℤ m n) (M : ℕ)
    (hA : ∀ i j, (P.A i j).natAbs ≤ M) (hc : ∀ j, (P.c j).natAbs ≤ M) :
    ∀ i j, ((unbounded P).A i j).natAbs ≤ M := by
  intro i j
  rw [← rayEntry_eq]
  unfold rayEntry
  split_ifs <;> simp_all [Int.natAbs_neg]

theorem unbounded_b_bound {m n : ℕ} (P : Program ℤ m n) (M : ℕ) (hM : 1 ≤ M)
    (hb : ∀ i, (P.b i).natAbs ≤ M) : ∀ i, ((unbounded P).b i).natAbs ≤ M := by
  intro i
  rw [← rayRhs_eq]
  unfold rayRhs
  split_ifs <;> simp_all

end Lax109476Proofs.CertificateFamilyHeight

import Lax109476Proofs.CertificateFamilyPrograms

namespace Lax109476Proofs.CertificateFamilyEntries

open Lax109476.LinearProgram
open CertificateFamilyPrograms IntegerCertificates CertificateSystems CertificateSearch IndexedPointRecovery

def pairEntry {m n : ℕ} (P : Program ℤ m n) (i : Fin (m + (n + 2))) (j : Fin (n + m)) : ℤ :=
  if hi : i.val < m then
    if hj : j.val < n then P.A ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
  else if hir : i.val < m + n then
    if hj : j.val < n then 0 else -P.A ⟨j.val - n, by omega⟩ ⟨i.val - m, by omega⟩
  else if i.val = m + n then
    if hj : j.val < n then P.c ⟨j.val, hj⟩ else -P.b ⟨j.val - n, by omega⟩
  else if hj : j.val < n then -P.c ⟨j.val, hj⟩ else P.b ⟨j.val - n, by omega⟩

def pairRhs {m n : ℕ} (P : Program ℤ m n) (i : Fin (m + (n + 2))) : ℤ :=
  if hi : i.val < m then P.b ⟨i.val, hi⟩
  else if hir : i.val < m + n then -P.c ⟨i.val - m, by omega⟩ else 0

def farkasEntry {m n : ℕ} (P : Program ℤ m n) (i : Fin (n + 1)) (j : Fin m) : ℤ :=
  if hi : i.val < n then -P.A j ⟨i.val, hi⟩ else P.b j

def farkasRhs {n : ℕ} (i : Fin (n + 1)) : ℤ := if i.val < n then 0 else -1

def rayEntry {m n : ℕ} (P : Program ℤ m n) (i : Fin (m + (m + 1))) (j : Fin (n + n)) : ℤ :=
  if hi : i.val < m then
    if hj : j.val < n then P.A ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
  else if hir : i.val < m + m then
    if hj : j.val < n then 0 else P.A ⟨i.val - m, by omega⟩ ⟨j.val - n, by omega⟩
  else if hj : j.val < n then 0 else -P.c ⟨j.val - n, by omega⟩

def rayRhs {m n : ℕ} (P : Program ℤ m n) (i : Fin (m + (m + 1))) : ℤ :=
  if hi : i.val < m then P.b ⟨i.val, hi⟩ else if i.val < m + m then 0 else -1

set_option maxHeartbeats 1000000 in
theorem pairEntry_eq {m n : ℕ} (P : Program ℤ m n) (i : Fin (m + (n + 2))) (j : Fin (n + m)) :
    pairEntry P i j = (optimal P).A i j := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    all_goals simp [-Fin.natAdd_eq_addNat, pairEntry, optimal, reindexProgram, pairRows, pairMatrix, i.isLt, j.isLt]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      all_goals simp [-Fin.natAdd_eq_addNat, pairEntry, optimal, reindexProgram, pairRows, pairMatrix, i.isLt, j.isLt]
      all_goals omega
    · fin_cases i
      all_goals refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      all_goals simp [-Fin.natAdd_eq_addNat, pairEntry, optimal, reindexProgram, pairRows, pairMatrix,
        finTwoEquiv, j.isLt, Nat.add_assoc]
      all_goals omega

theorem pairRhs_eq {m n : ℕ} (P : Program ℤ m n) (i : Fin (m + (n + 2))) :
    pairRhs P i = (optimal P).b i := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [pairRhs, optimal, reindexProgram, pairRows, pairBound, i.isLt]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp [-Fin.natAdd_eq_addNat, pairRhs, optimal, reindexProgram, pairRows, pairBound, i.isLt]
    · fin_cases i
      all_goals simp [-Fin.natAdd_eq_addNat, pairRhs, optimal, reindexProgram, pairRows, pairBound, finTwoEquiv]
      all_goals omega

theorem farkasEntry_eq {m n : ℕ} (P : Program ℤ m n) (i : Fin (n + 1)) (j : Fin m) :
    farkasEntry P i j = (infeasible P).A i j := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [farkasEntry, infeasible, reindexProgram, farkasRows, farkasMatrix, i.isLt]
  · have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [-Fin.natAdd_eq_addNat, farkasEntry, infeasible, reindexProgram, farkasRows, farkasMatrix, unitFin]

theorem farkasRhs_eq {m n : ℕ} (P : Program ℤ m n) (i : Fin (n + 1)) :
    farkasRhs i = (infeasible P).b i := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [farkasRhs, infeasible, reindexProgram, farkasRows, farkasBound, i.isLt]
  · have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [-Fin.natAdd_eq_addNat, farkasRhs, infeasible, reindexProgram, farkasRows, farkasBound, unitFin]

theorem rayEntry_eq {m n : ℕ} (P : Program ℤ m n) (i : Fin (m + (m + 1))) (j : Fin (n + n)) :
    rayEntry P i j = (unbounded P).A i j := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    all_goals simp [-Fin.natAdd_eq_addNat, rayEntry, unbounded, reindexProgram, rayRows, rayMatrix, i.isLt, j.isLt]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      all_goals simp [-Fin.natAdd_eq_addNat, rayEntry, unbounded, reindexProgram, rayRows, rayMatrix, i.isLt, j.isLt]
      all_goals omega
    · have hi : i = 0 := Subsingleton.elim _ _
      subst i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      all_goals simp [-Fin.natAdd_eq_addNat, rayEntry, unbounded, reindexProgram, rayRows, rayMatrix, unitFin, j.isLt, Nat.add_assoc]
      all_goals omega

theorem rayRhs_eq {m n : ℕ} (P : Program ℤ m n) (i : Fin (m + (m + 1))) :
    rayRhs P i = (unbounded P).b i := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [rayRhs, unbounded, reindexProgram, rayRows, rayBound, i.isLt]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp [-Fin.natAdd_eq_addNat, rayRhs, unbounded, reindexProgram, rayRows, rayBound, i.isLt]
    · have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp [-Fin.natAdd_eq_addNat, rayRhs, unbounded, reindexProgram, rayRows, rayBound, unitFin]

end Lax109476Proofs.CertificateFamilyEntries

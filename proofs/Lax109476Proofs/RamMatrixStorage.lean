import Lax109476Proofs.RamMatrixRows
import Mathlib.Logic.Equiv.Fin.Basic

namespace Lax109476Proofs.RamMatrixStorage

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamMatrixRows

def flatten {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : List ℚ :=
  List.ofFn (fun k : Fin (m * n) => A k.divNat k.modNat)

@[simp] theorem flatten_length {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    (flatten A).length = m * n := by simp [flatten]

theorem row_index_lt {m n : ℕ} (i : Fin m) (j : Fin n) : i.val * n + j.val < m * n := by
  have hmul := Nat.mul_le_mul_right n i.isLt
  calc
    _ < i.val * n + n := Nat.add_lt_add_left j.isLt _
    _ = (i.val + 1) * n := by ring
    _ ≤ _ := hmul

theorem flatten_entry {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) (j : Fin n) :
    (flatten A)[i.val * n + j.val]'(by simp; exact row_index_lt i j) = A i j := by
  have hk : (⟨i.val * n + j.val, row_index_lt i j⟩ : Fin (m * n)) = finProdFinEquiv (i, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  simp only [flatten, List.getElem_ofFn]
  change A ((finProdFinEquiv.symm (⟨i.val * n + j.val, row_index_lt i j⟩ : Fin (m * n))).1)
    ((finProdFinEquiv.symm (⟨i.val * n + j.val, row_index_lt i j⟩ : Fin (m * n))).2) = _
  rw [hk, Equiv.symm_apply_apply]

theorem rows_of_represents {m n : ℕ} (a : String) (A : Matrix (Fin m) (Fin n) ℚ) (σ : Env)
    (h : Represents a (flatten A) σ) : MatrixRows a A σ := by
  rcases h with ⟨hs, hn, hd⟩
  intro i
  have hlen : i.val * n + n ≤ m * n := by
    have hm := Nat.mul_le_mul_right n i.isLt
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hs] using hlen
  · simpa [hn] using hlen
  · simpa [hd] using hlen
  · intro j hj
    have hjn : j < n := by simpa using hj
    have hk : i.val * n + j < (flatten A).length := by
      simpa using row_index_lt i (⟨j, hjn⟩ : Fin n)
    rw [hs, map_getD _ _ _ hk, flatten_entry A i ⟨j, hjn⟩]
    simp
  · intro j hj
    have hjn : j < n := by simpa using hj
    have hk : i.val * n + j < (flatten A).length := by
      simpa using row_index_lt i (⟨j, hjn⟩ : Fin n)
    rw [hn, map_getD _ _ _ hk, flatten_entry A i ⟨j, hjn⟩]
    simp
  · intro j hj
    have hjn : j < n := by simpa using hj
    have hk : i.val * n + j < (flatten A).length := by
      simpa using row_index_lt i (⟨j, hjn⟩ : Fin n)
    rw [hd, map_getD _ _ _ hk, flatten_entry A i ⟨j, hjn⟩]
    simp

theorem loadFlat_spec (B m n : ℕ) (a : String) (A : Matrix (Fin m) (Fin n) ℚ)
    (k : Fin (m * n)) (hB : 1 < B) (hkB : k.val < B)
    (hn : (A k.divNat k.modNat).num.natAbs < B) (hd : (A k.divNat k.modNat).den < B) :
    Spec B (fun σ => Represents a (flatten A) σ ∧ σ.vars "vec.i" = k.val)
      (loadLeft a) (fun _ τ => LeftOutput (A k.divNat k.modNat) τ) 9 := by
  have hk : k.val < (flatten A).length := by simp
  have hq : (flatten A)[k.val] = A k.divNat k.modNat := by simp [flatten]
  have hload := loadLeft_spec B a (flatten A) k.val hk hB hkB
    (by rw [hq]; exact hn) (by rw [hq]; exact hd)
  simpa only [hq] using hload

end Lax109476Proofs.RamMatrixStorage

import Lax109476Proofs.RecoveryQueryEntries
import Lax109476Proofs.RamPadSelector

namespace Lax109476Proofs.RamRecoverySelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamMatrixStorage RationalArithmeticBounds RecoveryQueryEntries

def negativeOne : Com := .seq (.assign "rat.s" (.lit 1))
  (.seq (.assign "rat.n" (.lit 1)) (.assign "rat.d" (.lit 1)))

theorem negativeOne_spec (B : ℕ) (h1 : 1 < B) :
    Spec B (fun _ => True) negativeOne (fun _ τ => FractionOutput (-1) τ) 6 := by
  intro σ _
  run_vcg
  all_goals norm_num [FractionOutput, fractionValue]

def selectEntry : Com := .ite (.lt (.var "query.row") (.var "point.m"))
  (.seq (.assign "vec.i" (.add (.mul (.var "query.row") (.var "point.n")) (.var "query.col")))
    (.seq (loadLeft "point.A") RamCopy.leftToResult))
  (.ite (.lt (.var "query.row") (.add (.var "point.m") (.var "point.n")))
    (.ite (.lt (.sub (.var "query.row") (.var "point.m")) (.var "point.k"))
      (.ite (.eq (.var "query.col") (.sub (.var "query.row") (.var "point.m")))
        (RamPadSelector.constantFraction 1) (RamPadSelector.constantFraction 0))
      (RamPadSelector.constantFraction 0))
    (.ite (.lt (.var "query.row") (.add (.add (.var "point.m") (.var "point.n")) (.var "point.n")))
      (.ite (.lt (.sub (.sub (.var "query.row") (.var "point.m")) (.var "point.n")) (.var "point.k"))
        (.ite (.eq (.var "query.col") (.sub (.sub (.var "query.row") (.var "point.m")) (.var "point.n")))
          negativeOne (RamPadSelector.constantFraction 0))
        (RamPadSelector.constantFraction 0))
      (.ite (.eq (.var "query.col") (.var "point.k"))
        (RamPadSelector.constantFraction 1) (RamPadSelector.constantFraction 0))))

def fields : List String := ["point.m", "point.n", "point.k", "query.row", "query.col"]

set_option maxHeartbeats 2000000 in
theorem selectEntry_spec (B M m n k : ℕ) (P : Program ℚ m n) (hk : k < n)
    (i : Fin ((m + (n + n)) + 1)) (j : Fin n) (hM : 1 ≤ M) (hMB : M < B)
    (hB : ((m + (n + n)) + 1) * n + m + (n + n) + 4 < B)
    (hA : ∀ i j, Height (P.A i j) M) :
    Spec B (fun σ => Represents "point.A" (RamMatrixStorage.flatten P.A) σ ∧
      σ.vars "point.m" = m ∧ σ.vars "point.n" = n ∧ σ.vars "point.k" = k ∧
      σ.vars "query.row" = i.val ∧ σ.vars "query.col" = j.val)
      selectEntry (fun _ τ => FractionOutput (entry P k i j) τ) 76 := by
  have h1 : 1 < B := by omega
  have hiB : i.val < B := i.isLt.trans (by omega)
  have hjB : j.val < B := j.isLt.trans (by omega)
  have hm : m < B := by omega
  have hn : n < B := by omega
  have hkB : k < B := hk.trans hn
  have hmnB : m * n < B := (Nat.mul_le_mul_right n (show m ≤ (m + (n + n)) + 1 by omega)).trans_lt (by omega)
  have hzero := RamPadSelector.constantFraction_spec B 0 h1 (by omega)
  have hone := RamPadSelector.constantFraction_spec B 1 h1 h1
  have hneg := negativeOne_spec B h1
  rintro σ ⟨hσA, hσm, hσn, hσk, hσi, hσj⟩
  by_cases hi : i.val < m
  · let ii : Fin m := ⟨i.val, hi⟩
    let index := i.val * n + j.val
    have hindex : index < (RamMatrixStorage.flatten P.A).length := by
      simpa [index, ii, RamMatrixStorage.flatten] using RamMatrixStorage.row_index_lt ii j
    have hindexB : index < B := (by simpa only [RamMatrixStorage.flatten, List.length_ofFn] using hindex : index < m * n).trans hmnB
    have hmulB : i.val * n < B := by dsimp only [index] at hindexB; omega
    have hentry : (RamMatrixStorage.flatten P.A)[index] = P.A ii j := RamMatrixStorage.flatten_entry P.A ii j
    have hq := hA ii j
    have hload := spec_with_fields fields
      (loadLeft_spec B "point.A" (RamMatrixStorage.flatten P.A) index hindex h1 hindexB
        (by rw [hentry]; exact hq.1.trans_lt hMB) (by rw [hentry]; exact hq.2.trans_lt hMB))
      (by intro x hx; simp [fields] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide) (by rfl)
    have hresult := RamCopy.leftToResult_spec B (P.A ii j) h1 (hq.1.trans_lt hMB) (hq.2.trans_lt hMB)
    run_vcg [hload, hresult]
    all_goals clear hload hresult
    all_goals simp_all [fields, FieldsAgree, entry, index, ii, Represents]
    all_goals omega
  · run_vcg [hzero, hone, hneg]
    all_goals clear hzero hone hneg
    all_goals simp_all [entry, Represents]
    all_goals (try split_ifs) <;> (try simp_all) <;> omega

end Lax109476Proofs.RamRecoverySelector

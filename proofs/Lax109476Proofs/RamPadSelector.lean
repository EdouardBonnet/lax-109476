import Lax109476Proofs.RamPadEntries
import Lax109476Proofs.RamCopy

namespace Lax109476Proofs.RamPadSelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamMatrixStorage RamPadEntries RationalArithmeticBounds

def constantFraction (v : ℕ) : Com := .seq (.assign "rat.s" (.lit 0))
  (.seq (.assign "rat.n" (.lit v)) (.assign "rat.d" (.lit 1)))

theorem constantFraction_spec (B v : ℕ) (h1 : 1 < B) (hv : v < B) :
    Spec B (fun _ => True) (constantFraction v) (fun _ τ => FractionOutput (v : ℚ) τ) 6 := by
  intro σ _
  run_vcg
  all_goals simp [FractionOutput, fractionValue]

def selectEntry : Com := .ite (.lt (.var "pad.row") (.var "source.m"))
  (.ite (.lt (.var "pad.col") (.var "source.n"))
    (.seq (.assign "vec.i" (.add (.mul (.var "pad.row") (.var "source.n")) (.var "pad.col")))
      (.seq (loadLeft "query.A") RamCopy.leftToResult)) (constantFraction 0))
  (.ite (.lt (.var "pad.col") (.var "source.n")) (constantFraction 0)
    (.ite (.eq (.sub (.var "pad.row") (.var "source.m"))
      (.sub (.var "pad.col") (.var "source.n"))) (constantFraction 1) (constantFraction 0)))

def fields : List String := ["source.m", "source.n", "pad.row", "pad.col"]

set_option maxHeartbeats 600000 in
theorem selectEntry_spec (B M m n : ℕ) (P : Program ℚ m n)
    (i : Fin (m + 2)) (j : Fin (n + 2)) (h1 : 1 < B) (hM : 1 ≤ M)
    (hMB : M < B) (hmB : m + 2 < B) (hnB : n + 2 < B) (hmnB : m * n < B)
    (hA : ∀ i j, Height (P.A i j) M) :
    Spec B (fun σ => Represents "query.A" (RamMatrixStorage.flatten P.A) σ ∧
        σ.vars "source.m" = m ∧ σ.vars "source.n" = n ∧
        σ.vars "pad.row" = i.val ∧ σ.vars "pad.col" = j.val)
      selectEntry (fun _ τ => FractionOutput (entry P i j) τ) 40 := by
  have hiB : i.val < B := i.isLt.trans hmB
  have hjB : j.val < B := j.isLt.trans hnB
  have hm : m < B := by omega
  have hn : n < B := by omega
  have hzero := constantFraction_spec B 0 h1 (by omega)
  have hone := constantFraction_spec B 1 h1 h1
  rintro σ ⟨hσA, hσm, hσn, hσi, hσj⟩
  by_cases hi : i.val < m
  · by_cases hj : j.val < n
    · let ii : Fin m := ⟨i.val, hi⟩
      let jj : Fin n := ⟨j.val, hj⟩
      let k := i.val * n + j.val
      have hk : k < (RamMatrixStorage.flatten P.A).length := by simpa [k, ii, jj, RamMatrixStorage.flatten] using RamMatrixStorage.row_index_lt ii jj
      have hkB : k < B := (by simpa only [RamMatrixStorage.flatten, List.length_ofFn] using hk : k < m * n).trans hmnB
      have hmulB : i.val * n < B := by dsimp [k] at hkB; omega
      have hentry : (RamMatrixStorage.flatten P.A)[k] = P.A ii jj := RamMatrixStorage.flatten_entry P.A ii jj
      have hq := hA ii jj
      have hload := spec_with_fields fields
        (loadLeft_spec B "query.A" (RamMatrixStorage.flatten P.A) k hk h1 hkB
          (by rw [hentry]; exact hq.1.trans_lt hMB) (by rw [hentry]; exact hq.2.trans_lt hMB))
        (by intro x hx; simp [fields] at hx; rcases hx with rfl | rfl | rfl | rfl <;> decide) (by rfl)
      have hresult := RamCopy.leftToResult_spec B (P.A ii jj) h1 (hq.1.trans_lt hMB) (hq.2.trans_lt hMB)
      run_vcg [hload, hresult]
      all_goals clear hload hresult
      all_goals simp_all [fields, FieldsAgree, entry, k, ii, jj, Represents]
      all_goals (try split_ifs) <;> (try simp_all) <;> omega
    · run_vcg [hzero]
      all_goals simp_all [entry, Represents]
      all_goals (try split_ifs) <;> (try simp_all) <;> omega
  · by_cases hj : j.val < n
    · run_vcg [hzero]
      all_goals simp_all [entry, Represents]
      all_goals (try split_ifs) <;> (try simp_all) <;> omega
    · by_cases he : i.val - m = j.val - n
      · run_vcg [hone]
        all_goals simp_all [entry, Represents]
        all_goals (try split_ifs) <;> (try simp_all) <;> omega
      · run_vcg [hzero]
        all_goals simp_all [entry, Represents]
        all_goals (try split_ifs) <;> (try simp_all) <;> omega

end Lax109476Proofs.RamPadSelector

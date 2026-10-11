import Lax109476Proofs.RamRecoverySelector
import Lax109476Proofs.RamArrayResult
import Lax109476Proofs.RamResultNegation

namespace Lax109476Proofs.RamRecoveryBoundSelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds RecoveryQueryEntries RamRationalScalars

def selectBound : Com := .ite (.lt (.var "query.row") (.var "point.m"))
  (.seq (.assign "vec.i" (.var "query.row")) (RamArrayResult.load "point.b"))
  (.ite (.lt (.var "query.row") (.add (.var "point.m") (.var "point.n")))
    (.ite (.lt (.sub (.var "query.row") (.var "point.m")) (.var "point.k"))
      (.seq (.assign "vec.i" (.sub (.var "query.row") (.var "point.m"))) (RamArrayResult.load "point.x"))
      (RamPadSelector.constantFraction 0))
    (.ite (.lt (.var "query.row") (.add (.add (.var "point.m") (.var "point.n")) (.var "point.n")))
      (.ite (.lt (.sub (.sub (.var "query.row") (.var "point.m")) (.var "point.n")) (.var "point.k"))
        (.seq (.assign "vec.i" (.sub (.sub (.var "query.row") (.var "point.m")) (.var "point.n")))
          (.seq (RamArrayResult.load "point.x") RamResultNegation.negateResult))
        (RamPadSelector.constantFraction 0))
      (RamScalarCopy.copy "bisect.mid" "rat")))

def fields : List String := ["point.m", "point.n", "point.k", "query.row"]

set_option maxHeartbeats 2000000 in
theorem selectBound_spec (B M m n k : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ) (hk : k < n)
    (t : ℚ) (i : Fin ((m + (n + n)) + 1)) (hM : 1 ≤ M) (hMB : M < B)
    (hB : m + (n + n) + 4 < B) (hb : ∀ i, Height (P.b i) M)
    (hx : ∀ j, Height (x j) M) (ht : Height t M) :
    Spec B (fun σ => Represents "point.b" (List.ofFn P.b) σ ∧ Represents "point.x" (List.ofFn x) σ ∧
      Value "bisect.mid" t σ ∧ σ.vars "point.m" = m ∧ σ.vars "point.n" = n ∧
      σ.vars "point.k" = k ∧ σ.vars "query.row" = i.val)
      selectBound (fun _ τ => FractionOutput (bound P x k t i) τ) 80 := by
  have h1 : 1 < B := by omega
  have hiB : i.val < B := i.isLt.trans (by omega)
  have hm : m < B := by omega
  have hn : n < B := by omega
  have hkB : k < B := hk.trans hn
  have hzero := RamPadSelector.constantFraction_spec B 0 h1 (by omega)
  rintro σ ⟨hσb, hσx, hσt, hσm, hσn, hσk, hσi⟩
  by_cases hi : i.val < m
  · let ii : Fin m := ⟨i.val, hi⟩
    have hq := hb ii
    have hload := spec_with_fields fields
      (RamArrayResult.load_spec B "point.b" (List.ofFn P.b) i.val (by simpa using hi) h1 hiB
        (by simpa [ii] using hq.1.trans_lt hMB) (by simpa [ii] using hq.2.trans_lt hMB))
      (by intro z hz; simp [fields] at hz; rcases hz with rfl | rfl | rfl | rfl <;> decide) (by rfl)
    run_vcg [hload]
    all_goals clear hload
    all_goals simp_all [bound, Represents, fields, FieldsAgree, ii]
    all_goals (try split_ifs) <;> (try simp_all) <;> omega
  · by_cases hi₂ : i.val < m + n
    · by_cases ha : i.val - m < k
      · let j : Fin n := ⟨i.val - m, by omega⟩
        have hjB : i.val - m < B := (Nat.sub_le _ _).trans_lt hiB
        have hq := hx j
        have hload := spec_with_fields fields
          (RamArrayResult.load_spec B "point.x" (List.ofFn x) j.val (by simp) h1 hjB
            (by simpa using hq.1.trans_lt hMB) (by simpa using hq.2.trans_lt hMB))
          (by intro z hz; simp [fields] at hz; rcases hz with rfl | rfl | rfl | rfl <;> decide) (by rfl)
        run_vcg [hload]
        all_goals clear hload
        all_goals simp_all [bound, Represents, fields, FieldsAgree, j]
        all_goals (try split_ifs) <;> (try simp_all) <;> omega
      · run_vcg [hzero]
        all_goals simp_all [bound, Represents]
        all_goals (try split_ifs) <;> (try simp_all) <;> omega
    · by_cases hi₃ : i.val < m + n + n
      · by_cases ha : i.val - m - n < k
        · let j : Fin n := ⟨i.val - m - n, by omega⟩
          have hjB : i.val - m - n < B := by omega
          have hq := hx j
          have hload := spec_with_fields fields
            (RamArrayResult.load_spec B "point.x" (List.ofFn x) j.val (by simp) h1 hjB
              (by simpa using hq.1.trans_lt hMB) (by simpa using hq.2.trans_lt hMB))
            (by intro z hz; simp [fields] at hz; rcases hz with rfl | rfl | rfl | rfl <;> decide) (by rfl)
          have hneg := RamResultNegation.negateResult_spec B (x j) h1
          run_vcg [hload, hneg]
          all_goals clear hload hneg
          all_goals simp_all [bound, Represents, fields, FieldsAgree, j]
          all_goals (try split_ifs) <;> (try simp_all) <;> omega
        · run_vcg [hzero]
          all_goals simp_all [bound, Represents]
          all_goals (try split_ifs) <;> (try simp_all) <;> omega
      · have hcopy := RamArrayResult.copyResult_spec B "bisect.mid" t h1 (ht.1.trans_lt hMB) (ht.2.trans_lt hMB)
          (by simp [RamCopy.Disjoint, RamCopy.suffixes])
        run_vcg [hcopy]
        all_goals simp_all [bound, Represents]
        all_goals (try split_ifs) <;> (try simp_all) <;> omega

end Lax109476Proofs.RamRecoveryBoundSelector

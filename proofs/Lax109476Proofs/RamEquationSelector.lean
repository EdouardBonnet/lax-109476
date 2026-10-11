import Lax109476Proofs.EquationQueryEntries
import Lax109476Proofs.RamEquationData

namespace Lax109476Proofs.RamEquationSelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds RamEquationData EquationQueryEntries IntegerEncoding

def selectSlack : Com := .ite (.lt (.var "query.col") (.var "system.n"))
  (.seq (.assign "vec.i" (.add (.mul (.var "query.baseRow") (.var "system.n")) (.var "query.col")))
    (RamArrayResult.load "system.A"))
  (.ite (.eq (.sub (.var "query.col") (.var "system.n")) (.var "query.baseRow"))
    (RamPadSelector.constantFraction 1) (RamPadSelector.constantFraction 0))

def slackFields : List String := ["system.m", "system.n", "query.row", "query.baseRow", "query.col"]

set_option maxHeartbeats 1000000 in
theorem selectSlack_spec (B M m n : ℕ) (P : Program ℤ m n) (i : Fin m) (j : Fin (n + m))
    (hM : 1 ≤ M) (hMB : M < B) (hB : m * n + m + n + 4 < B)
    (hA : ∀ r s, (P.A r s).natAbs ≤ M) :
    Spec B (fun σ => Data P σ ∧ σ.vars "query.baseRow" = i.val ∧ σ.vars "query.col" = j.val)
      selectSlack (fun _ τ => FractionOutput (slackEntry P i j) τ) 32 := by
  have h1 : 1 < B := by omega
  have hiB : i.val < B := i.isLt.trans (by omega)
  have hjB : j.val < B := j.isLt.trans (by omega)
  have hnB : n < B := by omega
  have hmB : m < B := by omega
  have hzero := RamPadSelector.constantFraction_spec B 0 h1 (by omega)
  have hone := RamPadSelector.constantFraction_spec B 1 h1 h1
  rintro σ ⟨⟨hσA, hσb, hσm, hσn⟩, hσi, hσj⟩
  by_cases hj : j.val < n
  · let jj : Fin n := ⟨j.val, hj⟩
    let index := i.val * n + j.val
    have hindex : index < (RamMatrixStorage.flatten (rationalProgram P).A).length := by
      simpa [RamMatrixStorage.flatten, index, jj] using RamMatrixStorage.row_index_lt i jj
    have hindexB : index < B := (by simpa only [RamMatrixStorage.flatten, List.length_ofFn] using hindex : index < m * n).trans
      (by omega)
    have hmulB : i.val * n < B := by dsimp only [index] at hindexB; omega
    have he : (RamMatrixStorage.flatten (rationalProgram P).A)[index] = (P.A i jj : ℚ) :=
      RamMatrixStorage.flatten_entry (rationalProgram P).A i jj
    have hq : Height (P.A i jj : ℚ) M := ⟨by simpa using hA i jj, by simpa using hM⟩
    have hload := spec_with_fields slackFields
      (RamArrayResult.load_spec B "system.A" (RamMatrixStorage.flatten (rationalProgram P).A) index
        hindex h1 hindexB (by rw [he]; exact hq.1.trans_lt hMB) (by rw [he]; exact hq.2.trans_lt hMB))
      (by intro a ha; simp [slackFields] at ha; rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide) (by rfl)
    run_vcg [hload]
    all_goals clear hload
    all_goals simp_all [slackFields, FieldsAgree, slackEntry, index, jj, Represents]
    all_goals omega
  · have hsub : j.val - n < B := (Nat.sub_le _ _).trans_lt hjB
    run_vcg [hzero, hone]
    all_goals clear hzero hone
    all_goals simp_all [slackEntry, Represents]
    all_goals (try split_ifs) <;> (try simp_all) <;> omega

def prepareRow : Com := .ite (.lt (.var "query.row") (.var "system.m"))
  (.assign "query.baseRow" (.var "query.row"))
  (.assign "query.baseRow" (.sub (.var "query.row") (.var "system.m")))

def applyRowSign : Com := .ite (.lt (.var "query.row") (.var "system.m")) .skip RamResultNegation.negateResult

def selectEntry : Com := .seq prepareRow (.seq selectSlack applyRowSign)

theorem applyRowSign_spec (B m row : ℕ) (q : ℚ) (h1 : 1 < B) (hm : m < B) (hr : row < B) :
    Spec B (fun σ => FractionOutput q σ ∧ σ.vars "system.m" = m ∧ σ.vars "query.row" = row)
      applyRowSign (fun _ τ => FractionOutput (if row < m then q else -q) τ) 8 := by
  have hn := RamResultNegation.negateResult_spec B q h1
  rintro σ ⟨hσq, hσm, hσrow⟩
  by_cases hrow : row < m
  · run_vcg [hn]
    all_goals clear hn
    all_goals simp_all
  · run_vcg [hn]
    all_goals clear hn
    all_goals simp_all
    all_goals split_ifs <;> (try simp_all) <;> omega

set_option maxHeartbeats 1000000 in
theorem selectEntry_spec (B M m n : ℕ) (P : Program ℤ m n) (i : Fin (m + m)) (j : Fin (n + m))
    (hM : 1 ≤ M) (hMB : M < B) (hB : (m + m) * (n + m) + m + n + 4 < B)
    (hA : ∀ r s, (P.A r s).natAbs ≤ M) :
    Spec B (fun σ => Data P σ ∧ σ.vars "query.row" = i.val ∧ σ.vars "query.col" = j.val)
      selectEntry (fun _ τ => Data P τ ∧ FractionOutput (entry P i j) τ) 48 := by
  have h1 : 1 < B := by omega
  have hm : m < B := by omega
  have hmpos : 0 < m := by have hi := i.isLt; omega
  have hrows : m + m ≤ (m + m) * (n + m) := Nat.le_mul_of_pos_right _ (by omega)
  have hiB : i.val < B := (i.isLt.trans_le hrows).trans (by omega)
  have hjB : j.val < B := j.isLt.trans (by omega)
  have hmn : m * n ≤ (m + m) * (n + m) := Nat.mul_le_mul (by omega) (by omega)
  let r : Fin m := if hi : i.val < m then ⟨i.val, hi⟩ else ⟨i.val - m, by omega⟩
  have hrB : r.val < B := r.isLt.trans hm
  have hprepare : Spec B (fun σ => σ.vars "system.m" = m ∧ σ.vars "query.row" = i.val)
      prepareRow (fun _ τ => τ.vars "query.baseRow" = r.val) 8 := by
    rintro σ ⟨hσm, hσrow⟩
    have hsub : i.val - m < B := (Nat.sub_le _ _).trans_lt hiB
    run_vcg
    all_goals simp_all [r]
    all_goals (try split_ifs) <;> (try simp_all) <;> omega
  rintro σ ⟨hσData, hσrow, hσcol⟩
  obtain ⟨τ, hr₁, hτr⟩ := hprepare σ ⟨hσData.2.2.1, hσrow⟩
  have hτData := data_frame hr₁ P hσData
    (by intro a ha; simp [RamEquationData.fields] at ha; rcases ha with rfl | rfl <;> decide)
    (by intro a ha s hs; change a ++ s ∉ ([] : List String); simp)
  have hτcol := (hr₁.frame_var "query.col" (by decide)).trans hσcol
  obtain ⟨υ, hr₂, hυq⟩ := selectSlack_spec B M m n P r j hM hMB (by omega) hA τ ⟨hτData, hτr, hτcol⟩
  have hυm := (hr₂.frame_var "system.m" (by decide)).trans hτData.2.2.1
  have hυrow := (hr₂.frame_var "query.row" (by decide)).trans ((hr₁.frame_var _ (by decide)).trans hσrow)
  obtain ⟨ρ, hr₃, hρq⟩ := applyRowSign_spec B m i.val (slackEntry P r j) h1 hm hiB υ ⟨hυq, hυm, hυrow⟩
  have hr := hr₁.seq (hr₂.seq hr₃)
  refine ⟨ρ, hr, data_frame hr P hσData ?_ ?_, ?_⟩
  · intro a ha; simp [RamEquationData.fields] at ha; rcases ha with rfl | rfl <;> decide
  · intro a ha s hs; change a ++ s ∉ ([] : List String); simp
  · by_cases hi : i.val < m <;> simpa [entry, r, hi] using hρq

end Lax109476Proofs.RamEquationSelector

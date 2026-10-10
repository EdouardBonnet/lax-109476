import Lax109476Proofs.RamPadSelector
import Lax109476Proofs.RamScaleCoordinate
import Lax109476Proofs.NormalizedFeasibility

namespace Lax109476Proofs.RamNormalizedEntry

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamFractionInterface RationalArithmeticBounds
open RamMatrixStorage IntegerEncoding NormalizedFeasibility RamScaleCoordinate

def entry {m n : ℕ} (P : Program ℤ m n) (R : ℕ) (i : Fin (m + n)) (j : Fin n) : ℚ :=
  if hi : i.val < m then (P.A ⟨i.val, hi⟩ j : ℚ) * (R : ℚ)
  else if i.val - m = j.val then -(R : ℚ) else 0

theorem entry_eq {m n : ℕ} (P : Program ℤ m n) (R : ℕ) (i : Fin (m + n)) (j : Fin n) :
    entry P R i j = (normalizedMatrix P R i j : ℚ) := by
  refine Fin.addCases ?_ ?_ i
  · intro i
    simp [entry, normalizedMatrix, i.isLt, mul_comm]
  · intro k
    simp [entry, normalizedMatrix, Fin.ext_iff, apply_ite]
    split_ifs <;> simp_all

theorem entry_height {m n : ℕ} (P : Program ℤ m n) (R M : ℕ)
    (hM : 1 ≤ M) (hR : R ≤ M) (hA : ∀ i j, (P.A i j).natAbs ≤ M)
    (i : Fin (m + n)) (j : Fin n) : Height (entry P R i j) (M ^ 2) := by
  have hMM : M ≤ M ^ 2 := by nlinarith
  have hnat := height_nat R M hR hM
  unfold entry
  split_ifs with hi he
  · have hq : Height (P.A ⟨i.val, hi⟩ j : ℚ) M := by simpa [Height] using And.intro (hA ⟨i.val, hi⟩ j) hM
    simpa only [pow_two] using height_mul _ _ M M hq hnat
  · exact height_mono _ (height_neg _ M hnat) hMM
  · exact height_mono _ height_zero (hM.trans hMM)

def negativeFactor : Com := .seq (.assign "rat.s" (.lit 1))
  (.seq (.assign "rat.n" (.var "cap.R")) (.assign "rat.d" (.lit 1)))

theorem negativeFactor_spec (B R : ℕ) (h1 : 1 < B) (hRB : R < B) :
    Spec B (fun σ => σ.vars "cap.R" = R) negativeFactor
      (fun _ τ => FractionOutput (-(R : ℚ)) τ) 6 := by
  intro σ hσ
  run_vcg
  all_goals simp_all [FractionOutput, fractionValue]

def selectEntry : Com := .ite (.lt (.var "norm.row") (.var "query.m"))
  (.seq (.assign "vec.i" (.add (.mul (.var "norm.row") (.var "query.n")) (.var "norm.col")))
    (.seq (loadLeft "pad.A") (.seq (.assign "scale.factor" (.var "cap.R"))
      (.seq prepareFactor RamRational.multiplyFraction))))
  (.ite (.eq (.sub (.var "norm.row") (.var "query.m")) (.var "norm.col"))
    negativeFactor (RamPadSelector.constantFraction 0))

def fields : List String := ["query.m", "query.n", "norm.row", "norm.col", "cap.R"]

set_option maxHeartbeats 800000 in
theorem selectEntry_spec (B M m n R : ℕ) (P : Program ℤ m n) (i : Fin (m + n)) (j : Fin n)
    (hM : 1 ≤ M) (hR : R ≤ M) (hB : 2 * M ^ 2 + 3 < B)
    (hdim : (m + n) * n + m + n + 1 < B) (hA : ∀ i j, (P.A i j).natAbs ≤ M) :
    Spec B (fun σ => Represents "pad.A" (RamMatrixStorage.flatten (rationalProgram P).A) σ ∧
        σ.vars "query.m" = m ∧ σ.vars "query.n" = n ∧ σ.vars "norm.row" = i.val ∧
        σ.vars "norm.col" = j.val ∧ σ.vars "cap.R" = R)
      selectEntry (fun _ τ => FractionOutput (entry P R i j) τ) (72 * M.size + 100) := by
  have hMB : M < B := by nlinarith
  have hRB : R < B := hR.trans_lt hMB
  have h1 : 1 < B := by nlinarith
  have hiB : i.val < B := i.isLt.trans (by omega)
  have hjB : j.val < B := j.isLt.trans (by omega)
  have hmB : m < B := by omega
  have hnB : n < B := by omega
  have hzero := RamPadSelector.constantFraction_spec B 0 h1 (by omega)
  have hneg := negativeFactor_spec B R h1 hRB
  have hz : Height (0 : ℚ) M := height_mono 0 height_zero hM
  have hdead := multiply_spec B M 0 0 hB hz hz
  rintro σ ⟨hσA, hσm, hσn, hσi, hσj, hσR⟩
  by_cases hi : i.val < m
  · let ii : Fin m := ⟨i.val, hi⟩
    let k := i.val * n + j.val
    have hk : k < (RamMatrixStorage.flatten (rationalProgram P).A).length := by
      simpa only [RamMatrixStorage.flatten, List.length_ofFn] using row_index_lt ii j
    have hmn : m * n ≤ (m + n) * n := Nat.mul_le_mul_right n (by omega)
    have hkB : k < B := (by simpa only [RamMatrixStorage.flatten, List.length_ofFn] using hk : k < m * n).trans (by omega)
    have hmulB : i.val * n < B := by dsimp [k] at hkB; omega
    have he : (RamMatrixStorage.flatten (rationalProgram P).A)[k] = (P.A ii j : ℚ) := flatten_entry _ ii j
    have hq : Height (P.A ii j : ℚ) M := by simpa [Height] using And.intro (hA ii j) hM
    have hrq := height_nat R M hR hM
    have hload := spec_with_fields fields
      (loadLeft_spec B "pad.A" (RamMatrixStorage.flatten (rationalProgram P).A) k hk h1 hkB
        (by rw [he]; exact hq.1.trans_lt hMB) (by rw [he]; exact hq.2.trans_lt hMB))
      (by intro x hx; simp [fields] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide) (by rfl)
    have hfactor := spec_with_fields ["left.s", "left.n", "left.d"] (prepareFactor_spec B R h1 hRB)
      (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> decide) (by rfl)
    have hcanonical : fractionValue (rationalSign (P.A ii j : ℚ)) (P.A ii j).natAbs 1 = (P.A ii j : ℚ) := by
      simpa using canonical_fractionValue (P.A ii j : ℚ)
    have hproduct := multiply_spec B M (P.A ii j : ℚ) (R : ℚ) hB hq hrq
    run_vcg [hload, hfactor, hproduct]
    all_goals clear hload hfactor hproduct
    all_goals simp_all [fields, FieldsAgree, Represents, entry, k, ii, LeftOutput,
      LeftValue, RightValue, hcanonical, rationalSign_le_one]
    all_goals aesop
  · by_cases he : i.val - m = j.val
    · run_vcg [hneg, hdead]
      all_goals simp_all [entry, Represents]
      all_goals (try split_ifs) <;> (try simp_all) <;> omega
    · run_vcg [hzero, hdead]
      all_goals simp_all [entry, Represents]
      all_goals (try split_ifs) <;> (try simp_all) <;> omega

end Lax109476Proofs.RamNormalizedEntry

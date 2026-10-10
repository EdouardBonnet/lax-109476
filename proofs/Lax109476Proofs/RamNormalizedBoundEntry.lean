import Lax109476Proofs.RamNormalizedEntry

namespace Lax109476Proofs.RamNormalizedBoundEntry

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamFractionInterface RationalArithmeticBounds
open IntegerEncoding NormalizedFeasibility

def entry {m n : ℕ} (P : Program ℤ m n) (D : ℕ) (i : Fin (m + n)) : ℚ :=
  if hi : i.val < m then (P.b ⟨i.val, hi⟩ : ℚ) + 1 / (D : ℚ) else 1 / (D : ℚ)

theorem entry_eq {m n : ℕ} (P : Program ℤ m n) (D : ℕ) (i : Fin (m + n)) :
    entry P D i = normalizedBound P (1 / (D : ℚ)) i := by
  refine Fin.addCases ?_ ?_ i
  · intro i
    simp [entry, normalizedBound, i.isLt]
  · intro i
    simp [entry, normalizedBound]

theorem epsilon_height (D : ℕ) (hD : 0 < D) : Height (1 / (D : ℚ)) D := by
  simpa only [one_div] using height_inv (D : ℚ) D (height_nat D D le_rfl hD)

theorem entry_height {m n : ℕ} (P : Program ℤ m n) (D M : ℕ) (hM : 1 ≤ M)
    (hD : 0 < D) (hDM : D ≤ M) (hb : ∀ i, (P.b i).natAbs ≤ M) (i : Fin (m + n)) :
    Height (entry P D i) (2 * M ^ 2) := by
  have hε := height_mono _ (epsilon_height D hD) hDM
  unfold entry
  split_ifs with hi
  · have hq : Height (P.b ⟨i.val, hi⟩ : ℚ) M := by simpa [Height] using And.intro (hb ⟨i.val, hi⟩) hM
    simpa only [pow_two, Nat.mul_assoc] using height_add _ _ M M hq hε
  · exact height_mono _ hε (by nlinarith)

def prepareEpsilon : Com := .seq (.assign "right.s" (.lit 0))
  (.seq (.assign "right.n" (.lit 1)) (.assign "right.d" (.var "cap.D")))

theorem prepareEpsilon_spec (B D : ℕ) (h1 : 1 < B) (hD : 0 < D) (hDB : D < B) :
    Spec B (fun σ => σ.vars "cap.D" = D) prepareEpsilon
      (fun _ τ => RightValue (1 / (D : ℚ)) τ) 6 := by
  have hn : (1 / (D : ℚ)).num = 1 := by simpa only [one_div] using Rat.inv_natCast_num_of_pos hD
  have hd : (1 / (D : ℚ)).den = D := by simpa only [one_div] using Rat.inv_natCast_den_of_pos hD
  intro σ hσ
  run_vcg
  all_goals simp_all [RightValue, fractionValue]
  all_goals exact (congrArg Int.natAbs (Int.sign_eq_one_iff_pos.mpr
    (show (0 : ℤ) < D by exact_mod_cast hD))).symm

def epsilonResult : Com := .seq (.assign "rat.s" (.lit 0))
  (.seq (.assign "rat.n" (.lit 1)) (.assign "rat.d" (.var "cap.D")))

theorem epsilonResult_spec (B D : ℕ) (h1 : 1 < B) (hD : 0 < D) (hDB : D < B) :
    Spec B (fun σ => σ.vars "cap.D" = D) epsilonResult
      (fun _ τ => FractionOutput (1 / (D : ℚ)) τ) 6 := by
  have hn : (1 / (D : ℚ)).num = 1 := by simpa only [one_div] using Rat.inv_natCast_num_of_pos hD
  have hd : (1 / (D : ℚ)).den = D := by simpa only [one_div] using Rat.inv_natCast_den_of_pos hD
  intro σ hσ
  run_vcg
  all_goals simp_all [FractionOutput, fractionValue]
  all_goals exact (congrArg Int.natAbs (Int.sign_eq_one_iff_pos.mpr
    (show (0 : ℤ) < D by exact_mod_cast hD))).symm

def selectBound : Com := .ite (.lt (.var "norm.k") (.var "query.m"))
  (.seq (.assign "vec.i" (.var "norm.k"))
    (.seq (loadLeft "pad.b") (.seq prepareEpsilon RamRational.addFraction))) epsilonResult

def fields : List String := ["query.m", "norm.k", "cap.D"]

set_option maxHeartbeats 800000 in
theorem selectBound_spec (B M m n D : ℕ) (P : Program ℤ m n) (i : Fin (m + n))
    (hM : 1 ≤ M) (hD : 0 < D) (hDM : D ≤ M) (hB : 2 * M ^ 2 + 3 < B)
    (hdim : m + n + 1 < B) (hb : ∀ i, (P.b i).natAbs ≤ M) :
    Spec B (fun σ => Represents "pad.b" (List.ofFn (rationalProgram P).b) σ ∧
        σ.vars "query.m" = m ∧ σ.vars "norm.k" = i.val ∧ σ.vars "cap.D" = D)
      selectBound (fun _ τ => FractionOutput (entry P D i) τ) (72 * M.size + 130) := by
  have hMB : M < B := by nlinarith
  have hDB : D < B := hDM.trans_lt hMB
  have h1 : 1 < B := by nlinarith
  have hiB : i.val < B := i.isLt.trans (by omega)
  have hmB : m < B := by omega
  have hresult := epsilonResult_spec B D h1 hD hDB
  have hz : Height (0 : ℚ) M := height_mono _ height_zero hM
  have hdead := add_spec B M 0 0 hB hz hz
  rintro σ ⟨hσb, hσm, hσi, hσD⟩
  by_cases hi : i.val < m
  · let ii : Fin m := ⟨i.val, hi⟩
    have hq : Height (P.b ii : ℚ) M := by simpa [Height] using And.intro (hb ii) hM
    have hε := height_mono _ (epsilon_height D hD) hDM
    have hload := spec_with_fields fields
      (loadLeft_spec B "pad.b" (List.ofFn (rationalProgram P).b) i.val (by simpa using hi)
        h1 hiB (by simpa [ii, rationalProgram] using hq.1.trans_lt hMB)
        (by simpa [ii, rationalProgram] using hq.2.trans_lt hMB))
      (by intro x hx; simp [fields] at hx; rcases hx with rfl | rfl | rfl <;> decide) (by rfl)
    have hprepare := spec_with_fields ["left.s", "left.n", "left.d"]
      (prepareEpsilon_spec B D h1 hD hDB)
      (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> decide) (by rfl)
    have hcanonical : fractionValue (rationalSign (P.b ii : ℚ)) (P.b ii).natAbs 1 = (P.b ii : ℚ) := by
      simpa using canonical_fractionValue (P.b ii : ℚ)
    have hadd := add_spec B M (P.b ii : ℚ) (1 / (D : ℚ)) hB hq hε
    run_vcg [hload, hprepare, hadd]
    all_goals clear hload hprepare hadd
    all_goals simp_all [fields, FieldsAgree, Represents, entry, ii, LeftOutput, LeftValue,
      RightValue, rationalProgram, hcanonical, rationalSign_le_one]
    all_goals aesop
  · run_vcg [hresult, hdead]
    all_goals simp_all [entry, Represents]
    all_goals (try split_ifs) <;> (try simp_all) <;> omega

end Lax109476Proofs.RamNormalizedBoundEntry

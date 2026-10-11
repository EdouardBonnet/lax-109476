import Lax109476Proofs.RamEquationSelector

namespace Lax109476Proofs.RamEquationMatrix

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds RamEquationData EquationQueryEntries RamEllipsoidStep

def values {m n : ℕ} (P : Program ℤ m n) : Fin ((m + m) * (n + m)) → ℚ :=
  fun i => entry P i.divNat i.modNat

def selectCoordinate : Com := .seq
  (.assign "query.row" (.div (.var "build.i") (.add (.var "system.n") (.var "system.m"))))
  (.seq (.assign "query.col" (.sub (.var "build.i")
    (.mul (.var "query.row") (.add (.var "system.n") (.var "system.m"))))) RamEquationSelector.selectEntry)

set_option maxHeartbeats 1000000 in
theorem selectCoordinate_spec (B M m n : ℕ) (P : Program ℤ m n) (i : Fin ((m + m) * (n + m)))
    (hM : 1 ≤ M) (hMB : M < B) (hB : (m + m) * (n + m) + m + n + 4 < B)
    (hA : ∀ r s, (P.A r s).natAbs ≤ M) :
    Spec B (fun σ => Data P σ ∧ σ.vars "build.i" = i.val ∧ σ.vars "build.count" = (m + m) * (n + m))
      selectCoordinate (fun _ τ => Data P τ ∧ FractionOutput (values P i) τ) 62 := by
  have hiB : i.val < B := i.isLt.trans (by omega)
  have hm : m < B := by omega
  have hn : n < B := by omega
  have hsum : n + m < B := by omega
  have hdiv : i.val / (n + m) < B := (Nat.div_le_self _ _).trans_lt hiB
  have hmul : (i.val / (n + m)) * (n + m) < B := (Nat.div_mul_le_self _ _).trans_lt hiB
  have hsub : i.val - (i.val / (n + m)) * (n + m) < B := (Nat.sub_le _ _).trans_lt hiB
  have hmod : i.val - (i.val / (n + m)) * (n + m) = i.val % (n + m) := by
    simpa [Nat.mul_comm] using (Nat.mod_eq_sub_mul_div (x := i.val) (k := n + m)).symm
  have hselector := RamEquationSelector.selectEntry_spec B M m n P i.divNat i.modNat hM hMB hB hA
  have hbase : Spec B (fun σ => Data P σ ∧ σ.vars "build.i" = i.val ∧ σ.vars "build.count" = (m + m) * (n + m))
      selectCoordinate (fun _ τ => FractionOutput (values P i) τ) 62 := by
    rintro σ ⟨⟨hσA, hσb, hσm, hσn⟩, hσi, hσcount⟩
    run_vcg [hselector]
    all_goals clear hselector
    all_goals simp_all [values, Fin.divNat, Fin.modNat, Data, Represents, arrs_setVar]
  intro σ hσ
  obtain ⟨τ, hr, hτ⟩ := hbase σ hσ
  refine ⟨τ, hr, data_frame hr P hσ.1 ?_ ?_, hτ⟩
  · intro a ha; simp [RamEquationData.fields] at ha; rcases ha with rfl | rfl <;> decide
  · intro a ha s hs; change a ++ s ∉ ([] : List String); simp

def prepare : Com := .assign "build.count"
  (.mul (.add (.var "system.m") (.var "system.m")) (.add (.var "system.n") (.var "system.m")))

def matrix : Com := .seq prepare (RamBuildVector.build "point.A" selectCoordinate)

set_option maxHeartbeats 1000000 in
theorem matrix_spec (B M m n : ℕ) (P : Program ℤ m n)
    (hM : 1 ≤ M) (hMB : M < B) (hB : (m + m) * (n + m) + m + n + 4 < B)
    (hA : ∀ r s, (P.A r s).natAbs ≤ M) :
    Spec B (fun σ => Data P σ ∧ Extents "point.A" ((m + m) * (n + m)) σ) matrix
      (fun _ τ => Data P τ ∧ Represents "point.A"
        (RamMatrixStorage.flatten (RamStandardPointRecovery.program (IntegerPointRecovery.slackMatrix P) P.b).A) τ)
      (118 * ((m + m) * (n + m)) + 34) := by
  let N := (m + m) * (n + m)
  have h1 : 1 < B := by omega
  have hNB : N < B := by dsimp only [N]; omega
  have hrowsB : m + m < B := by
    by_cases hm : m = 0
    · simp [hm]; omega
    · exact (Nat.le_mul_of_pos_right (m + m) (by omega : 0 < n + m)).trans_lt hNB
  have hbuild := RamBuildVector.build_spec B M N 62 "point.A" (values P) selectCoordinate (Data P)
    h1 hNB hMB (fun i => entry_height P M hM hA i.divNat i.modNat)
    (selectCoordinate_spec B M m n P · hM hMB hB hA) (by decide) (by decide)
    (by intro s hs; change "point.A" ++ s ∉ ([] : List String); simp)
    (preserves_data B P (storeReduced "point.A")
      (by intro a ha; simp [RamEquationData.fields] at ha; rcases ha with rfl | rfl <;> decide)
      (by
        intro a ha s hs
        simp [RamEquationData.arrays] at ha
        simp [RamCopy.suffixes] at hs
        rcases ha with rfl | rfl <;> rcases hs with rfl | rfl | rfl <;> decide))
    (preserves_data B P (RamZeroArray.zeroRationalArray "point.A")
      (by intro a ha; simp [RamEquationData.fields] at ha; rcases ha with rfl | rfl <;> decide)
      (by
        intro a ha s hs
        simp [RamEquationData.arrays] at ha
        simp [RamCopy.suffixes] at hs
        rcases ha with rfl | rfl <;> rcases hs with rfl | rfl | rfl <;> decide))
    (fun σ z h => data_setVar P σ "build.i" z (by decide) h)
    (fun σ z h => data_setVar P σ "vec.i" z (by decide) h)
    (fun σ z h => data_setVar P σ "vec.n" z (by decide) h)
  have hvalues : List.ofFn (values P) = RamMatrixStorage.flatten
      (RamStandardPointRecovery.program (IntegerPointRecovery.slackMatrix P) P.b).A := by
    congr 1
    funext i
    exact entry_eq P i.divNat i.modNat
  have hmeta : Spec B (fun σ => σ.vars "system.m" = m ∧ σ.vars "system.n" = n) prepare
      (fun _ τ => τ.vars "build.count" = N) 8 := by
    rintro σ ⟨hm, hn⟩
    run_vcg
    all_goals simp_all [N]
    all_goals omega
  rintro σ ⟨hσData, hσtarget⟩
  obtain ⟨τ, hr₁, hτcount⟩ := hmeta σ ⟨hσData.2.2.1, hσData.2.2.2⟩
  have hτData := data_frame hr₁ P hσData
    (by intro a ha; simp [RamEquationData.fields] at ha; rcases ha with rfl | rfl <;> decide)
    (by intro a ha s hs; simp [Com.warrs, prepare])
  obtain ⟨υ, hr₂, hυData, hυtarget, hυcount⟩ := hbuild τ
    ⟨hτData, RamAdvanceState.extents_of_run hr₁ "point.A" N hσtarget, hτcount⟩
  refine ⟨υ, (hr₁.seq hr₂).mono ?_, hυData, ?_⟩
  · dsimp only [N]; omega
  · simpa only [hvalues] using hυtarget

end Lax109476Proofs.RamEquationMatrix

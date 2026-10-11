import Lax109476Proofs.RamRecoveryData

namespace Lax109476Proofs.RamRecoveryMatrix

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamMatrixStorage RationalArithmeticBounds RecoveryQueryEntries
open RamRecoveryData RamEllipsoidStep

def values {m n : ℕ} (P : Program ℚ m n) (k : ℕ) : Fin (((m + (n + n)) + 1) * n) → ℚ :=
  fun i => entry P k i.divNat i.modNat

def selectCoordinate : Com := .seq (.assign "query.row" (.div (.var "build.i") (.var "point.n")))
  (.seq (.assign "query.col" (.sub (.var "build.i") (.mul (.var "query.row") (.var "point.n"))))
    RamRecoverySelector.selectEntry)

set_option maxHeartbeats 800000 in
theorem selectCoordinate_spec (B M m n k : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ) (t : ℚ)
    (hk : k < n) (i : Fin (((m + (n + n)) + 1) * n)) (hM : 1 ≤ M) (hMB : M < B)
    (hB : ((m + (n + n)) + 1) * n + m + (n + n) + 4 < B)
    (hA : ∀ r j, Height (P.A r j) M) :
    Spec B (fun σ => Data P x k t σ ∧ σ.vars "build.i" = i.val ∧
      σ.vars "build.count" = ((m + (n + n)) + 1) * n) selectCoordinate
      (fun _ τ => Data P x k t τ ∧ FractionOutput (values P k i) τ) 86 := by
  have hiB : i.val < B := i.isLt.trans (by omega)
  have hnB : n < B := by omega
  have hdivB : i.val / n < B := (Nat.div_le_self _ _).trans_lt hiB
  have hmulB : (i.val / n) * n < B := (Nat.div_mul_le_self _ _).trans_lt hiB
  have hmodB : i.val - (i.val / n) * n < B := (Nat.sub_le _ _).trans_lt hiB
  have hmod : i.val - (i.val / n) * n = i.val % n := by
    simpa [Nat.mul_comm] using (Nat.mod_eq_sub_mul_div (x := i.val) (k := n)).symm
  have hbase : Spec B (fun σ => Data P x k t σ ∧ σ.vars "build.i" = i.val ∧
      σ.vars "build.count" = ((m + (n + n)) + 1) * n) selectCoordinate
      (fun _ τ => FractionOutput (values P k i) τ) 86 := by
    have hselect := RamRecoverySelector.selectEntry_spec B M m n k P hk i.divNat i.modNat hM hMB hB hA
    rintro σ ⟨⟨hσA, hσb, hσx, hσm, hσn, hσk, hσt⟩, hσi, hσcount⟩
    run_vcg [hselect]
    all_goals clear hselect
    all_goals simp_all [values, Fin.divNat, Fin.modNat, Represents, arrs_setVar]
  intro σ hσ
  obtain ⟨τ, hr, hτ⟩ := hbase σ hσ
  refine ⟨τ, hr, data_frame hr P x k t hσ.1 ?_ ?_, hτ⟩
  · intro a ha
    simp [RamRecoveryData.fields] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha s hs
    change a ++ s ∉ ([] : List String)
    simp

def prepare : Com := .assign "build.count"
    (.mul (.add (.add (.var "point.m") (.add (.var "point.n") (.var "point.n"))) (.lit 1)) (.var "point.n"))

def matrix : Com := .seq prepare (RamBuildVector.build "lp.A" selectCoordinate)

set_option maxHeartbeats 1000000 in
theorem matrix_spec (B M m n k : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ) (t : ℚ)
    (hk : k < n) (hM : 1 ≤ M) (hMB : M < B)
    (hB : ((m + (n + n)) + 1) * n + m + (n + n) + 4 < B)
    (hA : ∀ r j, Height (P.A r j) M) :
    Spec B (fun σ => Data P x k t σ ∧ Extents "lp.A" (((m + (n + n)) + 1) * n) σ) matrix
      (fun _ τ => Data P x k t τ ∧ Represents "lp.A"
        (RamMatrixStorage.flatten (CoordinateOptimization.coordinateCut (LexicographicMinima.fixedPrefix P x k) ⟨k, hk⟩ t).A) τ)
      (142 * (((m + (n + n)) + 1) * n) + 36) := by
  let N := ((m + (n + n)) + 1) * n
  have h1 : 1 < B := by omega
  have hNB : N < B := by dsimp only [N]; omega
  have hbuild := RamBuildVector.build_spec B M N 86 "lp.A" (values P k) selectCoordinate (Data P x k t)
    h1 hNB hMB (fun i => entry_height P k M hM hA i.divNat i.modNat)
    (selectCoordinate_spec B M m n k P x t hk · hM hMB hB hA) (by decide) (by decide)
    (by intro s hs; change "lp.A" ++ s ∉ ([] : List String); simp)
    (preserves_data B P x k t (storeReduced "lp.A")
      (by intro a ha; simp [RamRecoveryData.fields] at ha; rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by intro a ha s hs; simp [arrays] at ha; simp [RamCopy.suffixes] at hs; rcases ha with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl <;> decide))
    (preserves_data B P x k t (RamZeroArray.zeroRationalArray "lp.A")
      (by intro a ha; simp [RamRecoveryData.fields] at ha; rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by intro a ha s hs; simp [arrays] at ha; simp [RamCopy.suffixes] at hs; rcases ha with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl <;> decide))
    (fun σ z h => data_setVar P x k t σ "build.i" z (by decide) h)
    (fun σ z h => data_setVar P x k t σ "vec.i" z (by decide) h)
    (fun σ z h => data_setVar P x k t σ "vec.n" z (by decide) h)
  have hvalues : List.ofFn (values P k) = RamMatrixStorage.flatten
      (CoordinateOptimization.coordinateCut (LexicographicMinima.fixedPrefix P x k) ⟨k, hk⟩ t).A := by
    congr 1
    funext i
    exact entry_eq P x k hk t i.divNat i.modNat
  have hmeta : Spec B (fun σ => σ.vars "point.m" = m ∧ σ.vars "point.n" = n) prepare
      (fun _ τ => τ.vars "build.count" = N) 10 := by
    rintro σ ⟨hm, hn⟩
    run_vcg
    all_goals simp_all [N]
    all_goals omega
  rintro σ ⟨hσData, hσtarget⟩
  obtain ⟨τ, hr₁, hτcount⟩ := hmeta σ ⟨hσData.2.2.2.1, hσData.2.2.2.2.1⟩
  have hτData := data_frame hr₁ P x k t hσData
    (by intro a ha; simp [RamRecoveryData.fields] at ha; rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by intro a ha s hs; simp [Com.warrs, prepare])
  have hτtarget := RamAdvanceState.extents_of_run hr₁ "lp.A" N hσtarget
  obtain ⟨υ, hr₂, hυData, hυtarget, hυcount⟩ := hbuild τ ⟨hτData, hτtarget, hτcount⟩
  refine ⟨υ, (hr₁.seq hr₂).mono ?_, hυData, ?_⟩
  · dsimp only [N]
    norm_num only
    omega
  · simpa only [hvalues] using hυtarget

end Lax109476Proofs.RamRecoveryMatrix

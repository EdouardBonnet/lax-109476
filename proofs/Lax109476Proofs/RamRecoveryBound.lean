import Lax109476Proofs.RamRecoveryData

namespace Lax109476Proofs.RamRecoveryBound

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds RecoveryQueryEntries
open RamRecoveryData RamEllipsoidStep

def values {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (k : ℕ) (t : ℚ) :
    Fin ((m + (n + n)) + 1) → ℚ := bound P x k t

def selectCoordinate : Com := .seq (.assign "query.row" (.var "build.i")) RamRecoveryBoundSelector.selectBound

set_option maxHeartbeats 800000 in
theorem selectCoordinate_spec (B M m n k : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ) (t : ℚ)
    (hk : k < n) (i : Fin ((m + (n + n)) + 1)) (hM : 1 ≤ M) (hMB : M < B)
    (hB : m + (n + n) + 4 < B) (hb : ∀ r, Height (P.b r) M)
    (hx : ∀ j, Height (x j) M) (ht : Height t M) :
    Spec B (fun σ => Data P x k t σ ∧ σ.vars "build.i" = i.val ∧
      σ.vars "build.count" = (m + (n + n)) + 1) selectCoordinate
      (fun _ τ => Data P x k t τ ∧ FractionOutput (values P x k t i) τ) 82 := by
  have hiB : i.val < B := i.isLt.trans (by omega)
  have hbase : Spec B (fun σ => Data P x k t σ ∧ σ.vars "build.i" = i.val ∧
      σ.vars "build.count" = (m + (n + n)) + 1) selectCoordinate
      (fun _ τ => FractionOutput (values P x k t i) τ) 82 := by
    have hselect := RamRecoveryBoundSelector.selectBound_spec B M m n k P x hk t i hM hMB hB hb hx ht
    rintro σ ⟨⟨hσA, hσb, hσx, hσm, hσn, hσk, hσt⟩, hσi, hσcount⟩
    run_vcg [hselect]
    all_goals clear hselect
    all_goals simp_all [values, Represents, arrs_setVar]
    all_goals aesop
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
    (.add (.add (.var "point.m") (.add (.var "point.n") (.var "point.n"))) (.lit 1))

def buildBound : Com := .seq prepare (RamBuildVector.build "lp.b" selectCoordinate)

set_option maxHeartbeats 1000000 in
theorem buildBound_spec (B M m n k : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ) (t : ℚ)
    (hk : k < n) (hM : 1 ≤ M) (hMB : M < B)
    (hB : m + (n + n) + 4 < B) (hb : ∀ r, Height (P.b r) M)
    (hx : ∀ j, Height (x j) M) (ht : Height t M) :
    Spec B (fun σ => Data P x k t σ ∧ Extents "lp.b" ((m + (n + n)) + 1) σ) buildBound
      (fun _ τ => Data P x k t τ ∧ Represents "lp.b"
        (List.ofFn (CoordinateOptimization.coordinateCut (LexicographicMinima.fixedPrefix P x k) ⟨k, hk⟩ t).b) τ)
      (138 * ((m + (n + n)) + 1) + 34) := by
  let N := (m + (n + n)) + 1
  have h1 : 1 < B := by omega
  have hNB : N < B := by dsimp only [N]; omega
  have hbuild := RamBuildVector.build_spec B M N 82 "lp.b" (values P x k t) selectCoordinate (Data P x k t)
    h1 hNB hMB (bound_height P x k M t hM hb hx ht)
    (selectCoordinate_spec B M m n k P x t hk · hM hMB hB hb hx ht) (by decide) (by decide)
    (by intro s hs; change "lp.b" ++ s ∉ ([] : List String); simp)
    (preserves_data B P x k t (storeReduced "lp.b")
      (by intro a ha; simp [RamRecoveryData.fields] at ha; rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by intro a ha s hs; simp [arrays] at ha; simp [RamCopy.suffixes] at hs; rcases ha with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl <;> decide))
    (preserves_data B P x k t (RamZeroArray.zeroRationalArray "lp.b")
      (by intro a ha; simp [RamRecoveryData.fields] at ha; rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by intro a ha s hs; simp [arrays] at ha; simp [RamCopy.suffixes] at hs; rcases ha with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl <;> decide))
    (fun σ z h => data_setVar P x k t σ "build.i" z (by decide) h)
    (fun σ z h => data_setVar P x k t σ "vec.i" z (by decide) h)
    (fun σ z h => data_setVar P x k t σ "vec.n" z (by decide) h)
  have hvalues : List.ofFn (values P x k t) = List.ofFn
      (CoordinateOptimization.coordinateCut (LexicographicMinima.fixedPrefix P x k) ⟨k, hk⟩ t).b := by
    congr 1
    funext i
    exact bound_eq P x k hk t i
  have hmeta : Spec B (fun σ => σ.vars "point.m" = m ∧ σ.vars "point.n" = n) prepare
      (fun _ τ => τ.vars "build.count" = N) 8 := by
    rintro σ ⟨hm, hn⟩
    run_vcg
    all_goals simp_all [N]
    all_goals omega
  rintro σ ⟨hσData, hσtarget⟩
  obtain ⟨τ, hr₁, hτcount⟩ := hmeta σ ⟨hσData.2.2.2.1, hσData.2.2.2.2.1⟩
  have hτData := data_frame hr₁ P x k t hσData
    (by intro a ha; simp [RamRecoveryData.fields] at ha; rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by intro a ha s hs; simp [Com.warrs, prepare])
  have hτtarget := RamAdvanceState.extents_of_run hr₁ "lp.b" N hσtarget
  obtain ⟨υ, hr₂, hυData, hυtarget, hυcount⟩ := hbuild τ ⟨hτData, hτtarget, hτcount⟩
  refine ⟨υ, (hr₁.seq hr₂).mono ?_, hυData, ?_⟩
  · dsimp only [N]
    norm_num only
    omega
  · simpa only [hvalues] using hυtarget

end Lax109476Proofs.RamRecoveryBound

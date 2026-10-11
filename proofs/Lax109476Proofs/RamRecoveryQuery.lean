import Lax109476Proofs.RamRecoveryMatrix
import Lax109476Proofs.RamRecoveryBound
import Lax109476Proofs.RamStoredProgram

namespace Lax109476Proofs.RamRecoveryQuery

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamRecoveryData RationalArithmeticBounds RamStoredProgram

def objective : Com := .seq (.assign "vec.n" (.var "point.n"))
  (RamZeroArray.zeroRationalArray "lp.c")

def metadata : Com := .seq
  (.assign "lp.m" (.add (.add (.var "point.m") (.add (.var "point.n") (.var "point.n"))) (.lit 1)))
  (.seq (.assign "lp.n" (.var "point.n"))
    (.assign "decode.count" (.mul (.var "lp.m") (.var "lp.n"))))

/-- Build one coordinate threshold query from the immutable point-recovery
system and its already recovered prefix. The command is independent of the
dimensions, prefix length, and rational threshold. -/
def buildQuery : Com := .seq RamRecoveryMatrix.matrix
  (.seq RamRecoveryBound.buildBound (.seq objective metadata))

def Extent (m n : ℕ) (σ : Env) : Prop :=
  Extents "lp.A" (((m + (n + n)) + 1) * n) σ ∧
    Extents "lp.b" ((m + (n + n)) + 1) σ ∧ Extents "lp.c" n σ

theorem extent_frame {B z : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ z)
    (m n : ℕ) (hσ : Extent m n σ) : Extent m n τ :=
  ⟨RamAdvanceState.extents_of_run hr _ _ hσ.1,
    RamAdvanceState.extents_of_run hr _ _ hσ.2.1,
    RamAdvanceState.extents_of_run hr _ _ hσ.2.2⟩

theorem objective_spec (B m n k : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ) (t : ℚ)
    (hn : n < B) (h1 : 1 < B) :
    Spec B (fun σ => Data P x k t σ ∧ Extents "lp.c" n σ) objective
      (fun _ τ => Data P x k t τ ∧ Represents "lp.c" (List.replicate n 0) τ)
      (33 * n + 20) := by
  have hzero := RamZeroArray.zeroRationalArray_spec B n "lp.c" hn h1
  have hbase : Spec B (fun σ => σ.vars "point.n" = n ∧ Extents "lp.c" n σ)
      objective (fun _ τ => Represents "lp.c" (List.replicate n 0) τ) (33 * n + 20) := by
    rintro σ ⟨hσn, hσc⟩
    have hs := hσc ".s" (by simp [RamCopy.suffixes])
    have hnum := hσc ".n" (by simp [RamCopy.suffixes])
    have hd := hσc ".d" (by simp [RamCopy.suffixes])
    run_vcg [hzero]
    all_goals clear hzero
    all_goals simp_all [arrs_setVar]
  rintro σ ⟨hσData, hσc⟩
  obtain ⟨τ, hr, hτ⟩ := hbase σ ⟨hσData.2.2.2.2.1, hσc⟩
  refine ⟨τ, hr, data_frame hr P x k t hσData ?_ ?_, hτ⟩
  · intro a ha
    simp [RamRecoveryData.fields] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro a ha s hs
    simp [arrays] at ha
    simp [RamCopy.suffixes] at hs
    rcases ha with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl <;> decide

theorem metadata_spec (B m n : ℕ) (hB : ((m + (n + n)) + 1) * n + m + (n + n) + 4 < B) :
    Spec B (fun σ => σ.vars "point.m" = m ∧ σ.vars "point.n" = n) metadata
      (fun _ τ => τ.vars "lp.m" = (m + (n + n)) + 1 ∧ τ.vars "lp.n" = n ∧
        τ.vars "decode.count" = ((m + (n + n)) + 1) * n) 16 := by
  rintro σ ⟨hm, hn⟩
  run_vcg
  all_goals simp_all
  all_goals omega

set_option maxHeartbeats 1000000 in
theorem buildQuery_spec (B M m n k : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ) (t : ℚ)
    (hk : k < n) (hM : 1 ≤ M) (hMB : M < B)
    (hB : ((m + (n + n)) + 1) * n + m + (n + n) + 4 < B)
    (hA : ∀ i j, Height (P.A i j) M) (hb : ∀ i, Height (P.b i) M)
    (hx : ∀ j, Height (x j) M) (ht : Height t M) (hc : ∀ j, P.c j = 0) :
    Spec B (fun σ => Data P x k t σ ∧ Extent m n σ) buildQuery
      (fun _ τ => Data P x k t τ ∧ RepresentsProgram
        (CoordinateOptimization.coordinateCut (LexicographicMinima.fixedPrefix P x k) ⟨k, hk⟩ t) τ)
      (142 * (((m + (n + n)) + 1) * n) + 138 * ((m + (n + n)) + 1) + 33 * n + 106) := by
  let C := CoordinateOptimization.coordinateCut (LexicographicMinima.fixedPrefix P x k) ⟨k, hk⟩ t
  have h1 : 1 < B := by omega
  have hn : n < B := by omega
  rintro σ ⟨hσData, hσExt⟩
  obtain ⟨τ, hr₁, hτData, hτA⟩ := RamRecoveryMatrix.matrix_spec B M m n k P x t hk hM hMB hB hA σ
    ⟨hσData, hσExt.1⟩
  have hτExt := extent_frame hr₁ m n hσExt
  obtain ⟨υ, hr₂, hυData, hυb⟩ := RamRecoveryBound.buildBound_spec B M m n k P x t hk hM hMB
    (by omega) hb hx ht τ ⟨hτData, hτExt.2.1⟩
  have hυExt := extent_frame hr₂ m n hτExt
  have hυA := RamReadBody.represents_frame "lp.A" (RamMatrixStorage.flatten C.A) hτA hr₂
    (by intro s hs; simp [RamCopy.suffixes] at hs; rcases hs with rfl | rfl | rfl <;> decide)
  obtain ⟨ρ, hr₃, hρData, hρc⟩ := objective_spec B m n k P x t hn h1 υ ⟨hυData, hυExt.2.2⟩
  have hρA := RamReadBody.represents_frame "lp.A" (RamMatrixStorage.flatten C.A) hυA hr₃
    (by intro s hs; simp [RamCopy.suffixes] at hs; rcases hs with rfl | rfl | rfl <;> decide)
  have hρb := RamReadBody.represents_frame "lp.b" (List.ofFn C.b) hυb hr₃
    (by intro s hs; simp [RamCopy.suffixes] at hs; rcases hs with rfl | rfl | rfl <;> decide)
  obtain ⟨ξ, hr₄, hξm, hξn, hξcount⟩ := metadata_spec B m n hB ρ
    ⟨hρData.2.2.2.1, hρData.2.2.2.2.1⟩
  have hξData := data_frame hr₄ P x k t hρData
    (by intro a ha; simp [RamRecoveryData.fields] at ha; rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by intro a ha s hs; simp [Com.warrs, metadata])
  have hξA := RamReadBody.represents_frame "lp.A" (RamMatrixStorage.flatten C.A) hρA hr₄
    (by intro s hs; simp [Com.warrs, metadata])
  have hξb := RamReadBody.represents_frame "lp.b" (List.ofFn C.b) hρb hr₄
    (by intro s hs; simp [Com.warrs, metadata])
  have hξc := RamReadBody.represents_frame "lp.c" (List.replicate n 0) hρc hr₄
    (by intro s hs; simp [Com.warrs, metadata])
  have hcz : List.ofFn C.c = List.replicate n 0 := by
    have he : C.c = fun _ => 0 := funext hc
    simp [he]
  refine ⟨ξ, (hr₁.seq (hr₂.seq (hr₃.seq hr₄))).mono (by omega), hξData,
    hξA, hξb, ?_, hξm, hξn, hξcount⟩
  change Represents "lp.c" (List.ofFn C.c) ξ
  simpa only [hcz] using hξc

end Lax109476Proofs.RamRecoveryQuery

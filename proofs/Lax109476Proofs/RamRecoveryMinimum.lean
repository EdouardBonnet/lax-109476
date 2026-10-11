import Lax109476Proofs.RamRecoveryThreshold
import Lax109476Proofs.RamBinaryMinimum

namespace Lax109476Proofs.RamRecoveryMinimum

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalScalars RamRationalArrays RamRecoveryThreshold RationalArithmeticBounds

def pointFields : List String := ["point.m", "point.n", "point.k"]

theorem state_frame {B z : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ z)
    {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (k : ℕ) (hσ : State P x k σ)
    (hf : ∀ a ∈ pointFields, a ∉ c.wvars)
    (ha : ∀ a ∈ RamRecoveryData.arrays, ∀ s ∈ RamCopy.suffixes, a ++ s ∉ c.warrs) :
    State P x k τ := by
  rcases hσ with ⟨hA, hb, hx, hm, hn, hk⟩
  exact ⟨RamReadBody.represents_frame _ _ hA hr (ha _ (by simp [RamRecoveryData.arrays])),
    RamReadBody.represents_frame _ _ hb hr (ha _ (by simp [RamRecoveryData.arrays])),
    RamReadBody.represents_frame _ _ hx hr (ha _ (by simp [RamRecoveryData.arrays])),
    (hr.frame_var _ (hf _ (by simp [pointFields]))).trans hm,
    (hr.frame_var _ (hf _ (by simp [pointFields]))).trans hn,
    (hr.frame_var _ (hf _ (by simp [pointFields]))).trans hk⟩

theorem persistent_frame {B z : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ z)
    {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (k : ℕ) (hσ : Persistent P x k σ)
    (hf : ∀ a ∈ pointFields, a ∉ c.wvars)
    (ha : ∀ a ∈ RamRecoveryData.arrays, ∀ s ∈ RamCopy.suffixes, a ++ s ∉ c.warrs) :
    Persistent P x k τ := ⟨state_frame hr P x k hσ.1 hf ha, workspace_frame hr _ _ hσ.2⟩

theorem persistent_setVar {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (k : ℕ)
    (σ : Env) (v : String) (z : ℕ) (hv : v ∉ pointFields) (hσ : Persistent P x k σ) :
    Persistent P x k (σ.setVar v z) := by
  have hm : v ≠ "point.m" := by intro h; subst v; simp [pointFields] at hv
  have hn : v ≠ "point.n" := by intro h; subst v; simp [pointFields] at hv
  have hk : v ≠ "point.k" := by intro h; subst v; simp [pointFields] at hv
  constructor
  · simpa [State, Represents, arrs_setVar, vars_setVar, Ne.symm hm, Ne.symm hn, Ne.symm hk] using hσ.1
  · exact hσ.2

theorem preserves_persistent (B : ℕ) {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (k : ℕ)
    (c : Com) (hf : ∀ a ∈ pointFields, a ∉ c.wvars)
    (ha : ∀ a ∈ RamRecoveryData.arrays, ∀ s ∈ RamCopy.suffixes, a ++ s ∉ c.warrs) :
    RamBisectionLoop.preserves B (Persistent P x k) c := fun hr hσ => persistent_frame hr P x k hσ hf ha

def recoverCoordinate : Com := RamBinaryMinimum.minimum decideThreshold

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
theorem recoverCoordinate_spec (S N w D M m n k : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ)
    (hk : k < n) (hB : 4 * M ^ 2 + 3 < 2 ^ w) (hKB : BinaryOptimization.steps D < 2 ^ w)
    (hM : (D + 1) * 2 ^ BinaryOptimization.steps D ≤ M) (hMS : M ≤ 2 ^ S)
    (hN : RamRationalReconstruction.depthBound S + 1 ≤ N)
    (hw : RamRationalReconstruction.wordWidth S ≤ w) (hDB : D < 2 ^ w)
    (hsize : ((m + (n + n)) + 1) * n + m + (n + n) + 4 < 2 ^ w)
    (hwQuery : RamStoredFeasibility.wordWidth (sizeBound m n (4 * M ^ 2)) ≤ w)
    (hA : ∀ i j, Height (P.A i j) M) (hb : ∀ i, Height (P.b i) M)
    (hx : ∀ j, Height (x j) M) (hc : ∀ j, P.c j = 0) :
    Spec (2 ^ w) (fun σ => Persistent P x k σ ∧ σ.vars "minimum.bound" = D ∧ (σ.arrs "cf.stack").length = N)
      recoverCoordinate (fun _ τ => Persistent P x k τ ∧ RamReconstructionRecord.Output
        (CoordinateOptimization.coordinateMinimum (LexicographicMinima.fixedPrefix P x k) ⟨k, hk⟩ D) τ)
      ((144 * M.size + 342 + instructionBound m n (4 * M ^ 2)) * BinaryOptimization.steps D +
        12 * D.size + RamRationalReconstruction.instructionBound S + 48) := by
  have hM1 : 1 ≤ M := by
    have hp : 1 ≤ 2 ^ BinaryOptimization.steps D := Nat.one_le_pow _ _ (by decide)
    nlinarith
  have hMQ : M ≤ 4 * M ^ 2 := by nlinarith
  have hquery := fun t ht => decideThreshold_spec m n k (4 * M ^ 2) w P x t hk
    (by nlinarith) (by omega) hsize hwQuery
    (fun i j => height_mono _ (hA i j) hMQ) (fun i => height_mono _ (hb i) hMQ)
    (fun j => height_mono _ (hx j) hMQ) ht hc
  apply RamBinaryMinimum.minimum_spec S N w D M (instructionBound m n (4 * M ^ 2))
    (fun t => RationalFeasibilityDecision.feasible
      (CoordinateOptimization.coordinateCut (LexicographicMinima.fixedPrefix P x k) ⟨k, hk⟩ t))
    decideThreshold (Persistent P x k) hB hKB hM hMS hN hw hDB hquery
  · intro a ha
    simp [RamBisectionLoop.fields] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · decide
  · apply preserves_persistent
    · intro a ha; simp [pointFields] at ha; rcases ha with rfl | rfl | rfl <;> decide
    · intro a ha s hs; change a ++ s ∉ ([] : List String); simp
  · apply preserves_persistent
    · intro a ha; simp [pointFields] at ha; rcases ha with rfl | rfl | rfl <;> decide
    · intro a ha s hs; change a ++ s ∉ ([] : List String); simp
  · intro σ hσ; exact persistent_setVar P x k σ "bisect.i" 0 (by decide) hσ
  · apply preserves_persistent
    · intro a ha; simp [pointFields] at ha; rcases ha with rfl | rfl | rfl <;> decide
    · intro a ha s hs; change a ++ s ∉ ([] : List String); simp
  · apply preserves_persistent
    · intro a ha; simp [pointFields] at ha; rcases ha with rfl | rfl | rfl <;> decide
    · intro a ha s hs; simp [RamRecoveryData.arrays] at ha; simp [RamCopy.suffixes] at hs;
      rcases ha with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl <;> decide

end Lax109476Proofs.RamRecoveryMinimum

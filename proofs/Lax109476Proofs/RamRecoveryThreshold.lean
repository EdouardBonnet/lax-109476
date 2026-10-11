import Lax109476Proofs.RamRecoveryQuery
import Lax109476Proofs.RamFeasibilityFlags
import Lax109476Proofs.RamStoredFeasibilityBounds
import Lax109476Proofs.RecoveryArithmeticBounds

namespace Lax109476Proofs.RamRecoveryThreshold

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamRationalScalars RamEllipsoidStep RationalArithmeticBounds

def State {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (k : ℕ) (σ : Env) : Prop :=
  Represents "point.A" (RamMatrixStorage.flatten P.A) σ ∧ Represents "point.b" (List.ofFn P.b) σ ∧
    Represents "point.x" (List.ofFn x) σ ∧ σ.vars "point.m" = m ∧ σ.vars "point.n" = n ∧
    σ.vars "point.k" = k

def Workspace (m n : ℕ) (σ : Env) : Prop :=
  RamRecoveryQuery.Extent m n σ ∧
    Extents "int.A" (((m + (n + n)) + 1) * n) σ ∧
    Extents "int.b" ((m + (n + n)) + 1) σ ∧ Extents "int.c" n σ ∧
    RamFeasibilityQuery.Workspace ((m + (n + n)) + 1) n σ

def Persistent {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (k : ℕ) (σ : Env) : Prop :=
  State P x k σ ∧ Workspace m n σ

def decideThreshold : Com := .seq RamRecoveryQuery.buildQuery RamStoredFeasibility.decideFeasible

def sizeBound (m n M : ℕ) : ℕ :=
  ((m + (n + n)) + 1) + n + 2 +
    ((((m + (n + n)) + 1) * n) + ((m + (n + n)) + 1) + n) * (4 + 2 * M.size)

def instructionBound (m n M : ℕ) : ℕ :=
  142 * (((m + (n + n)) + 1) * n) + 138 * ((m + (n + n)) + 1) + 33 * n + 106 +
    RamStoredFeasibility.instructionBound (sizeBound m n M)

theorem state_of_data {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (k : ℕ) (t : ℚ)
    (σ : Env) (h : RamRecoveryData.Data P x k t σ) : State P x k σ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

theorem data_of_state {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (k : ℕ) (t : ℚ)
    (σ : Env) (h : State P x k σ) (ht : Value "bisect.mid" t σ) :
    RamRecoveryData.Data P x k t σ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, ht⟩

theorem workspace_frame {B z : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ z)
    (m n : ℕ) (hσ : Workspace m n σ) : Workspace m n τ :=
  ⟨RamRecoveryQuery.extent_frame hr _ _ hσ.1,
    RamAdvanceState.extents_of_run hr _ _ hσ.2.1,
    RamAdvanceState.extents_of_run hr _ _ hσ.2.2.1,
    RamAdvanceState.extents_of_run hr _ _ hσ.2.2.2.1,
    RamStoredFeasibility.workspace_of_run hr _ _ hσ.2.2.2.2⟩

theorem query_size_bound {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (k M : ℕ)
    (hk : k < n) (t : ℚ) (hM : 1 ≤ M) (hA : ∀ i j, Height (P.A i j) M)
    (hb : ∀ i, Height (P.b i) M) (hx : ∀ j, Height (x j) M) (ht : Height t M)
    (hc : ∀ j, P.c j = 0) :
    bitSize (encodeProgram (CoordinateOptimization.coordinateCut
      (LexicographicMinima.fixedPrefix P x k) ⟨k, hk⟩ t)) ≤ sizeBound m n M := by
  apply RecoveryArithmeticBounds.program_height_size
  · intro i j
    rw [← RecoveryQueryEntries.entry_eq P x k hk t i j]
    exact RecoveryQueryEntries.entry_height P k M hM hA i j
  · intro i
    rw [← RecoveryQueryEntries.bound_eq P x k hk t i]
    exact RecoveryQueryEntries.bound_height P x k M t hM hb hx ht i
  · intro j
    change Height (P.c j) M
    rw [hc j]
    exact height_mono 0 height_zero (by omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
theorem decideThreshold_spec (m n k M w : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ) (t : ℚ)
    (hk : k < n) (hM : 1 ≤ M) (hMB : M < 2 ^ w)
    (hB : ((m + (n + n)) + 1) * n + m + (n + n) + 4 < 2 ^ w)
    (hw : RamStoredFeasibility.wordWidth (sizeBound m n M) ≤ w)
    (hA : ∀ i j, Height (P.A i j) M) (hb : ∀ i, Height (P.b i) M)
    (hx : ∀ j, Height (x j) M) (ht : Height t M) (hc : ∀ j, P.c j = 0) :
    Spec (2 ^ w) (fun σ => Persistent P x k σ ∧ Value "bisect.mid" t σ) decideThreshold
      (fun _ τ => Persistent P x k τ ∧ RamBisectionCommit.condition.evalB (2 ^ w) τ =
        some (RationalFeasibilityDecision.feasible
          (CoordinateOptimization.coordinateCut (LexicographicMinima.fixedPrefix P x k) ⟨k, hk⟩ t)))
      (instructionBound m n M) := by
  let C := CoordinateOptimization.coordinateCut (LexicographicMinima.fixedPrefix P x k) ⟨k, hk⟩ t
  have hsize := query_size_bound P x k M hk t hM hA hb hx ht hc
  have hwidth : RamStoredFeasibility.wordWidth (bitSize (encodeProgram C)) ≤ w :=
    (RamStoredFeasibilityBounds.wordWidth_monotone hsize).trans hw
  rintro σ ⟨⟨hσState, hσWork⟩, hσt⟩
  obtain ⟨τ, hr₁, hτData, hτC⟩ := RamRecoveryQuery.buildQuery_spec (2 ^ w) M m n k P x t hk hM hMB hB
    hA hb hx ht hc σ ⟨data_of_state P x k t σ hσState hσt, hσWork.1⟩
  have hτWork := workspace_frame hr₁ m n hσWork
  obtain ⟨υ, hr₂, hυBool⟩ := RamStoredFeasibility.decideFeasible_condition_spec _ _ C w hwidth τ
    ⟨hτC, hτWork.2.1, hτWork.2.2.1, hτWork.2.2.2.1, hτWork.2.2.2.2⟩
  have hυData := RamRecoveryData.data_frame hr₂ P x k t hτData
    (by intro a ha; simp [RamRecoveryData.fields] at ha; rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by intro a ha s hs; simp [RamRecoveryData.arrays] at ha; simp [RamCopy.suffixes] at hs;
        rcases ha with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl <;> decide)
  refine ⟨υ, (hr₁.seq hr₂).mono ?_, ⟨state_of_data P x k t υ hυData,
    workspace_frame hr₂ m n hτWork⟩, hυBool⟩
  exact Nat.add_le_add_left (RamStoredFeasibilityBounds.instructionBound_monotone hsize) _

end Lax109476Proofs.RamRecoveryThreshold

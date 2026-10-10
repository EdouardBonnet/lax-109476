import Lax109476Proofs.RamCommitState
import Lax109476Proofs.RamEllipsoidStoredBounds

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamAdvanceState

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RationalArithmeticBounds RamEllipsoidStep RamCommitState
open RamEllipsoidCoefficients RamEllipsoidWordBounds RamEllipsoidStoredBounds RamMatrixStorage

/-- Array storage has a fixed extent throughout a structured RAM run. -/
theorem array_length_of_bigStep {c : Com} {σ τ : Env} {K : ℕ}
    (hr : BigStep c σ τ K) (b : String) : (τ.arrs b).length = (σ.arrs b).length := by
  induction hr with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => exact length_arrs_setArr _ _ _ _ _
  | seq _ _ ih ih' => exact ih'.trans ih
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => exact ih'.trans ih
  | while_false _ => rfl
  | read _ => rfl
  | write _ => rfl

theorem extents_of_run {B K : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ K)
    (b : String) (n : ℕ) (hσ : Extents b n σ) : Extents b n τ := by
  obtain ⟨_, _, hstep⟩ := hr.bigStep
  intro s hs
  rw [array_length_of_bigStep hstep]
  exact hσ s hs

theorem workspace_of_run {B K : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ K)
    (n : ℕ) (hσ : Workspace n σ) : Workspace n τ :=
  ⟨extents_of_run hr _ _ hσ.1, extents_of_run hr _ _ hσ.2.1,
    extents_of_run hr _ _ hσ.2.2.1, extents_of_run hr _ _ hσ.2.2.2⟩

theorem represents_extents (b : String) (xs : List ℚ) (σ : Env)
    (h : Represents b xs σ) : Extents b xs.length σ := by
  intro s hs
  simp at hs
  rcases hs with rfl | rfl | rfl <;> simp [h.1, h.2.1, h.2.2]

/-- A complete central cut, installation of the next state, and counter advance. -/
def advanceState : Com := .seq ellipsoidStep
  (.seq commitState (.assign "iter.k" (.add (.var "iter.k") (.lit 1))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
theorem advanceState_spec (B n H M k : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ)
    (hn : 2 ≤ n) (hH : 1 ≤ H) (hA : ∀ i j, Height (A i j) H)
    (ha : ∀ i, Height (a i) H) (hc : ∀ i, Height (c i) H)
    (hqpos : 0 < a ⬝ᵥ (A *ᵥ a)) (hnM : n * n ≤ M)
    (hFM : RamEllipsoidForm.formHeight n H ≤ M)
    (hDM : 2 ^ (2 * k + 3 * n + 9) ≤ M) (hEM : 2 ^ (2 * n + 4) ≤ M)
    (hB : 2 * (RamShapeCoordinate.shapeCap (coefficientCap M)) ^ 2 + 3 < B) :
    Spec B (fun σ => Represents "ell.shape" (flatten A) σ ∧ Represents "ell.normal" (List.ofFn a) σ ∧
        Represents "ell.center" (List.ofFn c) σ ∧ Workspace n σ ∧
        σ.vars "vec.n" = n ∧ σ.vars "iter.k" = k)
      advanceState
      (fun _ τ => Represents "ell.center"
          (List.ofFn (EllipsoidCenter.roundedCenter n A a c (2 ^ (2 * k + 3 * n + 9)))) τ ∧
        Represents "ell.shape"
          (flatten (EllipsoidCenter.roundedStepShape n A a (2 ^ (2 * k + 3 * n + 9))
            (EllipsoidIteration.stepAccuracy n))) τ ∧
        Workspace n τ ∧ τ.vars "vec.n" = n ∧ τ.vars "iter.k" = k + 1)
      (stepCost n H M + 71 * n + 71 * (n * n) + 60) := by
  let S := RamShapeCoordinate.shapeCap (coefficientCap M)
  let A' := EllipsoidCenter.roundedStepShape n A a (2 ^ (2 * k + 3 * n + 9))
    (EllipsoidIteration.stepAccuracy n)
  let c' := EllipsoidCenter.roundedCenter n A a c (2 ^ (2 * k + 3 * n + 9))
  have bounds := unified_word_bounds B M n hn hnM hB
  have h1 : 1 < B := by omega
  have hnB : n < B := bounds.2.2.2.1
  have hnnB : n * n < B := by simpa only [pow_two] using bounds.2.2.1
  have hnM' : n ≤ M := (Nat.le_mul_self n).trans hnM
  have hSpos : 1 ≤ S := by
    have hp : 1 ≤ (coefficientCap M + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
    dsimp [S, RamShapeCoordinate.shapeCap]
    omega
  have hSS : S ≤ S ^ 2 := le_self_pow hSpos (by decide : (2 : ℕ) ≠ 0)
  have hSB : S < B := by change 2 * S ^ 2 + 3 < B at hB; omega
  have hkB : k + 1 < B := by
    have hp : 2 * k + 3 * n + 9 < 2 ^ (2 * k + 3 * n + 9) := Nat.lt_two_pow_self
    have hMB : M < B := bounds.2.1
    omega
  have hnew := step_stored_bounds n H M k A a c hH hA ha hc hnM' hFM hDM hEM
  rintro σ ⟨hσA, hσa, hσc, hσw, hσn, hσk⟩
  obtain ⟨τ, hr₁, hτc, hτA, hτoldA, hτoldc, hτn, _⟩ :=
    ellipsoidStep_spec B n H M k A a c hn hH hA ha hc hqpos hnM hFM hDM hEM hB
      σ ⟨hσA, hσa, hσc, hσw, hσn, hσk⟩
  have hτk : τ.vars "iter.k" = k := (hr₁.frame_var _ (by decide)).trans hσk
  have hτcExt : Extents "ell.center" n τ := by simpa using represents_extents _ _ _ hτoldc
  have hτAExt : Extents "ell.shape" (n * n) τ := by
    simpa [flatten] using represents_extents _ _ _ hτoldA
  obtain ⟨υ, hr₂, hυA, hυc, _, _, hυn⟩ := commitState_spec B n S A' c' h1 hnB hnnB hSB
    hnew.2 hnew.1 τ ⟨hτA, hτc, hτcExt, hτAExt, hτn⟩
  have hυk : υ.vars "iter.k" = k := (hr₂.frame_var _ (by decide)).trans hτk
  have haddB : Bop.add.apply (υ.vars "iter.k") 1 < B := by simpa [Bop.apply, hυk] using hkB
  have hi : Run B (.assign "iter.k" (.add (.var "iter.k") (.lit 1))) υ
      (υ.setVar "iter.k" (k + 1)) 4 := by
    exact Run.assign (by simpa [Bop.apply, hυk] using
      (evalB_bin (evalB_var (by omega : υ.vars "iter.k" < B)) (evalB_lit h1)
        haddB))
  have hrun := hr₁.seq (hr₂.seq hi)
  refine ⟨_, hrun.mono (by omega), ?_, ?_, workspace_of_run hrun n hσw, ?_, ?_⟩
  · simpa only [Represents, arrs_setVar] using hυc
  · simpa only [Represents, arrs_setVar] using hυA
  · simpa using hυn
  · simp

end Lax109476Proofs.RamAdvanceState

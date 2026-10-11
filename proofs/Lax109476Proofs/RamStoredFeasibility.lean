import Lax109476Proofs.RamRationalFeasibility
import Lax109476Proofs.RamProgramSize

namespace Lax109476Proofs.RamStoredFeasibility

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamStoredProgram RamClearProgram RamEllipsoidStep RationalArithmeticBounds IntegerEncoding

def decideFeasible : Com := .seq RamProgramSize.prepareSize
  (.seq RamProgramDenominator.prepareDenominator
    (.seq clearProgram RamRationalFeasibility.decideFeasible))

def Input {m n : ℕ} (P : Program ℚ m n) (σ : Env) : Prop :=
  RepresentsProgram P σ ∧ Extents "int.A" (m * n) σ ∧ Extents "int.b" m σ ∧
    Extents "int.c" n σ ∧ RamFeasibilityQuery.Workspace m n σ

def wordWidth (L : ℕ) : ℕ := RamDecoder.wordWidth L + RamRationalFeasibility.wordWidth L

def instructionBound (L : ℕ) : ℕ :=
  (36 * (L + 1) + 61) * L + 24 * L + 56 + 13 * L + 26 +
    (72 * (L + 1) + 135) * L + 80 + RamRationalFeasibility.instructionBound L

theorem workspace_of_run {B K : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ K)
    (m n : ℕ) (h : RamFeasibilityQuery.Workspace m n σ) : RamFeasibilityQuery.Workspace m n τ := by
  rcases h with ⟨hqA, hqb, hpA, hpb, hrows, hrhs, hcenter, hshape, hw, hnormal⟩
  exact ⟨RamAdvanceState.extents_of_run hr _ _ hqA, RamAdvanceState.extents_of_run hr _ _ hqb,
    RamAdvanceState.extents_of_run hr _ _ hpA, RamAdvanceState.extents_of_run hr _ _ hpb,
    RamAdvanceState.extents_of_run hr _ _ hrows, RamAdvanceState.extents_of_run hr _ _ hrhs,
    RamAdvanceState.extents_of_run hr _ _ hcenter, RamAdvanceState.extents_of_run hr _ _ hshape,
    RamAdvanceState.workspace_of_run hr _ hw, RamAdvanceState.extents_of_run hr _ _ hnormal⟩

/-- Feasibility of an auxiliary rational program is computed from its stored
coefficients. Its denominator and precision parameters are recomputed by RAM
instructions on each call. -/
theorem decideFeasible_spec (m n : ℕ) (P : Program ℚ m n) (w : ℕ)
    (hw : wordWidth (bitSize (encodeProgram P)) ≤ w) :
    Spec (2 ^ w) (Input P) decideFeasible
      (fun _ τ => decide (τ.vars "search.found" = 1) = RationalFeasibilityDecision.feasible P)
      (instructionBound (bitSize (encodeProgram P))) := by
  let L := bitSize (encodeProgram P)
  let H := 2 ^ L
  have hwFront : RamDecoder.wordWidth L ≤ w := by dsimp only [L]; unfold wordWidth at hw; omega
  have hwFeas : RamRationalFeasibility.wordWidth L ≤ w := by dsimp only [L]; unfold wordWidth at hw; omega
  have hH : 1 ≤ H := Nat.one_le_pow L 2 (by decide)
  have hHB : H < 2 ^ w := Nat.pow_lt_pow_right (by decide)
    (by unfold RamDecoder.wordWidth at hwFront; omega)
  have hLB : L < 2 ^ w := (Nat.lt_two_pow_self (n := L)).trans hHB
  have hcells := RamSolverInitialization.cells_bound P
  have hmB : m < 2 ^ w := (by omega : m ≤ L).trans_lt hLB
  have hnB : n < 2 ^ w := (by omega : n ≤ L).trans_lt hLB
  have hmnB : m * n < 2 ^ w := (by omega : m * n ≤ L).trans_lt hLB
  have hms : m.size ≤ L := (RationalSizeBounds.size_le_self m).trans (by omega)
  have hns : n.size ≤ L := (RationalSizeBounds.size_le_self n).trans (by omega)
  have h2 : 2 < 2 ^ w := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) (show 2 ≤ w by unfold RamDecoder.wordWidth at hwFront; omega)
    norm_num at this; omega
  have hA : ∀ i j, Height (P.A i j) H := fun i j => RamSolverInitialization.datum_height P (.inl (i, j))
  have hb : ∀ i, Height (P.b i) H := fun i => RamSolverInitialization.datum_height P (.inr (.inl i))
  have hc : ∀ j, Height (P.c j) H := fun j => RamSolverInitialization.datum_height P (.inr (.inr j))
  have hD : programDenominator P ≤ H := programDenominator_bound P
  have hB := RamSolverFrontEnd.clearing_word_guard L w hwFront
  rintro σ ⟨hσP, hσA, hσb, hσc, hσW⟩
  obtain ⟨τ, hr₁, hτbits, hτP, hτarrs⟩ := RamProgramSize.prepareSize_spec (2 ^ w) H m n P
    h2 hH hHB hmB hnB hmnB hA hb hc hLB σ hσP
  obtain ⟨υ, hr₂, hυD, hυP, hυarrs⟩ := RamProgramDenominator.prepareDenominator_spec (2 ^ w) m n P
    (by omega) hmB hnB hmnB (hD.trans_lt hHB) τ hτP
  have hrPre := hr₁.seq hr₂
  have hυA := RamAdvanceState.extents_of_run hrPre "int.A" (m * n) hσA
  have hυb := RamAdvanceState.extents_of_run hrPre "int.b" m hσb
  have hυc := RamAdvanceState.extents_of_run hrPre "int.c" n hσc
  obtain ⟨ρ, hr₃, hρI, hρP, hρD, hρbits⟩ := clearProgram_spec (2 ^ w) H m n P
    hH hmB hnB hmnB hB hA hb hc hD υ ⟨hυP, hυA, hυb, hυc, hυD⟩
  have hυbits : υ.vars "input.bits" = L := (hr₂.frame_var _ (by decide)).trans hτbits
  have hρW := workspace_of_run (hrPre.seq hr₃) m n hσW
  obtain ⟨ξ, hr₄, hξ⟩ := RamRationalFeasibility.decideFeasible_spec m n P w hwFeas ρ
    ⟨hρI, hρW, hρP.2.2.2.1, hρP.2.2.2.2.1, hρP.2.2.2.2.2, hρbits.trans hυbits⟩
  have hcount := Nat.mul_le_mul_left (36 * (L + 1) + 61) hcells
  have hden := Nat.mul_le_mul_left 13 hcells
  have hclear := Nat.mul_le_mul_left (72 * (L + 1) + 135) hcells
  refine ⟨ξ, (hr₁.seq (hr₂.seq (hr₃.seq hr₄))).mono ?_, hξ⟩
  dsimp only [instructionBound, H]
  rw [Nat.size_pow]
  dsimp only [L] at hcount hden hclear hms hns ⊢
  omega

end Lax109476Proofs.RamStoredFeasibility

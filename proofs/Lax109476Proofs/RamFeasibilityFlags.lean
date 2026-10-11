import Lax109476Proofs.RamStoredFeasibility

namespace Lax109476Proofs.RamIntegerFeasibility

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NormalizedFeasibility IntegerCertificates EllipsoidSequence EllipsoidSearch RamNormalizedBounds

theorem decideFeasible_with_flag_spec (m n S w : ℕ) (P : Program ℤ m n) (hn : 2 ≤ n)
    (hdim : m + n ≤ S) (hA : ∀ i j, (P.A i j).natAbs ≤ 2 ^ (2 * S))
    (hb : ∀ i, (P.b i).natAbs ≤ 2 ^ (2 * S)) (hw : wordWidth S ≤ w) :
    Spec (2 ^ w) (RamFeasibilitySetup.Input P S) decideFeasible
      (fun _ τ => τ.vars "search.found" ≤ 1 ∧ decide (τ.vars "search.found" = 1) = IntegerFeasibilityDecision.feasible P (2 ^ (2 * S)))
      (instructionBound m n S) := by
  have hwSetup : RamFeasibilitySetup.wordWidth S ≤ w := by unfold wordWidth at hw; omega
  have hwSearch := search_width_bound m n S w hdim hw
  have hbounds := normalized_bounds m n S P hdim hA hb
  let H := 2 ^ (2 * S)
  let A := normalizedMatrix P (outerScale n (coordinateCap m n H))
  let b := normalizedBound P (1 / (precisionDenominator m n H : ℚ))
  let K := thresholdSteps n (ballExponent m n H)
  intro σ hσ
  obtain ⟨τ, hr₁, hτ⟩ := RamFeasibilitySetup.setup_spec m n S w P hdim hA hb hwSetup σ hσ
  obtain ⟨υ, hr₂, hυ, hfind⟩ := RamSearchBounds.search_bounded_spec A b hn (K + 1) (coefficientBits S) w
    hbounds.1 hbounds.2 hwSearch τ hτ
  have he : findIteration A b K = if υ.vars "search.found" = 1 then some (υ.vars "iter.k") else none := by
    change scanStates A b 0 (K + 1) (trajectory A b 0) = _
    rw [scanStates_eq_findFirst]
    exact hfind
  refine ⟨υ, (hr₁.seq hr₂).mono (by dsimp only [instructionBound, K, H]; omega), ?_, ?_⟩
  · rcases hυ with ⟨k, hk, hstate, hprior, hstatus⟩
    rcases hstatus with h | h <;> omega
  · have hi := congrArg Option.isSome he
    change decide (υ.vars "search.found" = 1) = (findIteration A b K).isSome
    rw [hi]
    split_ifs <;> simp_all


end Lax109476Proofs.RamIntegerFeasibility

namespace Lax109476Proofs.RamPaddedFeasibility

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamMatrixStorage IntegerEncoding RationalArithmeticBounds

theorem decideFeasible_with_flag_spec (m n S w : ℕ) (P : Program ℤ m n) (hdim : m + n ≤ S)
    (hA : ∀ i j, (P.A i j).natAbs ≤ 2 ^ (2 * S))
    (hb : ∀ i, (P.b i).natAbs ≤ 2 ^ (2 * S)) (hw : wordWidth S ≤ w) :
    Spec (2 ^ w) (Input P S) decideFeasible
      (fun _ τ => τ.vars "search.found" ≤ 1 ∧ decide (τ.vars "search.found" = 1) = FeasibilityPadding.feasible P (2 ^ (2 * (S + 4))))
      (instructionBound S) := by
  let H := 2 ^ (2 * S)
  have hH : 1 ≤ H := Nat.one_le_pow _ _ (by decide)
  have hwInt : RamIntegerFeasibility.wordWidth (S + 4) ≤ w := by unfold wordWidth at hw; omega
  have hwDec : RamDecoder.wordWidth (2 * S) ≤ w := by unfold wordWidth at hw; omega
  have hHB : H < 2 ^ w := Nat.pow_lt_pow_right (by decide)
    (by unfold RamDecoder.wordWidth at hwDec; omega)
  have hdims : (m + 2) * (n + 2) + m + n + 4 < 2 ^ w := by
    have hmn : (m + 2) * (n + 2) ≤ (S + 4) ^ 2 := by
      have h := Nat.mul_le_mul (show m + 2 ≤ S + 4 by omega) (show n + 2 ≤ S + 4 by omega)
      simpa only [pow_two] using h
    have hh := (Nat.lt_two_pow_self (n := (S + 4) ^ 2 + S + 5)).trans_le
      (Nat.pow_le_pow_right (by decide) (show (S + 4) ^ 2 + S + 5 ≤ w by unfold wordWidth at hw; omega))
    omega
  have hSB : S + 4 < 2 ^ w :=
    (Nat.lt_two_pow_self (n := S + 4)).trans_le
      (Nat.pow_le_pow_right (by decide) (by unfold wordWidth at hw; omega))
  have hAH : ∀ i j, Height ((rationalProgram P).A i j) H := by
    intro i j
    simpa [Height, rationalProgram, H] using And.intro (hA i j) hH
  have hbH : ∀ i, Height ((rationalProgram P).b i) H := by
    intro i
    simpa [Height, rationalProgram, H] using And.intro (hb i) hH
  have hlarge : H ≤ 2 ^ (2 * (S + 4)) := Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨hpadA, hpadb⟩ := FeasibilityPadding.padded_bounds P H hH hA hb
  rintro σ ⟨hσpad, hσrows, hσrhs, hσcenter, hσshape, hσworkspace, hσnormal⟩
  obtain ⟨τ, hr₁, hτA, hτb, hτsourceA, hτsourceb, hτm, hτn, hτbits⟩ :=
    RamQueryPadding.padQuery_spec (2 ^ w) H m n S (rationalProgram P)
      hH hHB hdims hSB hAH hbH σ hσpad
  have hτinput : RamFeasibilitySetup.Input (FeasibilityPadding.pad P) (S + 4) τ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hτm, hτn, hτbits⟩
    · simpa only [rationalProgram_pad] using hτA
    · simpa only [rationalProgram_pad] using hτb
    · exact RamAdvanceState.extents_of_run hr₁ _ _ hσrows
    · exact RamAdvanceState.extents_of_run hr₁ _ _ hσrhs
    · exact RamAdvanceState.extents_of_run hr₁ _ _ hσcenter
    · exact RamAdvanceState.extents_of_run hr₁ _ _ hσshape
    · exact RamAdvanceState.workspace_of_run hr₁ _ hσworkspace
    · exact RamAdvanceState.extents_of_run hr₁ _ _ hσnormal
  obtain ⟨υ, hr₂, hυ⟩ := RamIntegerFeasibility.decideFeasible_with_flag_spec (m + 2) (n + 2) (S + 4) w
    (FeasibilityPadding.pad P) (by omega) (by omega)
    (fun i j => (hpadA i j).trans hlarge) (fun i => (hpadb i).trans hlarge) hwInt τ hτinput
  have hr₂ := hr₂.mono (RamIntegerFeasibility.instructionBound_le (m + 2) (n + 2) (S + 4) (by omega))
  have hprod : (m + 2) * (n + 2) ≤ (S + 4) ^ 2 := by
    have h := Nat.mul_le_mul (show m + 2 ≤ S + 4 by omega) (show n + 2 ≤ S + 4 by omega)
    simpa only [pow_two] using h
  have hm := Nat.mul_le_mul_left 111 hprod
  have hbcount := Nat.mul_le_mul_left 77 (show m + 2 ≤ S + 4 by omega)
  exact ⟨υ, (hr₁.seq hr₂).mono (by unfold instructionBound; omega), hυ⟩


end Lax109476Proofs.RamPaddedFeasibility

namespace Lax109476Proofs.RamRationalFeasibility

open Lax109476.LinearProgram Lax109476.RationalEncoding Lax109476.RationalCertificates
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep IntegerEncoding

theorem decideFeasible_with_flag_spec (m n : ℕ) (P : Program ℚ m n) (w : ℕ)
    (hw : wordWidth (bitSize (encodeProgram P)) ≤ w) :
    Spec (2 ^ w) (RamFeasibilityQuery.Input P) decideFeasible
      (fun _ τ => τ.vars "search.found" ≤ 1 ∧ decide (τ.vars "search.found" = 1) = RationalFeasibilityDecision.feasible P)
      (instructionBound (bitSize (encodeProgram P))) := by
  let L := bitSize (encodeProgram P)
  have hwCopy : RamDecoder.wordWidth (2 * L) ≤ w := by dsimp only [L]; unfold wordWidth at hw; omega
  have hwFeas : RamPaddedFeasibility.wordWidth L ≤ w := by dsimp only [L]; unfold wordWidth at hw; omega
  have hdim := EncodingSize.dimension_bound P
  obtain ⟨hA, hb, hc⟩ := integerProgram_bounds P
  intro σ hσ
  obtain ⟨τ, hr₁, hτ⟩ := RamFeasibilityQuery.copyInput_spec m n P w hwCopy σ hσ
  obtain ⟨υ, hr₂, hυ⟩ := RamPaddedFeasibility.decideFeasible_with_flag_spec m n L w (integerProgram P)
    hdim hA hb hwFeas τ hτ
  have hcells := RamSolverInitialization.cells_bound P
  have hcost := Nat.mul_le_mul_left 71 (show m * n + m ≤ L by omega)
  exact ⟨υ, (hr₁.seq hr₂).mono (by dsimp only [instructionBound, L]; dsimp only [L] at hcost; omega), hυ⟩


end Lax109476Proofs.RamRationalFeasibility

namespace Lax109476Proofs.RamStoredFeasibility

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamStoredProgram RamClearProgram RamEllipsoidStep RationalArithmeticBounds IntegerEncoding

theorem decideFeasible_with_flag_spec (m n : ℕ) (P : Program ℚ m n) (w : ℕ)
    (hw : wordWidth (bitSize (encodeProgram P)) ≤ w) :
    Spec (2 ^ w) (Input P) decideFeasible
      (fun _ τ => τ.vars "search.found" ≤ 1 ∧ decide (τ.vars "search.found" = 1) = RationalFeasibilityDecision.feasible P)
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
  obtain ⟨ξ, hr₄, hξ⟩ := RamRationalFeasibility.decideFeasible_with_flag_spec m n P w hwFeas ρ
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

namespace Lax109476Proofs.RamStoredFeasibility

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem decideFeasible_condition_spec (m n : ℕ) (P : Program ℚ m n) (w : ℕ)
    (hw : wordWidth (bitSize (encodeProgram P)) ≤ w) :
    Spec (2 ^ w) (Input P) decideFeasible
      (fun _ τ => (Cond.eq (.var "search.found") (.lit 1)).evalB (2 ^ w) τ =
        some (RationalFeasibilityDecision.feasible P))
      (instructionBound (bitSize (encodeProgram P))) := by
  have h1 : 1 < 2 ^ w := by
    have hwD : RamDecoder.wordWidth (bitSize (encodeProgram P)) ≤ w := by unfold wordWidth at hw; omega
    have hp := Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ w by unfold RamDecoder.wordWidth at hwD; omega)
    norm_num at hp; omega
  refine (decideFeasible_with_flag_spec m n P w hw).post ?_
  rintro σ τ _ ⟨hflag, hvalue⟩
  have he := evalB_condEq (evalB_var (B := 2 ^ w) (σ := τ) (x := "search.found")
    (hflag.trans_lt h1)) (evalB_lit h1)
  simpa only [Bool.beq_eq_decide_eq, hvalue] using he

end Lax109476Proofs.RamStoredFeasibility

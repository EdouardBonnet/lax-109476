import Lax109476Proofs.RamFeasibilitySetup
import Lax109476Proofs.IntegerFeasibilityDecision

namespace Lax109476Proofs.RamIntegerFeasibility

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NormalizedFeasibility IntegerCertificates EllipsoidSequence EllipsoidSearch RamNormalizedBounds

def iterationBound (S : ℕ) : ℕ := 1024 * (S + 1) ^ 4 + 1

def wordWidth (S : ℕ) : ℕ := RamFeasibilitySetup.wordWidth S +
  RamSearchBounds.wordWidth S S (iterationBound S) (coefficientBits S)

def decideFeasible : Com := .seq RamFeasibilitySetup.setup RamSearchLoop.search

def instructionBound (m n S : ℕ) : ℕ := RamFeasibilitySetup.instructionBound S +
  RamSearchBounds.instructionBound (m + n) n
    (thresholdSteps n (ballExponent m n (2 ^ (2 * S))) + 1) (coefficientBits S)

theorem search_width_bound (m n S w : ℕ) (hdim : m + n ≤ S) (hw : wordWidth S ≤ w) :
    RamSearchBounds.wordWidth (m + n) n
      (thresholdSteps n (ballExponent m n (2 ^ (2 * S))) + 1) (coefficientBits S) ≤ w := by
  let N := thresholdSteps n (ballExponent m n (2 ^ (2 * S))) + 1
  have hN : N ≤ iterationBound S := by
    have h := IterationBudget.thresholdSteps_polynomial m n S hdim
    dsimp [N, iterationBound]
    omega
  have hn : n ≤ S := by omega
  have hstate : RamTrajectoryBounds.stateBits n N (coefficientBits S) ≤
      RamTrajectoryBounds.stateBits S (iterationBound S) (coefficientBits S) := by
    unfold RamTrajectoryBounds.stateBits
    omega
  have hc := RamEllipsoidBitBounds.wordWidth_monotone hn hstate hN
  have hprod := Nat.mul_le_mul hdim hn
  unfold wordWidth RamSearchBounds.wordWidth at hw
  unfold RamSearchBounds.wordWidth
  dsimp only [N] at hc hN
  omega

theorem search_cost_monotone {m n N l m' n' N' l' : ℕ}
    (hm : m ≤ m') (hn : n ≤ n') (hN : N ≤ N') (hl : l ≤ l') :
    RamSearchBounds.instructionBound m n N l ≤ RamSearchBounds.instructionBound m' n' N' l' := by
  unfold RamSearchBounds.instructionBound RamSearchBounds.stepBound RamSearchBounds.rowBound
    RamTrajectoryBounds.instructionBound RamTrajectoryBounds.stateBits
    RamEllipsoidBitBounds.magnitudeExponent RamEllipsoidBitBounds.formExponent
  dsimp only
  gcongr

def uniformInstructionBound (S : ℕ) : ℕ := RamFeasibilitySetup.instructionBound S +
  RamSearchBounds.instructionBound S S (iterationBound S) (coefficientBits S)

theorem instructionBound_le (m n S : ℕ) (hdim : m + n ≤ S) :
    instructionBound m n S ≤ uniformInstructionBound S := by
  have hN := IterationBudget.thresholdSteps_polynomial m n S hdim
  apply Nat.add_le_add_left
  exact search_cost_monotone hdim (by omega) (by unfold iterationBound; omega) le_rfl

theorem decideFeasible_spec (m n S w : ℕ) (P : Program ℤ m n) (hn : 2 ≤ n)
    (hdim : m + n ≤ S) (hA : ∀ i j, (P.A i j).natAbs ≤ 2 ^ (2 * S))
    (hb : ∀ i, (P.b i).natAbs ≤ 2 ^ (2 * S)) (hw : wordWidth S ≤ w) :
    Spec (2 ^ w) (RamFeasibilitySetup.Input P S) decideFeasible
      (fun _ τ => decide (τ.vars "search.found" = 1) = IntegerFeasibilityDecision.feasible P (2 ^ (2 * S)))
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
  refine ⟨υ, (hr₁.seq hr₂).mono (by dsimp only [instructionBound, K, H]; omega), ?_⟩
  have hi := congrArg Option.isSome he
  change decide (υ.vars "search.found" = 1) = (findIteration A b K).isSome
  rw [hi]
  split_ifs <;> simp_all

theorem decideFeasible_correct_spec (m n S w : ℕ) (P : Program ℤ m n) (hn : 2 ≤ n)
    (hdim : m + n ≤ S) (hA : ∀ i j, (P.A i j).natAbs ≤ 2 ^ (2 * S))
    (hb : ∀ i, (P.b i).natAbs ≤ 2 ^ (2 * S)) (hw : wordWidth S ≤ w) :
    Spec (2 ^ w) (RamFeasibilitySetup.Input P S) decideFeasible
      (fun _ τ => (τ.vars "search.found" = 1 ↔ IsFeasible (toReal (IntegerEncoding.rationalProgram P))))
      (instructionBound m n S) := by
  refine (decideFeasible_spec m n S w P hn hdim hA hb hw).post ?_
  intro σ τ _ hτ
  have hcorrect := IntegerFeasibilityDecision.feasible_correct P (2 ^ (2 * S)) hn
    (Nat.one_le_pow _ _ (by decide)) hA hb
  rw [← hτ, decide_eq_true_eq] at hcorrect
  exact hcorrect

theorem decideFeasible_uniform_spec (m n S w : ℕ) (P : Program ℤ m n) (hn : 2 ≤ n)
    (hdim : m + n ≤ S) (hA : ∀ i j, (P.A i j).natAbs ≤ 2 ^ (2 * S))
    (hb : ∀ i, (P.b i).natAbs ≤ 2 ^ (2 * S)) (hw : wordWidth S ≤ w) :
    Spec (2 ^ w) (RamFeasibilitySetup.Input P S) decideFeasible
      (fun _ τ => decide (τ.vars "search.found" = 1) = IntegerFeasibilityDecision.feasible P (2 ^ (2 * S)))
      (uniformInstructionBound S) :=
  (decideFeasible_spec m n S w P hn hdim hA hb hw).mono (instructionBound_le m n S hdim)

end Lax109476Proofs.RamIntegerFeasibility

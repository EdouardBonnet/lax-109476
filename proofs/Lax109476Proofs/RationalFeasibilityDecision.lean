import Lax109476Proofs.FeasibilityPadding
import Lax109476Proofs.IterationBudget

open scoped BigOperators

namespace Lax109476Proofs.RationalFeasibilityDecision

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open IntegerEncoding EncodingSize NormalizedFeasibility EllipsoidSequence IterationBudget

theorem scaled_real_feasible_iff {m n : ℕ} (P : Program ℚ m n) (s : ℚ)
    (hs : 0 < s) (x : Fin n → ℝ) :
    PrimalFeasible (toReal (scaledProgram P s)) x ↔ PrimalFeasible (toReal P) x := by
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hrow : ∀ i, rowValue (toReal (scaledProgram P s)) x i =
      (s : ℝ) * rowValue (toReal P) x i := by
    intro i
    simp only [rowValue, toReal, scaledProgram, Rat.cast_mul, Finset.mul_sum, mul_assoc]
  constructor
  · rintro ⟨hxpos, hxrows⟩
    refine ⟨hxpos, ?_⟩
    intro i
    have h := hxrows i
    rw [hrow] at h
    have hi : (s : ℝ) * rowValue (toReal P) x i ≤ (s : ℝ) * (P.b i : ℝ) := by
      simpa [toReal, scaledProgram] using h
    exact (mul_le_mul_iff_of_pos_left hsR).mp hi
  · rintro ⟨hxpos, hxrows⟩
    refine ⟨hxpos, ?_⟩
    intro i
    rw [hrow]
    simpa [toReal, scaledProgram] using (mul_le_mul_iff_of_pos_left hsR).mpr (hxrows i)

theorem integerProgram_feasible_iff {m n : ℕ} (P : Program ℚ m n) :
    IsFeasible (toReal (rationalProgram (integerProgram P))) ↔ IsFeasible (toReal P) := by
  rw [integerProgram_eq_scaled]
  have hs : 0 < (programDenominator P : ℚ) := by
    exact_mod_cast RationalSizeBounds.commonDenominator_pos (programData P)
  exact exists_congr (fun x => scaled_real_feasible_iff P _ hs x)

def sizeParameter {m n : ℕ} (P : Program ℚ m n) : ℕ := bitSize (encodeProgram P) + 4

/-- Total, computable feasibility decision by exact rational ellipsoid updates.
Its mathematical correctness does not assert a RAM execution theorem. -/
def feasible {m n : ℕ} (P : Program ℚ m n) : Bool :=
  FeasibilityPadding.feasible (integerProgram P) (2 ^ (2 * sizeParameter P))

theorem coefficient_bounds {m n : ℕ} (P : Program ℚ m n) :
    (∀ i j, ((integerProgram P).A i j).natAbs ≤ 2 ^ (2 * sizeParameter P)) ∧
      (∀ i, ((integerProgram P).b i).natAbs ≤ 2 ^ (2 * sizeParameter P)) := by
  obtain ⟨hA, hb, _⟩ := integerProgram_bounds P
  have hp : 2 ^ (2 * bitSize (encodeProgram P)) ≤ 2 ^ (2 * sizeParameter P) :=
    Nat.pow_le_pow_right (by decide) (by unfold sizeParameter; omega)
  exact ⟨fun i j => (hA i j).trans hp, fun i => (hb i).trans hp⟩

/-- No feasibility or dimension promise is needed by the rational decision. -/
theorem feasible_correct {m n : ℕ} (P : Program ℚ m n) :
    feasible P = true ↔ IsFeasible (toReal P) := by
  obtain ⟨hA, hb⟩ := coefficient_bounds P
  have hH : 1 ≤ 2 ^ (2 * sizeParameter P) := by
    have hp : 0 < 2 ^ (2 * sizeParameter P) := by positivity
    omega
  rw [feasible, FeasibilityPadding.feasible_correct _ _ hH hA hb,
    integerProgram_feasible_iff]

/-- Even after padding, the exact rational decision's central-cut budget is
bounded by a universal polynomial in the registered input encoding size. -/
theorem iteration_budget {m n : ℕ} (P : Program ℚ m n) :
    thresholdSteps (n + 2) (ballExponent (m + 2) (n + 2) (2 ^ (2 * sizeParameter P))) ≤
      640000 * (bitSize (encodeProgram P) + 1) ^ 4 := by
  have hdim : (m + 2) + (n + 2) ≤ sizeParameter P := by
    have h := dimension_bound P
    unfold sizeParameter
    omega
  calc
    _ ≤ 1024 * (sizeParameter P + 1) ^ 4 :=
      thresholdSteps_polynomial (m + 2) (n + 2) (sizeParameter P) hdim
    _ ≤ 1024 * (5 * (bitSize (encodeProgram P) + 1)) ^ 4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by unfold sizeParameter; omega) _)
    _ = _ := by rw [Nat.mul_pow]; norm_num; ring

end Lax109476Proofs.RationalFeasibilityDecision

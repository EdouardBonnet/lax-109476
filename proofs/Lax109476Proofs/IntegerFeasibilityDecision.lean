import Lax109476Proofs.NormalizedFeasibility

open scoped BigOperators Matrix

namespace Lax109476Proofs.IntegerFeasibilityDecision

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding IntegerCertificates Relaxation NormalizedFeasibility
open EllipsoidSearch EllipsoidSequence

def iterationResult {m n : ℕ} (P : Program ℤ m n) (H : ℕ) : Option ℕ :=
  findIteration (normalizedMatrix P (outerScale n (coordinateCap m n H)))
    (normalizedBound P (1 / (precisionDenominator m n H : ℚ)))
    (thresholdSteps n (ballExponent m n H))

/-- A computable exact feasibility test using rounded rational ellipsoid steps.
This definition alone makes no claim about registered RAM execution. -/
def feasible {m n : ℕ} (P : Program ℤ m n) (H : ℕ) : Bool := (iterationResult P H).isSome

theorem feasible_of_feasible {m n : ℕ} (P : Program ℤ m n) (H : ℕ)
    (hn : 2 ≤ n) (hH : 1 ≤ H) (hA : ∀ i j, (P.A i j).natAbs ≤ H)
    (hb : ∀ i, (P.b i).natAbs ≤ H)
    (hf : IsFeasible (toReal (rationalProgram P))) : feasible P H = true := by
  obtain ⟨z, hunit, hball⟩ := normalized_feasible_ball P H hH hA hb hf
  obtain ⟨k, hk⟩ := search_finds_ball
    (normalizedMatrix P (outerScale n (coordinateCap m n H)))
    (normalizedBound P (1 / (precisionDenominator m n H : ℚ))) hn z
    (ballExponent m n H) hunit hball
  simp only [feasible, iterationResult, hk, Option.isSome_some]

theorem feasible_sound {m n : ℕ} (P : Program ℤ m n) (H : ℕ)
    (hH : 1 ≤ H) (hA : ∀ i j, (P.A i j).natAbs ≤ H)
    (hb : ∀ i, (P.b i).natAbs ≤ H) (h : feasible P H = true) :
    IsFeasible (toReal (rationalProgram P)) := by
  let R := outerScale n (coordinateCap m n H)
  let D := precisionDenominator m n H
  let A := normalizedMatrix P R
  let b := normalizedBound P (1 / (D : ℚ))
  cases hi : iterationResult P H with
  | none => simp [feasible, hi] at h
  | some k =>
    have hr := foundIteration_feasible A b (thresholdSteps n (ballExponent m n H)) k hi
    let x := realVector (trajectory A b k).2
    have hrreal : ∀ i, (∑ j, (A i j : ℝ) * x j) ≤ (b i : ℝ) := by
      intro i
      have h := (Rat.cast_le (K := ℝ)).mpr (hr i)
      simpa [RationalSeparation.rowValue, x, realVector] using h
    have hrelax := (normalized_iff_relaxed P R (1 / (D : ℚ)) x).mp hrreal
    by_contra hf
    apply integer_relaxation_infeasible P H hH hA hb hf
    refine ⟨(R : ℝ) • x, ?_⟩
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, D, precisionDenominator] using hrelax

/-- Correctness for every bounded integer coefficient input in dimension at
least two, including empty and lower-dimensional feasible polyhedra. -/
theorem feasible_correct {m n : ℕ} (P : Program ℤ m n) (H : ℕ)
    (hn : 2 ≤ n) (hH : 1 ≤ H) (hA : ∀ i j, (P.A i j).natAbs ≤ H)
    (hb : ∀ i, (P.b i).natAbs ≤ H) :
    feasible P H = true ↔ IsFeasible (toReal (rationalProgram P)) :=
  ⟨feasible_sound P H hH hA hb, feasible_of_feasible P H hn hH hA hb⟩

end Lax109476Proofs.IntegerFeasibilityDecision

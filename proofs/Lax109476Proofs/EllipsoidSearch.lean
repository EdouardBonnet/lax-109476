import Lax109476Proofs.RationalSeparation
import Lax109476Proofs.EllipsoidTermination

open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidSearch

open Lax109476.RationalCertificates
open RationalSeparation EllipsoidRounding EllipsoidCenter EllipsoidPrecision
open EllipsoidIteration EllipsoidSequence EllipsoidTermination

def fallbackNormal (n : ℕ) : Fin n → ℚ := fun j => if j.val = 0 then 1 else 0

/-- A nonzero integer violated row supplies the normal; a fixed nonzero
normal makes the trajectory total after success or a violated constant row. -/
def selectedNormal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ)
    (c : Fin n → ℚ) : Fin n → ℚ :=
  match firstViolation A b c with
  | none => fallbackNormal n
  | some i => if A i = 0 then fallbackNormal n else rationalRow A i

def trajectory {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ) :
    ℕ → Matrix (Fin n) (Fin n) ℚ × (Fin n → ℚ)
  | 0 => (1, 0)
  | k + 1 =>
    let old := trajectory A b k
    let a := selectedNormal A b old.2
    let D := gridDenominator (2 * k + 2) (2 * n + 4) n
    (roundedStepShape n old.1 a D (stepAccuracy n), roundedCenter n old.1 a old.2 D)

def normalSchedule {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ)
    (k : ℕ) : Fin n → ℚ := selectedNormal A b (trajectory A b k).2

theorem fallbackNormal_norm (n : ℕ) (hn : 0 < n) :
    1 ≤ realVector (fallbackNormal n) ⬝ᵥ realVector (fallbackNormal n) := by
  let a : Fin n → ℤ := fun j => if j.val = 0 then 1 else 0
  have ha : a ≠ 0 := by
    intro h
    have hz := congrFun h ⟨0, hn⟩
    simp [a] at hz
  have hc : realVector (fallbackNormal n) =
      (fun j : Fin n => (if j.val = 0 then 1 else 0 : ℝ)) := by
    funext j
    change ((if j.val = 0 then 1 else 0 : ℚ) : ℝ) = _
    split_ifs <;> norm_num
  rw [hc]
  simpa [a, apply_ite] using integer_normal_norm a ha

theorem selectedNormal_norm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℚ) (c : Fin n → ℚ) (hn : 0 < n) :
    1 ≤ realVector (selectedNormal A b c) ⬝ᵥ realVector (selectedNormal A b c) := by
  unfold selectedNormal
  split
  · exact fallbackNormal_norm n hn
  · split_ifs with hz
    · exact fallbackNormal_norm n hn
    · change 1 ≤ (fun j => (A _ j : ℝ)) ⬝ᵥ (fun j => (A _ j : ℝ))
      exact integer_normal_norm _ hz

/-- The executable trajectory is precisely the rational sequence whose
conditioning, containment, and contraction have been proved. -/
theorem trajectory_eq_sequences {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℚ) (k : ℕ) :
    (trajectory A b k).1 = shapes n (normalSchedule A b) k ∧
      (trajectory A b k).2 = centers n (normalSchedule A b) 0 k := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    simp only [trajectory, shapes, centers]
    have ha : selectedNormal A b (trajectory A b k).2 = normalSchedule A b k := rfl
    rw [ha, ih.1, ih.2]
    exact ⟨rfl, rfl⟩

/-- Inspect the bounded sequence of centers with exact rational comparisons. -/
def findIteration {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ)
    (K : ℕ) : Option ℕ :=
  (List.range (K + 1)).find? (fun k => decide (firstViolation A b (trajectory A b k).2 = none))

def search {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ)
    (K : ℕ) : Option (Fin n → ℚ) :=
  (findIteration A b K).map (fun k => (trajectory A b k).2)

theorem foundIteration_feasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℚ) (K k : ℕ) (h : findIteration A b K = some k) :
    ∀ i, rowValue A (trajectory A b k).2 i ≤ b i := by
  have hp := List.find?_some h
  have hv : firstViolation A b (trajectory A b k).2 = none := by simpa using hp
  exact (firstViolation_none A b _).mp hv

theorem noIteration_violated {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℚ) (K : ℕ) (h : findIteration A b K = none) :
    ∀ k ≤ K, firstViolation A b (trajectory A b k).2 ≠ none := by
  have hp := List.find?_eq_none.mp h
  intro k hk
  simpa using hp k (List.mem_range.mpr (by omega))

/-- A ball in the feasible set forces the actual rational search to find a
feasible center within the proved iteration budget. -/
theorem search_finds_ball {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℚ) (hn : 2 ≤ n) (z : Fin n → ℝ) (B : ℕ)
    (hunit : ∀ e : Fin n → ℝ, e ⬝ᵥ e ≤ (((2 : ℝ) ^ B)⁻¹) ^ 2 →
      (z + e) ⬝ᵥ (z + e) ≤ 1)
    (hfeas : ∀ e : Fin n → ℝ, e ⬝ᵥ e ≤ (((2 : ℝ) ^ B)⁻¹) ^ 2 →
      ∀ i, (∑ j, (A i j : ℝ) * (z + e) j) ≤ (b i : ℝ)) :
    ∃ k, findIteration A b (thresholdSteps n B) = some k := by
  by_contra h
  have hnone : findIteration A b (thresholdSteps n B) = none := by
    cases hfind : findIteration A b (thresholdSteps n B) with
    | none => rfl
    | some k => exact False.elim (h ⟨k, hfind⟩)
  have hnorm : ∀ k, 1 ≤ realVector (normalSchedule A b k) ⬝ᵥ
      realVector (normalSchedule A b k) := fun k => selectedNormal_norm A b _ (by omega)
  have hzero : realVector (0 : Fin n → ℚ) = 0 := by funext j; simp [realVector]
  apply cannot_retain_ball n hn (normalSchedule A b) hnorm 0 z B
    (by simpa only [hzero, sub_zero] using hunit)
  intro k hk e he
  have hvne := noIteration_violated A b _ hnone k (by omega)
  cases hv : firstViolation A b (trajectory A b k).2 with
  | none => exact False.elim (hvne hv)
  | some i =>
    have haz : A i ≠ 0 := by
      intro haz
      apply zero_row_infeasible A b _ i hv haz
      exact ⟨z + e, hfeas e he⟩
    have hnormal : normalSchedule A b k = rationalRow A i := by
      simp [normalSchedule, selectedNormal, hv, haz]
    have hcenter := (trajectory_eq_sequences A b k).2
    rw [hnormal, ← hcenter]
    exact (violation_retains_points A b _ i hv (z + e) (hfeas e he i)).le

end Lax109476Proofs.EllipsoidSearch

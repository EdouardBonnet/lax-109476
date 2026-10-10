import Lax109476Proofs.Relaxation
import Mathlib.Data.List.FinRange

open scoped BigOperators Matrix

namespace Lax109476Proofs.RationalSeparation

open Lax109476.RationalCertificates

def rowValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (c : Fin n → ℚ) (i : Fin m) : ℚ :=
  ∑ j, (A i j : ℚ) * c j

/-- Scan the finite rational inequalities in their stored order. -/
def firstViolation {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ)
    (c : Fin n → ℚ) : Option (Fin m) :=
  (List.finRange m).find? (fun i => decide (b i < rowValue A c i))

theorem firstViolation_none {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℚ) (c : Fin n → ℚ) :
    firstViolation A b c = none ↔ ∀ i, rowValue A c i ≤ b i := by
  simp [firstViolation, List.find?_eq_none, not_lt]

theorem firstViolation_violates {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℚ) (c : Fin n → ℚ) (i : Fin m)
    (h : firstViolation A b c = some i) : b i < rowValue A c i := by
  have hp := List.find?_some h
  simpa using hp

def rationalRow {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (i : Fin m) : Fin n → ℚ :=
  fun j => A i j

/-- Every nonzero integer normal meets the norm lower bound of the rounded
ellipsoid update, without an irrational normalization operation. -/
theorem integer_normal_norm {n : ℕ} (a : Fin n → ℤ) (ha : a ≠ 0) :
    1 ≤ (fun j => (a j : ℝ)) ⬝ᵥ (fun j => (a j : ℝ)) := by
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
    by_contra! h
    exact ha (funext h)
  have habs : (1 : ℝ) ≤ |(a j : ℝ)| := by
    have h : (1 : ℕ) ≤ (a j).natAbs := Int.natAbs_pos.mpr hj
    have hh : (1 : ℝ) ≤ ((a j).natAbs : ℝ) := by exact_mod_cast h
    simpa [Nat.cast_natAbs, Int.cast_abs] using hh
  have hsq : (1 : ℝ) ≤ (a j : ℝ) * (a j : ℝ) := by nlinarith [sq_abs (a j : ℝ)]
  exact hsq.trans (Finset.single_le_sum (fun k _ => mul_self_nonneg (a k : ℝ))
    (Finset.mem_univ j))

/-- A violated row gives a strict central cut retaining every feasible point. -/
theorem violation_retains_points {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℚ) (c : Fin n → ℚ) (i : Fin m)
    (h : firstViolation A b c = some i) (x : Fin n → ℝ)
    (hx : (∑ j, (A i j : ℝ) * x j) ≤ (b i : ℝ)) :
    realVector (rationalRow A i) ⬝ᵥ (x - realVector c) < 0 := by
  have hc := (Rat.cast_lt (K := ℝ)).mpr (firstViolation_violates A b c i h)
  have hid : realVector (rationalRow A i) ⬝ᵥ (x - realVector c) =
      (∑ j, (A i j : ℝ) * x j) - (rowValue A c i : ℝ) := by
    simp [realVector, rationalRow, dotProduct, rowValue, mul_sub, Finset.sum_sub_distrib]
  rw [hid]
  linarith

/-- A violated zero row proves that the system has no feasible point. -/
theorem zero_row_infeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℚ) (c : Fin n → ℚ) (i : Fin m)
    (h : firstViolation A b c = some i) (hzero : A i = 0) :
    ¬ ∃ x : Fin n → ℝ, ∀ k, (∑ j, (A k j : ℝ) * x j) ≤ (b k : ℝ) := by
  have hv := firstViolation_violates A b c i h
  have hneg : b i < 0 := by simpa [rowValue, hzero] using hv
  rintro ⟨x, hx⟩
  have hi := hx i
  have hpos : (0 : ℝ) ≤ (b i : ℝ) := by simpa [hzero] using hi
  exact (not_lt_of_ge hpos) ((Rat.cast_lt_zero (K := ℝ)).mpr hneg)

end Lax109476Proofs.RationalSeparation

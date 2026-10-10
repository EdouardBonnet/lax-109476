import Lax109476Proofs.Elimination.Farkas1
import Lax109476.RationalFeasibility
import Mathlib.Tactic

open scoped BigOperators

namespace Lax109476Proofs.RationalFeasibility

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.FarkasCertificate

private def augmentedMatrix {m n : ℕ} (P : Program ℚ m n) :
    Matrix (Fin m ⊕ Fin n) (Fin n) ℚ :=
  Sum.elim P.A (fun k j => if k = j then -1 else 0)

private def augmentedBound {m n : ℕ} (P : Program ℚ m n) :
    (Fin m ⊕ Fin n) → ℚ := Sum.elim P.b (fun _ => 0)

/-- Farkas' alternative over rational coefficient data and rational variables. -/
theorem rational_farkas_exists {m n : ℕ} (P : Program ℚ m n)
    (hP : ¬ ∃ x, PrimalFeasible P x) :
    ∃ y : Fin m → ℚ, IsInfeasibilityCertificate P y := by
  classical
  have hno : ¬ Lax109476Proofs.Elimination.Farkas1Primal
      (augmentedMatrix P) (augmentedBound P) := by
    rintro ⟨x, hx⟩
    apply hP
    refine ⟨x, ?_, ?_⟩
    · intro j
      have hj := hx (.inr j)
      simp [augmentedMatrix, augmentedBound, Matrix.mulVec, dotProduct] at hj
      linarith
    · intro i
      exact hx (.inl i)
  rcases Lax109476Proofs.Elimination.Farkas1ExhaustRat
      (augmentedMatrix P) (augmentedBound P) with hp | ⟨y, hy, hA, hb⟩
  · exact False.elim (hno hp)
  · refine ⟨fun i => y (.inl i), fun i => hy (.inl i), ?_, ?_⟩
    · intro j
      have heq := congr_fun hA j
      simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type,
        augmentedMatrix, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply] at heq
      have hsum : (∑ k, y (Sum.inr k) * (if k = j then (-1 : ℚ) else 0)) =
          -y (.inr j) := by simp
      rw [hsum] at heq
      have hid : columnValue P (fun i => y (.inl i)) j =
          ∑ i, y (.inl i) * P.A i j := by
        simp only [columnValue, mul_comm]
      rw [hid]
      linarith [hy (.inr j)]
    · simpa [dualValue, dotProduct, Fintype.sum_sum_type,
        augmentedBound, mul_comm] using hb

theorem cast_feasible {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ)
    (hx : PrimalFeasible P x) : PrimalFeasible (toReal P) (realVector x) := by
  constructor
  · intro j
    change (0 : ℝ) ≤ (x j : ℚ)
    exact_mod_cast hx.1 j
  · intro i
    have h := (Rat.cast_le (K := ℝ)).mpr (hx.2 i)
    simpa [rowValue, toReal, realVector] using h

theorem cast_farkas {m n : ℕ} (P : Program ℚ m n) (y : Fin m → ℚ)
    (hy : IsInfeasibilityCertificate P y) :
    IsInfeasibilityCertificate (toReal P) (realVector y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change (0 : ℝ) ≤ (y i : ℚ)
    exact_mod_cast hy.1 i
  · intro j
    have h := (Rat.cast_nonneg (K := ℝ)).mpr (hy.2.1 j)
    simpa [columnValue, toReal, realVector] using h
  · have h := (Rat.cast_lt_zero (K := ℝ)).mpr hy.2.2
    simpa [dualValue, toReal, realVector] using h

/--
---
conclusion: Lax109476.RationalFeasibility.exists_rational_feasible_point
---
If there were no rational feasible point, Fourier–Motzkin elimination over
the rationals would supply rational Farkas multipliers. Casting them into
the reals gives an infeasibility certificate, contradicting the real
feasible point. This argument also applies to lower-dimensional feasible sets.
-/
theorem rational_feasibility :
    ∀ (m n : ℕ) (P : Program ℚ m n), IsFeasible (toReal P) →
      ∃ x : Fin n → ℚ, PrimalFeasible P x := by
  intro m n P hf
  by_contra h
  obtain ⟨y, hy⟩ := rational_farkas_exists P h
  exact Lax109476.FarkasSoundness.certificate_not_feasible m n (toReal P)
    (realVector y) (cast_farkas P y hy) hf

/-- Reindexing permits the rational-witness theorem to be used with arbitrary
finite constraint and variable types. -/
theorem finite_rational_feasibility {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : Matrix κ ι ℚ) (b : κ → ℚ) (x : ι → ℝ)
    (hx : ∀ j, 0 ≤ x j)
    (hrows : ∀ i, (∑ j, (A i j : ℝ) * x j) ≤ (b i : ℝ)) :
    ∃ z : ι → ℚ, (∀ j, 0 ≤ z j) ∧ ∀ i, (∑ j, A i j * z j) ≤ b i := by
  classical
  let s := Fintype.equivFin ι
  let t := Fintype.equivFin κ
  let P : Program ℚ (Fintype.card κ) (Fintype.card ι) :=
    ⟨fun i j => A (t.symm i) (s.symm j), fun i => b (t.symm i), fun _ => 0⟩
  have hP : IsFeasible (toReal P) := by
    refine ⟨fun j => x (s.symm j), fun j => hx _, ?_⟩
    intro i
    change (∑ j, (A (t.symm i) (s.symm j) : ℝ) * x (s.symm j)) ≤ (b (t.symm i) : ℝ)
    have heq := Fintype.sum_equiv s.symm
      (fun j => (A (t.symm i) (s.symm j) : ℝ) * x (s.symm j))
      (fun j => (A (t.symm i) j : ℝ) * x j) (fun _ => rfl)
    exact heq.le.trans (hrows _)
  obtain ⟨z, hz⟩ := Lax109476.RationalFeasibility.exists_rational_feasible_point _ _ P hP
  refine ⟨fun j => z (s j), fun j => hz.1 _, ?_⟩
  intro i
  calc
    _ = ∑ j, A i (s.symm j) * z j :=
      Fintype.sum_equiv s _ _ (fun j => by simp)
    _ ≤ _ := by simpa [P, rowValue] using hz.2 (t i)

end Lax109476Proofs.RationalFeasibility

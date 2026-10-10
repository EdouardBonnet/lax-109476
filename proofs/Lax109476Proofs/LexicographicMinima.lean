import Lax109476Proofs.RationalMinima
import Lax109476Proofs.LexicographicSupport

open scoped BigOperators Matrix

namespace Lax109476Proofs.LexicographicMinima

open Lax109476.LinearProgram Lax109476.RationalCertificates
open RationalMinima


def fixedPrefix {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (k : ℕ) :
    Program ℚ (m + (n + n)) n where
  A := Fin.addCases P.A (Fin.addCases
    (fun i j => if i.val < k then if j = i then 1 else 0 else 0)
    (fun i j => if i.val < k then if j = i then -1 else 0 else 0))
  b := Fin.addCases P.b (Fin.addCases
    (fun i => if i.val < k then x i else 0)
    (fun i => if i.val < k then -x i else 0))
  c := P.c

theorem fixedPrefix_feasible {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ)
    (k : ℕ) (y : Fin n → ℝ) :
    PrimalFeasible (toReal (fixedPrefix P x k)) y ↔
      PrimalFeasible (toReal P) y ∧ ∀ j, j.val < k → y j = (x j : ℝ) := by
  have hrow : ∀ i : Fin m, rowValue (toReal (fixedPrefix P x k)) y
      (Fin.castAdd (n + n) i) = rowValue (toReal P) y i := by
    intro i
    simp [-Fin.natAdd_eq_addNat, rowValue, toReal, fixedPrefix]
  have hpos : ∀ j : Fin n, rowValue (toReal (fixedPrefix P x k)) y
      (Fin.natAdd m (Fin.castAdd n j)) = if j.val < k then y j else 0 := by
    intro j
    by_cases hj : j.val < k <;> simp [-Fin.natAdd_eq_addNat, rowValue, toReal, fixedPrefix, hj, apply_ite]
  have hneg : ∀ j : Fin n, rowValue (toReal (fixedPrefix P x k)) y
      (Fin.natAdd m (Fin.natAdd n j)) = if j.val < k then -y j else 0 := by
    intro j
    by_cases hj : j.val < k <;> simp [-Fin.natAdd_eq_addNat, rowValue, toReal, fixedPrefix, hj, apply_ite]
  constructor
  · rintro ⟨hy, hr⟩
    refine ⟨⟨hy, fun i => ?_⟩, fun j hj => ?_⟩
    · have h := hr (Fin.castAdd (n + n) i)
      rw [hrow] at h
      simpa [toReal, fixedPrefix] using h
    · have hp := hr (Fin.natAdd m (Fin.castAdd n j))
      have hn := hr (Fin.natAdd m (Fin.natAdd n j))
      rw [hpos] at hp
      rw [hneg] at hn
      simp [-Fin.natAdd_eq_addNat, toReal, fixedPrefix, hj] at hp hn
      linarith
  · rintro ⟨⟨hy, hr⟩, hprefix⟩
    refine ⟨hy, fun i => ?_⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [hrow]
      simpa [toReal, fixedPrefix] using hr i
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [hpos]
        by_cases hj : j.val < k <;> simp [-Fin.natAdd_eq_addNat, toReal, fixedPrefix, hj, hprefix j]
      · rw [hneg]
        by_cases hj : j.val < k <;> simp [-Fin.natAdd_eq_addNat, toReal, fixedPrefix, hj, hprefix j]

theorem exists_partial_lex_minimum {m n : ℕ} (P : Program ℚ m n)
    (hf : IsFeasible (toReal P)) (k : ℕ) (hk : k ≤ n) :
    ∃ x : Fin n → ℚ, PrimalFeasible (toReal P) (realVector x) ∧
      ∀ i, i.val < k → ∀ y, PrimalFeasible (toReal P) y →
        (∀ j, j < i → y j = (x j : ℝ)) → (x i : ℝ) ≤ y i := by
  induction k with
  | zero =>
    obtain ⟨x, hx⟩ := Lax109476.RationalFeasibility.exists_rational_feasible_point m n P hf
    exact ⟨x, RationalFeasibility.cast_feasible P x hx, fun i hi => by omega⟩
  | succ k ih =>
    obtain ⟨x, hx, hlex⟩ := ih (by omega)
    let i : Fin n := ⟨k, by omega⟩
    have hQ : IsFeasible (toReal (fixedPrefix P x k)) :=
      ⟨realVector x, (fixedPrefix_feasible P x k _).mpr ⟨hx, fun _ _ => rfl⟩⟩
    obtain ⟨z, hz, hzmin⟩ := exists_coordinate_minimum (fixedPrefix P x k) i hQ
    obtain ⟨hzP, hzpref⟩ := (fixedPrefix_feasible P x k _).mp hz
    refine ⟨z, hzP, fun j hj y hy hprior => ?_⟩
    by_cases hjk : j.val < k
    · have hzpref' : ∀ l, l.val < k → (z l : ℝ) = (x l : ℝ) := hzpref
      rw [hzpref' j hjk]
      apply hlex j hjk y hy
      intro l hlj
      rw [← hzpref' l (by exact lt_trans hlj hjk)]
      exact hprior l hlj
    · have hji : j = i := Fin.ext (by dsimp [i]; omega)
      subst j
      apply hzmin y
      apply (fixedPrefix_feasible P x k y).mpr
      refine ⟨hy, fun l hl => ?_⟩
      have he : (z l : ℝ) = (x l : ℝ) := hzpref l hl
      rw [← he]
      exact hprior l hl

def equationProgram {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) :
    Program ℚ (m + m) n where
  A := Fin.addCases C (fun i j => -C i j)
  b := Fin.addCases b (fun i => -b i)
  c := 0

theorem equationProgram_feasible {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) (y : Fin n → ℝ) :
    PrimalFeasible (toReal (equationProgram C b)) y ↔
      (∀ j, 0 ≤ y j) ∧ (C.map (fun q => (q : ℝ))) *ᵥ y = fun i => (b i : ℝ) := by
  have hpos : ∀ i : Fin m, rowValue (toReal (equationProgram C b)) y
      (Fin.castAdd m i) = (C.map (fun q => (q : ℝ)) *ᵥ y) i := by
    intro i
    have ha : (equationProgram C b).A (Fin.castAdd m i) = C i := by
      dsimp only [equationProgram]
      exact Fin.addCases_left (motive := fun _ : Fin (m + m) => Fin n → ℚ)
        (left := C) (right := fun i j => -C i j) i
    change (∑ j, ((equationProgram C b).A (Fin.castAdd m i) j : ℝ) * y j) = _
    rw [ha]
    rfl
  have hneg : ∀ i : Fin m, rowValue (toReal (equationProgram C b)) y
      (Fin.natAdd m i) = -(C.map (fun q => (q : ℝ)) *ᵥ y) i := by
    intro i
    have ha : (equationProgram C b).A (Fin.natAdd m i) = (fun j => -C i j) := by
      dsimp only [equationProgram]
      exact Fin.addCases_right (motive := fun _ : Fin (m + m) => Fin n → ℚ)
        (left := C) (right := fun i j => -C i j) i
    change (∑ j, ((equationProgram C b).A (Fin.natAdd m i) j : ℝ) * y j) = _
    rw [ha]
    simp [Matrix.mulVec, Matrix.map, dotProduct, Finset.sum_neg_distrib]
  constructor
  · rintro ⟨hy, hr⟩
    refine ⟨hy, funext (fun i => ?_)⟩
    have hp := hr (Fin.castAdd m i)
    have hn := hr (Fin.natAdd m i)
    rw [hpos] at hp
    rw [hneg] at hn
    simp [-Fin.natAdd_eq_addNat, toReal, equationProgram] at hp hn
    linarith
  · rintro ⟨hy, he⟩
    refine ⟨hy, fun i => ?_⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [hpos, he]
      simp [toReal, equationProgram]
    · rw [hneg, he]
      simp [-Fin.natAdd_eq_addNat, toReal, equationProgram]

theorem cast_standard_feasible {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) (x : Fin n → ℚ) :
    LexicographicSupport.Feasible C b x ↔
      PrimalFeasible (toReal (equationProgram C b)) (realVector x) := by
  rw [equationProgram_feasible]
  have hcast : (C.map (fun q => (q : ℝ))) *ᵥ realVector x =
      fun i => ((C *ᵥ x) i : ℝ) := by
    funext i
    simp [Matrix.mulVec, Matrix.map, realVector, dotProduct, Rat.cast_sum]
  rw [hcast]
  constructor
  · rintro ⟨hx, he⟩
    exact ⟨fun j => (Rat.cast_nonneg (K := ℝ)).mpr (hx j), by rw [he]⟩
  · rintro ⟨hx, he⟩
    refine ⟨fun j => (Rat.cast_nonneg (K := ℝ)).mp (hx j), funext (fun i => ?_)⟩
    exact Rat.cast_injective (congrFun he i)

theorem exists_lex_minimum {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) (hf : ∃ x, LexicographicSupport.Feasible C b x) :
    ∃ x, LexicographicSupport.LexMinimum C b x := by
  obtain ⟨x₀, hx₀⟩ := hf
  have hfP : IsFeasible (toReal (equationProgram C b)) :=
    ⟨realVector x₀, (cast_standard_feasible C b x₀).mp hx₀⟩
  obtain ⟨x, hx, hlex⟩ := exists_partial_lex_minimum (equationProgram C b) hfP n le_rfl
  refine ⟨x, (cast_standard_feasible C b x).mpr hx, fun y hy i hprior => ?_⟩
  have h := hlex i i.isLt (realVector y) ((cast_standard_feasible C b y).mp hy)
    (fun j hj => by change (y j : ℝ) = (x j : ℝ); rw [hprior j hj])
  exact (Rat.cast_le (K := ℝ)).mp h

end Lax109476Proofs.LexicographicMinima

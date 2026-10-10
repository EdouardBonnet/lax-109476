import Lax109476Proofs.LexicographicBounds

open scoped BigOperators Matrix

namespace Lax109476Proofs.PointRecovery

open Lax109476.LinearProgram Lax109476.RationalCertificates
open LexicographicMinima CoordinateOptimization LexicographicBounds

def prefixVector {n : ℕ} (x : Fin n → ℚ) (k : ℕ) : Fin n → ℚ :=
  fun j => if j.val < k then x j else 0

/-- Recover coordinates in order. Every query is the proved exact rational
feasibility decision, and every returned coordinate comes from reconstruction. -/
def recoverPrefix {m n : ℕ} (P : Program ℚ m n) (B : ℕ) :
    ℕ → Option (Fin n → ℚ)
  | 0 => some 0
  | k + 1 =>
    (recoverPrefix P B k).bind (fun old =>
      if h : k < n then
        (coordinateMinimum (fixedPrefix P old k) ⟨k, h⟩ B).map
          (fun v => Function.update old ⟨k, h⟩ v)
      else some old)

theorem recoverPrefix_exact {m n : ℕ} (P : Program ℚ m n) (B : ℕ)
    (x : Fin n → ℚ) (hx : PrimalFeasible (toReal P) (realVector x))
    (hlex : ∀ i, ∀ y, PrimalFeasible (toReal P) y →
      (∀ j, j < i → y j = (x j : ℝ)) → (x i : ℝ) ≤ y i)
    (hb : ∀ j, x j ≤ B ∧ (x j).den ≤ B) (k : ℕ) (hk : k ≤ n) :
    recoverPrefix P B k = some (prefixVector x k) := by
  induction k with
  | zero =>
    simp only [recoverPrefix, Option.some.injEq]
    funext j
    simp [prefixVector]
  | succ k ih =>
    have hkn : k < n := by omega
    have hprev := ih (by omega)
    let i : Fin n := ⟨k, hkn⟩
    have hxf : PrimalFeasible (toReal (fixedPrefix P (prefixVector x k) k)) (realVector x) := by
      apply (fixedPrefix_feasible P _ k _).mpr
      refine ⟨hx, fun j hj => ?_⟩
      simp [prefixVector, hj, realVector]
    have hmin : ∀ y, PrimalFeasible (toReal (fixedPrefix P (prefixVector x k) k)) y →
        (x i : ℝ) ≤ y i := by
      intro y hy
      obtain ⟨hyP, hypref⟩ := (fixedPrefix_feasible P _ k y).mp hy
      apply hlex i y hyP
      intro j hj
      have hval : j.val < k := hj
      simpa [prefixVector, hval] using hypref j hval
    have hcoord := coordinateMinimum_exact (fixedPrefix P (prefixVector x k) k) i x hxf hmin
      B (hb i).1 (hb i).2
    simp only [recoverPrefix, hprev, Option.bind_some, dif_pos hkn]
    rw [hcoord]
    simp only [Option.map_some, Option.some.injEq]
    funext j
    by_cases hji : j = i
    · subst j
      simp [prefixVector, i, Function.update]
    · have hv : j.val ≠ k := by intro he; exact hji (Fin.ext he)
      change Function.update (prefixVector x k) i (x i) j = prefixVector x (k + 1) j
      rw [Function.update_of_ne hji]
      simp only [prefixVector]
      have he : (j.val < k + 1) = (j.val < k) := propext (by omega)
      simp only [he]

def recover {m n : ℕ} (P : Program ℚ m n) (B : ℕ) : Option (Fin n → ℚ) :=
  recoverPrefix P B n

theorem recover_exact {m n : ℕ} (P : Program ℚ m n) (B : ℕ)
    (x : Fin n → ℚ) (hx : PrimalFeasible (toReal P) (realVector x))
    (hlex : ∀ i, ∀ y, PrimalFeasible (toReal P) y →
      (∀ j, j < i → y j = (x j : ℝ)) → (x i : ℝ) ≤ y i)
    (hb : ∀ j, x j ≤ B ∧ (x j).den ≤ B) : recover P B = some x := by
  have he : prefixVector x n = x := by funext j; simp [prefixVector, j.isLt]
  simpa only [recover, he] using recoverPrefix_exact P B x hx hlex hb n le_rfl

/-- The determinant cap is computed from the original integer system once,
then used uniformly for every recovered coordinate. -/
def standardPoint {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (H : ℕ) : Option (Fin n → ℚ) :=
  recover (equationProgram (C.map (fun a => (a : ℚ))) (fun i => (b i : ℚ)))
    (coordinateCap m n H)

theorem standardPoint_correct {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (H : ℕ) (hC : ∀ i j, (C i j).natAbs ≤ H)
    (hb : ∀ i, (b i).natAbs ≤ H)
    (hf : ∃ x, LexicographicSupport.Feasible (C.map (fun a => (a : ℚ)))
      (fun i => (b i : ℚ)) x) :
    ∃ x, standardPoint C b H = some x ∧
      LexicographicSupport.Feasible (C.map (fun a => (a : ℚ))) (fun i => (b i : ℚ)) x ∧
      ∀ j, (x j).num.natAbs ≤ coordinateCap m n H ∧ (x j).den ≤ coordinateCap m n H := by
  obtain ⟨x, hx, hbounded, hlex⟩ := exists_bounded_lex_point C b H hC hb hf
  refine ⟨x, ?_, hx, hbounded⟩
  apply recover_exact _ _ x ((cast_standard_feasible _ _ x).mp hx) hlex
  intro j
  refine ⟨?_, (hbounded j).2⟩
  have hm : |(x j : ℝ)| ≤ coordinateCap m n H :=
    Relaxation.rational_magnitude_bound (x j) _ (hbounded j).1
  exact (Rat.cast_le (K := ℝ)).mp ((le_abs_self _).trans hm)

end Lax109476Proofs.PointRecovery

import Lax109476Proofs.IntegerCertificates
import Lax109476Proofs.RationalFeasibility
import Lax109476Proofs.Basic

open scoped BigOperators Matrix

namespace Lax109476Proofs.Relaxation

open Lax109476.LinearProgram Lax109476.FarkasCertificate
open Lax109476.RationalCertificates
open IntegerEncoding IntegerCertificates RationalFeasibility

/-- Both the inequality rows and the nonnegativity rows are relaxed uniformly. -/
def RelaxedFeasible {m n : ℕ} (P : Program ℝ m n) (ε : ℝ) (x : Fin n → ℝ) : Prop :=
  (∀ j, -ε ≤ x j) ∧ ∀ i, rowValue P x i ≤ P.b i + ε

/-- Bounded normalized Farkas multipliers give an explicit relaxation gap. -/
theorem farkas_excludes_relaxation {m n : ℕ} (P : Program ℝ m n)
    (y : Fin m → ℝ) (B H ε : ℝ) (_hB : 0 ≤ B) (hH : 0 ≤ H) (hε : 0 ≤ ε)
    (hy : IsInfeasibilityCertificate P y) (hdual : dualValue P y ≤ -1)
    (hyB : ∀ i, y i ≤ B) (hAH : ∀ i j, |P.A i j| ≤ H)
    (hgap : ε * ((m : ℝ) * B + (n : ℝ) * m * H * B) < 1) :
    ¬ ∃ x, RelaxedFeasible P ε x := by
  have hysum : (∑ i, y i) ≤ (m : ℝ) * B := by
    calc
      _ ≤ ∑ _i : Fin m, B := Finset.sum_le_sum (fun i _ => hyB i)
      _ = _ := by simp
  have hcol : ∀ j, columnValue P y j ≤ (m : ℝ) * H * B := by
    intro j
    calc
      _ ≤ ∑ _i : Fin m, H * B := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul ((le_abs_self _).trans (hAH i j)) (hyB i) (hy.1 i) hH
      _ = _ := by simp; ring
  have hcolsum : (∑ j, columnValue P y j) ≤ (n : ℝ) * m * H * B := by
    calc
      _ ≤ ∑ _j : Fin n, ((m : ℝ) * H * B) := Finset.sum_le_sum (fun j _ => hcol j)
      _ = _ := by simp; ring
  rintro ⟨x, hx⟩
  have hlo : -ε * ∑ j, columnValue P y j ≤ ∑ j, columnValue P y j * x j := by
    calc
      _ = ∑ j, columnValue P y j * -ε := by rw [← Finset.sum_mul]; ring
      _ ≤ _ := Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left (hx.1 j) (hy.2.1 j))
  have hup : (∑ j, columnValue P y j * x j) ≤ dualValue P y + ε * ∑ i, y i := by
    rw [Lax109476Proofs.Basic.transpose_identity]
    calc
      _ ≤ ∑ i, (P.b i + ε) * y i := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_right (hx.2 i) (hy.1 i))
      _ = _ := by simp [dualValue, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  have hlob := mul_le_mul_of_nonpos_left hcolsum (neg_nonpos.mpr hε)
  have hupb := add_le_add hdual (mul_le_mul_of_nonneg_left hysum hε)
  have hcontr := (hlob.trans hlo).trans (hup.trans hupb)
  nlinarith

/-- A bounded coordinate perturbation changes a row by at most `n H r`. -/
theorem row_perturbation_bound {m n : ℕ} (P : Program ℝ m n)
    (x e : Fin n → ℝ) (H r : ℝ) (hH : 0 ≤ H) (_hr : 0 ≤ r)
    (hA : ∀ i j, |P.A i j| ≤ H) (he : ∀ j, |e j| ≤ r) (i : Fin m) :
    |rowValue P (x + e) i - rowValue P x i| ≤ (n : ℝ) * H * r := by
  have hrow : rowValue P (x + e) i - rowValue P x i = ∑ j, P.A i j * e j := by
    simp [rowValue, mul_add, Finset.sum_add_distrib]
  rw [hrow]
  calc
    _ ≤ ∑ j, |P.A i j * e j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, H * r := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hA i j) (he j) (abs_nonneg _) hH
    _ = _ := by simp; ring

/-- Every feasible point is the center of a cube in the relaxed feasible set,
including points on the boundary of a lower-dimensional feasible polyhedron. -/
theorem perturbation_feasible {m n : ℕ} (P : Program ℝ m n)
    (x e : Fin n → ℝ) (H r ε : ℝ) (hH : 0 ≤ H) (hr : 0 ≤ r)
    (hrε : r ≤ ε) (hrowε : (n : ℝ) * H * r ≤ ε)
    (hA : ∀ i j, |P.A i j| ≤ H) (he : ∀ j, |e j| ≤ r)
    (hx : PrimalFeasible P x) : RelaxedFeasible P ε (x + e) := by
  constructor
  · intro j
    have h := (abs_le.mp (he j)).1
    change -ε ≤ x j + e j
    linarith [hx.1 j]
  · intro i
    have h := (abs_le.mp (row_perturbation_bound P x e H r hH hr hA he i)).2
    linarith [hx.2 i]

/-- A reduced numerator bound also bounds the real magnitude. -/
theorem rational_magnitude_bound (q : ℚ) (B : ℕ) (hq : q.num.natAbs ≤ B) :
    |(q : ℝ)| ≤ (B : ℝ) := by
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hd₁ : (1 : ℝ) ≤ q.den := by exact_mod_cast q.den_pos
  have hn : |(q.num : ℝ)| ≤ (B : ℝ) := by
    have h : (q.num.natAbs : ℝ) ≤ (B : ℝ) := by exact_mod_cast hq
    simpa only [Nat.cast_natAbs, Int.cast_abs] using h
  have heq : |(q : ℝ)| = |(q.num : ℝ)| / q.den := by
    conv_lhs => rw [← q.num_div_den]
    simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, abs_div,
      abs_of_pos hd]
  rw [heq]
  apply (div_le_iff₀ hd).mpr
  exact hn.trans (by simpa using mul_le_mul_of_nonneg_left hd₁ (Nat.cast_nonneg B))

def relaxationDenominator (m n H B : ℕ) : ℕ :=
  2 * (m * B + n * m * H * B + 1)

theorem relaxation_gap (m n H B : ℕ) :
    (1 / (relaxationDenominator m n H B : ℝ)) *
      ((m : ℝ) * B + (n : ℝ) * m * H * B) < 1 := by
  let G : ℝ := (m : ℝ) * B + (n : ℝ) * m * H * B
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hden : 0 < 2 * (G + 1) := by linarith
  change (1 / (relaxationDenominator m n H B : ℝ)) * G < 1
  have hd : (relaxationDenominator m n H B : ℝ) = 2 * (G + 1) := by
    simp [relaxationDenominator, G]
  rw [hd, one_div, inv_mul_eq_div]
  exact (div_lt_one hden).mpr (by linarith)

/-- An explicit rational relaxation remains infeasible whenever the original
integer LP is infeasible. Its precision depends only on coefficient and
certificate bounds, not on a numerical separation oracle. -/
theorem integer_relaxation_infeasible {m n : ℕ} (P : Program ℤ m n)
    (H : ℕ) (hH : 1 ≤ H) (hA : ∀ i j, (P.A i j).natAbs ≤ H)
    (hb : ∀ i, (P.b i).natAbs ≤ H)
    (hf : ¬ IsFeasible (toReal (rationalProgram P))) :
    ¬ ∃ x, RelaxedFeasible (toReal (rationalProgram P))
      (1 / (relaxationDenominator m n H (coordinateCap m n H) : ℝ)) x := by
  have hrat : ¬ ∃ x : Fin n → ℚ, PrimalFeasible (rationalProgram P) x := by
    rintro ⟨x, hx⟩
    exact hf ⟨realVector x, cast_feasible _ x hx⟩
  obtain ⟨y, hy⟩ := rational_farkas_exists (rationalProgram P) hrat
  obtain ⟨yr, hyr, hsize, hdual⟩ := normalized_small_infeasibility_certificate
    P H hH hA hb y hy
  let B := coordinateCap m n H
  have hyreal := cast_farkas (rationalProgram P) yr hyr
  have hdy : dualValue (toReal (rationalProgram P)) (realVector yr) ≤ -1 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hdual
    simpa [dualValue, toReal, rationalProgram, realVector] using h
  have hmag : ∀ i, realVector yr i ≤ (B : ℝ) := fun i =>
    (le_abs_self _).trans (rational_magnitude_bound (yr i) B (hsize i).1)
  have ha : ∀ i j, |(toReal (rationalProgram P)).A i j| ≤ (H : ℝ) := by
    intro i j
    have h : ((P.A i j).natAbs : ℝ) ≤ (H : ℝ) := by exact_mod_cast hA i j
    simpa [toReal, rationalProgram, Nat.cast_natAbs, Int.cast_abs] using h
  apply farkas_excludes_relaxation _ (realVector yr) (B : ℝ) (H : ℝ) _
    (by positivity) (by positivity) (by positivity) hyreal hdy hmag ha
  exact relaxation_gap m n H B

/-- A feasible integer LP has a real feasible point inside the explicit
coordinate cap, obtained from the independent-support argument. -/
theorem bounded_real_feasible_point {m n : ℕ} (P : Program ℤ m n)
    (H : ℕ) (hH : 1 ≤ H) (hA : ∀ i j, (P.A i j).natAbs ≤ H)
    (hb : ∀ i, (P.b i).natAbs ≤ H)
    (hf : IsFeasible (toReal (rationalProgram P))) :
    ∃ x : Fin n → ℝ, PrimalFeasible (toReal (rationalProgram P)) x ∧
      ∀ j, |x j| ≤ (coordinateCap m n H : ℝ) := by
  obtain ⟨x, hx⟩ := Lax109476.RationalFeasibility.exists_rational_feasible_point
    m n (rationalProgram P) hf
  obtain ⟨yr, hypos, hyrows, hysize⟩ := SmallFeasiblePoint.exists_capped_integer_inequality_point
    (P.A : Matrix (Fin m) (Fin n) ℤ) P.b H (2 * (m + n) + 2) hH
    (by simp only [Fintype.card_fin]; omega) hA hb ⟨x, hx⟩
  have hy : PrimalFeasible (rationalProgram P) yr := ⟨hypos, hyrows⟩
  exact ⟨realVector yr, cast_feasible _ yr hy,
    fun j => rational_magnitude_bound (yr j) _ (hysize j).1⟩

/-- Euclidean balls are contained in coordinate cubes of the same radius. -/
theorem coordinate_bound_of_ball {n : ℕ} (e : Fin n → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (he : dotProduct e e ≤ r ^ 2) (j : Fin n) : |e j| ≤ r := by
  have hj : e j * e j ≤ dotProduct e e :=
    Finset.single_le_sum (fun i _ => mul_self_nonneg (e i)) (Finset.mem_univ j)
  nlinarith [sq_abs (e j), abs_nonneg (e j)]

noncomputable def cubeRadius (n : ℕ) (H ε : ℝ) : ℝ := ε / ((n : ℝ) * H + 1)

theorem cubeRadius_bounds (n : ℕ) (H ε : ℝ) (hH : 0 ≤ H) (hε : 0 < ε) :
    0 < cubeRadius n H ε ∧ cubeRadius n H ε ≤ ε ∧
      (n : ℝ) * H * cubeRadius n H ε ≤ ε := by
  have hnH : 0 ≤ (n : ℝ) * H := by positivity
  have hden : 0 < (n : ℝ) * H + 1 := by linarith
  refine ⟨div_pos hε hden, ?_, ?_⟩
  · exact (div_le_iff₀ hden).mpr (by nlinarith)
  · dsimp [cubeRadius]
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hden).mpr (by nlinarith)

/-- Feasibility gives a full-dimensional ball after the prescribed relaxation. -/
theorem ball_in_relaxation {m n : ℕ} (P : Program ℝ m n) (H ε : ℝ)
    (hH : 0 ≤ H) (hε : 0 < ε) (hA : ∀ i j, |P.A i j| ≤ H)
    (x : Fin n → ℝ) (hx : PrimalFeasible P x) :
    ∀ e : Fin n → ℝ, dotProduct e e ≤ (cubeRadius n H ε) ^ 2 →
      RelaxedFeasible P ε (x + e) := by
  obtain ⟨hr, hrε, hnHr⟩ := cubeRadius_bounds n H ε hH hε
  intro e he
  exact perturbation_feasible P x e H _ ε hH hr.le hrε hnHr hA
    (fun j => coordinate_bound_of_ball e _ hr.le he j) hx

end Lax109476Proofs.Relaxation

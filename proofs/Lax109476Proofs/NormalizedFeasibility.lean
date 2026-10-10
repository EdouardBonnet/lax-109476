import Lax109476Proofs.EllipsoidSearch
import Mathlib.Data.Fin.Tuple.Basic

open scoped BigOperators Matrix

namespace Lax109476Proofs.NormalizedFeasibility

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding IntegerCertificates Relaxation

def outerScale (n B : ℕ) : ℕ := 4 * (n + 1) * (B + 1)

def normalizedMatrix {m n : ℕ} (P : Program ℤ m n) (R : ℕ) :
    Matrix (Fin (m + n)) (Fin n) ℤ :=
  Fin.addCases (fun i j => (R : ℤ) * P.A i j)
    (fun k j => if k = j then -(R : ℤ) else 0)

def normalizedBound {m n : ℕ} (P : Program ℤ m n) (ε : ℚ) : Fin (m + n) → ℚ :=
  Fin.addCases (fun i => (P.b i : ℚ) + ε) (fun _ => ε)

/-- Scaling the variables preserves the relaxed inequalities; the appended
rows explicitly express relaxed nonnegativity. -/
theorem normalized_iff_relaxed {m n : ℕ} (P : Program ℤ m n) (R : ℕ) (ε : ℚ)
    (z : Fin n → ℝ) :
    (∀ i, (∑ j, (normalizedMatrix P R i j : ℝ) * z j) ≤ (normalizedBound P ε i : ℝ)) ↔
      RelaxedFeasible (toReal (rationalProgram P)) (ε : ℝ) ((R : ℝ) • z) := by
  constructor
  · intro h
    constructor
    · intro j
      have hj := h (Fin.natAdd m j)
      have hh : -(R : ℝ) * z j ≤ (ε : ℝ) := by
        simpa [normalizedMatrix, normalizedBound, apply_ite] using hj
      change -(ε : ℝ) ≤ (R : ℝ) * z j
      linarith
    · intro i
      have hi := h (Fin.castAdd n i)
      simpa [normalizedMatrix, normalizedBound, rowValue, toReal,
        rationalProgram, Finset.mul_sum, mul_assoc, mul_left_comm] using hi
  · rintro ⟨hnonneg, hrows⟩ i
    refine Fin.addCases ?_ ?_ i
    · intro i
      simpa [normalizedMatrix, normalizedBound, rowValue, toReal,
        rationalProgram, Finset.mul_sum, mul_assoc, mul_left_comm] using hrows i
    · intro j
      have hj : -(R : ℝ) * z j ≤ (ε : ℝ) := by
        have h := hnonneg j
        change -(ε : ℝ) ≤ (R : ℝ) * z j at h
        linarith
      simpa [normalizedMatrix, normalizedBound, apply_ite] using hj

theorem outerScale_pos (n B : ℕ) : 0 < outerScale n B := by
  unfold outerScale
  positivity

theorem outerScale_large (n B : ℕ) :
    (n : ℝ) * (B : ℝ) ^ 2 ≤ (outerScale n B : ℝ) ^ 2 / 16 := by
  have hn : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  have hb : (B : ℝ) ^ 2 ≤ ((B : ℝ) + 1) ^ 2 := by
    nlinarith [(Nat.cast_nonneg B : (0 : ℝ) ≤ B)]
  have h := mul_le_mul hn hb (sq_nonneg (B : ℝ)) (sq_nonneg ((n : ℝ) + 1))
  simp only [outerScale, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  nlinarith

/-- The bounded feasible point lies well inside the initial unit ball after
the computable variable scaling. -/
theorem scaled_point_norm {n : ℕ} (x : Fin n → ℝ) (B : ℕ)
    (hx : ∀ j, |x j| ≤ (B : ℝ)) :
    ((outerScale n B : ℝ)⁻¹ • x) ⬝ᵥ ((outerScale n B : ℝ)⁻¹ • x) ≤ 1 / 16 := by
  have hr : (0 : ℝ) < outerScale n B := by exact_mod_cast outerScale_pos n B
  have hs : x ⬝ᵥ x ≤ (n : ℝ) * (B : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin n, (B : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        nlinarith [(abs_le.mp (hx j)).1, (abs_le.mp (hx j)).2]
      _ = _ := by simp
  have hlarge := outerScale_large n B
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, inv_pow, inv_mul_eq_div]
  apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
  linarith

/-- A smaller ball around such a normalized point remains inside the unit ball. -/
theorem ball_inside_unit {n : ℕ} (z : Fin n → ℝ) (hz : z ⬝ᵥ z ≤ 1 / 16)
    (r : ℝ) (hr : 0 ≤ r) (hrsmall : r ≤ 1 / 2) :
    ∀ e : Fin n → ℝ, e ⬝ᵥ e ≤ r ^ 2 → (z + e) ⬝ᵥ (z + e) ≤ 1 := by
  intro e he
  have h := EllipsoidCenter.form_add_le_two
    (show (1 : Matrix (Fin n) (Fin n) ℝ).PosDef from Matrix.PosDef.one) z e
  simp only [Matrix.one_mulVec] at h
  nlinarith

def precisionDenominator (m n H : ℕ) : ℕ :=
  relaxationDenominator m n H (coordinateCap m n H)

def ballDenominator (m n H : ℕ) : ℕ :=
  precisionDenominator m n H * (n * H + 1) * outerScale n (coordinateCap m n H)

def ballExponent (m n H : ℕ) : ℕ := Nat.size (ballDenominator m n H)

theorem precisionDenominator_pos (m n H : ℕ) : 0 < precisionDenominator m n H := by
  unfold precisionDenominator relaxationDenominator
  positivity

theorem ballDenominator_pos (m n H : ℕ) : 0 < ballDenominator m n H := by
  unfold ballDenominator
  exact Nat.mul_pos (Nat.mul_pos (precisionDenominator_pos _ _ _) (by omega))
    (outerScale_pos _ _)

theorem ballDenominator_ge_two (m n H : ℕ) : 2 ≤ ballDenominator m n H := by
  have hD : 2 ≤ precisionDenominator m n H := by
    unfold precisionDenominator relaxationDenominator
    omega
  exact hD.trans ((Nat.le_mul_of_pos_right _ (by omega : 0 < n * H + 1)).trans
    (Nat.le_mul_of_pos_right _ (outerScale_pos _ _)))

theorem dyadic_radius_bound (m n H : ℕ) :
    ((2 : ℝ) ^ ballExponent m n H)⁻¹ ≤ 1 / (ballDenominator m n H : ℝ) := by
  have hN : (0 : ℝ) < ballDenominator m n H := by exact_mod_cast ballDenominator_pos m n H
  have hpow : (0 : ℝ) < 2 ^ ballExponent m n H := by positivity
  rw [one_div]
  apply (inv_le_inv₀ hpow hN).mpr
  exact_mod_cast (Nat.lt_size_self (ballDenominator m n H)).le

theorem dyadic_radius_small (m n H : ℕ) :
    ((2 : ℝ) ^ ballExponent m n H)⁻¹ ≤ 1 / 2 := by
  have hN : (0 : ℝ) < ballDenominator m n H := by exact_mod_cast ballDenominator_pos m n H
  have hN₂ : (2 : ℝ) ≤ ballDenominator m n H := by exact_mod_cast ballDenominator_ge_two m n H
  apply (dyadic_radius_bound m n H).trans
  rw [one_div]
  simpa only [one_div] using (inv_le_inv₀ hN (by norm_num : (0 : ℝ) < 2)).mpr hN₂

/-- The radius derived from input magnitude bounds is realized by a dyadic
ball in the normalized relaxed system and its initial unit ellipsoid. -/
theorem normalized_feasible_ball {m n : ℕ} (P : Program ℤ m n) (H : ℕ)
    (hH : 1 ≤ H) (hA : ∀ i j, (P.A i j).natAbs ≤ H)
    (hb : ∀ i, (P.b i).natAbs ≤ H)
    (hf : IsFeasible (toReal (rationalProgram P))) :
    ∃ z : Fin n → ℝ,
      (∀ e : Fin n → ℝ, e ⬝ᵥ e ≤ (((2 : ℝ) ^ ballExponent m n H)⁻¹) ^ 2 →
        (z + e) ⬝ᵥ (z + e) ≤ 1) ∧
      ∀ e : Fin n → ℝ, e ⬝ᵥ e ≤ (((2 : ℝ) ^ ballExponent m n H)⁻¹) ^ 2 →
        ∀ i, (∑ j, (normalizedMatrix P (outerScale n (coordinateCap m n H)) i j : ℝ) *
          (z + e) j) ≤ (normalizedBound P (1 / (precisionDenominator m n H : ℚ)) i : ℝ) := by
  let B := coordinateCap m n H
  let R := outerScale n B
  let D := precisionDenominator m n H
  let ε : ℝ := 1 / (D : ℝ)
  let r := ((2 : ℝ) ^ ballExponent m n H)⁻¹
  obtain ⟨x, hx, hxb⟩ := bounded_real_feasible_point P H hH hA hb hf
  let z := (R : ℝ)⁻¹ • x
  have hR : (0 : ℝ) < R := by exact_mod_cast outerScale_pos n B
  have hD : (0 : ℝ) < D := by exact_mod_cast precisionDenominator_pos m n H
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hHR : (0 : ℝ) ≤ H := by positivity
  have hAR : ∀ i j, |(toReal (rationalProgram P)).A i j| ≤ (H : ℝ) := by
    intro i j
    have h : ((P.A i j).natAbs : ℝ) ≤ (H : ℝ) := by exact_mod_cast hA i j
    simpa [toReal, rationalProgram, Nat.cast_natAbs, Int.cast_abs] using h
  have hrad : r ≤ cubeRadius n (H : ℝ) ε / (R : ℝ) := by
    have hid : cubeRadius n (H : ℝ) ε / (R : ℝ) = 1 / (ballDenominator m n H : ℝ) := by
      dsimp only [cubeRadius, ε]
      rw [div_div, div_div]
      congr 1
      simp only [ballDenominator, D, R, B, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_assoc]
    rw [hid]
    exact dyadic_radius_bound m n H
  refine ⟨z, ball_inside_unit z (scaled_point_norm x B hxb) r
    (by dsimp [r]; positivity) (dyadic_radius_small m n H), ?_⟩
  intro e he
  change e ⬝ᵥ e ≤ r ^ 2 at he
  have hrscale : (R : ℝ) * r ≤ cubeRadius n (H : ℝ) ε := by
    have h := (le_div_iff₀ hR).mp hrad
    simpa [mul_comm] using h
  have heR : ((R : ℝ) • e) ⬝ᵥ ((R : ℝ) • e) ≤ (cubeRadius n (H : ℝ) ε) ^ 2 := by
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
    have h := mul_le_mul_of_nonneg_left he (sq_nonneg (R : ℝ))
    have hrpos : 0 ≤ r := by dsimp [r]; positivity
    have hrhopos := (cubeRadius_bounds n (H : ℝ) ε hHR hε).1
    have hs : ((R : ℝ) * r) ^ 2 ≤ (cubeRadius n (H : ℝ) ε) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hR.le hrpos) hrscale 2
    nlinarith
  have hrelax := ball_in_relaxation (toReal (rationalProgram P)) (H : ℝ) ε
    hHR hε hAR x hx ((R : ℝ) • e) heR
  have hscale : (R : ℝ) • (z + e) = x + (R : ℝ) • e := by
    simp only [z, smul_add, smul_smul, mul_inv_cancel₀ (ne_of_gt hR), one_smul]
  apply (normalized_iff_relaxed P R (1 / (D : ℚ)) (z + e)).mpr
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, hscale] using hrelax

end Lax109476Proofs.NormalizedFeasibility

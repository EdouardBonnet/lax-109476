import Lax109476Proofs.EllipsoidCenter

/-! A uniform dyadic grid for both parts of the rational center update. -/

namespace Lax109476Proofs.EllipsoidPrecision

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter
open Lax109476.RationalCertificates

/-- This denominator has a linear bit length in the conditioning and accuracy exponents. -/
def gridDenominator (l s n : ℕ) : ℕ := 2 ^ (l + s + n + 3)

theorem gridDenominator_pos (l s n : ℕ) : 0 < gridDenominator l s n := by
  unfold gridDenominator
  positivity

theorem gridDenominator_size (l s n : ℕ) :
    Nat.size (gridDenominator l s n) = l + s + n + 4 := by
  unfold gridDenominator
  rw [Nat.size_pow]

/-- The chosen center grid also meets the relative shape-rounding condition. -/
theorem grid_shape_precision (l s n : ℕ) :
    2 * (n : ℝ) / (gridDenominator l s n : ℝ) ≤
      ((2 : ℝ) ^ s)⁻¹ * ((2 : ℝ) ^ l)⁻¹ := by
  have hp : (2 : ℝ) ^ (l + s + n + 1) ≤ (gridDenominator l s n : ℝ) := by
    unfold gridDenominator
    exact_mod_cast Nat.pow_le_pow_right (show 0 < 2 by decide)
      (show l + s + n + 1 ≤ l + s + n + 3 by omega)
  exact (div_le_div_of_nonneg_left (by positivity) (by positivity) hp).trans
    (dyadic_shape_precision l s n)

/-- The same dyadic denominator bounds both independent center errors. -/
theorem dyadic_center_precision (l s n : ℕ) :
    4 / (((gridDenominator l s n : ℕ) : ℝ) ^ 2 * ((2 : ℝ) ^ l)⁻¹) ≤
        (((2 : ℝ) ^ s)⁻¹) ^ 2 / 4 ∧
    (((2 : ℝ) ^ l)⁻¹)⁻¹ * ((n : ℝ) * (1 / (gridDenominator l s n : ℝ)) ^ 2) ≤
        (((2 : ℝ) ^ s)⁻¹) ^ 2 / 4 := by
  let L := (2 : ℝ) ^ l
  let S := (2 : ℝ) ^ s
  let N := (2 : ℝ) ^ (n + 3)
  have hL : 1 ≤ L := one_le_pow₀ (by norm_num)
  have hS : 0 < S := by dsimp [S]; positivity
  have hN : 8 ≤ N := by
    dsimp [N]
    rw [pow_add]
    norm_num only [show (2 : ℝ) ^ 3 = 8 by norm_num]
    have h := one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := n)
    linarith
  have hn : (n : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have hnN : 8 * (n : ℝ) ≤ N := by
    dsimp [N]
    rw [pow_add]
    norm_num only [show (2 : ℝ) ^ 3 = 8 by norm_num]
    nlinarith
  have hLN : N ^ 2 ≤ L * N ^ 2 := by
    simpa using mul_le_mul_of_nonneg_right hL (sq_nonneg N)
  have hid : (gridDenominator l s n : ℝ) = L * S * N := by
    simp only [gridDenominator, Nat.cast_pow, Nat.cast_ofNat]
    dsimp [L, S, N]
    rw [show l + s + n + 3 = l + s + (n + 3) by omega, pow_add, pow_add]
  have hLz : L ≠ 0 := by linarith
  have hSz : S ≠ 0 := ne_of_gt hS
  have hNz : N ≠ 0 := by linarith
  change 4 / ((gridDenominator l s n : ℝ) ^ 2 * L⁻¹) ≤ (S⁻¹) ^ 2 / 4 ∧
    (L⁻¹)⁻¹ * ((n : ℝ) * (1 / (gridDenominator l s n : ℝ)) ^ 2) ≤ (S⁻¹) ^ 2 / 4
  rw [hid, inv_inv]
  constructor
  · field_simp
    nlinarith only [hN, hLN]
  · field_simp
    nlinarith only [hN, hnN, hLN]

/-- A lower bound on the old shape yields one for the exact rational central-cut shape. -/
theorem exactCut_lower_bound (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : (realShape A).PosDef)
    (a : Fin n → ℚ) (ha : realVector a ≠ 0)
    (l : ℕ) (hbound : ∀ x : Fin n → ℝ,
      ((2 : ℝ) ^ l)⁻¹ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (realShape A *ᵥ x))
    (x : Fin n → ℝ) :
    ((2 : ℝ) ^ (l + 2))⁻¹ * (x ⬝ᵥ x) ≤
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x) := by
  have he : ((2 : ℝ) ^ (l + 2))⁻¹ = (1 / 4 : ℝ) * ((2 : ℝ) ^ l)⁻¹ := by
    rw [pow_add]
    norm_num
  rw [he]
  calc
    _ = (1 / 4 : ℝ) * (((2 : ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)) := by ring
    _ ≤ (1 / 4 : ℝ) * (x ⬝ᵥ (realShape A *ᵥ x)) :=
      mul_le_mul_of_nonneg_left (hbound x) (by norm_num)
    _ ≤ x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x) := by
      rw [realShape_cutShape]
      exact (realCutShape_coarse_bounds n hn (realShape A) hA (realVector a) x ha).1

/-- The diagonal rounding allowance preserves the new lower shape bound. -/
theorem cut_lower_bound (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : (realShape A).PosDef)
    (a : Fin n → ℚ) (ha : realVector a ≠ 0) (D : ℕ) (hD : 0 < D)
    (l : ℕ) (hbound : ∀ x : Fin n → ℝ,
      ((2 : ℝ) ^ l)⁻¹ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (realShape A *ᵥ x))
    (x : Fin n → ℝ) :
    ((2 : ℝ) ^ (l + 2))⁻¹ * (x ⬝ᵥ x) ≤
      x ⬝ᵥ (realShape (roundedShape (cutShape n A a) D) *ᵥ x) :=
  (exactCut_lower_bound n hn A hA a ha l hbound x).trans
    (roundedShape_sandwich (cutShape n A a) D hD x).1

/-- A fixed dyadic grid automatically meets both center precision conditions.
An integer nonzero cut normal satisfies the assumed unit lower bound on its squared length. -/
theorem uniform_roundedStep_contains (n : ℕ) (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : (realShape A).PosDef)
    (a c : Fin n → ℚ) (hanorm : 1 ≤ realVector a ⬝ᵥ realVector a)
    (l s : ℕ) (hbound : ∀ x : Fin n → ℝ,
      ((2 : ℝ) ^ l)⁻¹ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (realShape A *ᵥ x))
    (x : Fin n → ℝ)
    (hx : (x - realVector c) ⬝ᵥ ((realShape A)⁻¹ *ᵥ (x - realVector c)) ≤ 1)
    (hcut : realVector a ⬝ᵥ (x - realVector c) ≤ 0) :
    let D := gridDenominator (l + 2) s n
    let η : ℚ := 1 / (2 : ℚ) ^ s
    (x - realVector (roundedCenter n A a c D)) ⬝ᵥ
      ((realShape (roundedStepShape n A a D η))⁻¹ *ᵥ
        (x - realVector (roundedCenter n A a c D))) ≤ 1 := by
  let D := gridDenominator (l + 2) s n
  let η : ℚ := 1 / (2 : ℚ) ^ s
  let lowerBound := ((2 : ℝ) ^ (l + 2))⁻¹
  have hD : 0 < D := gridDenominator_pos _ _ _
  have hη : 0 < η := by dsimp [η]; positivity
  have hl : 0 < lowerBound := by dsimp [lowerBound]; positivity
  have hcast : (η : ℝ) = ((2 : ℝ) ^ s)⁻¹ := by simp [η]
  have ha : realVector a ≠ 0 := by
    intro h
    rw [h, dotProduct_zero] at hanorm
    norm_num at hanorm
  have hlower := cut_lower_bound n hn A hA a ha D hD l hbound
  have hq : lowerBound ≤ realVector a ⬝ᵥ (realShape A *ᵥ realVector a) := by
    have he : lowerBound = (1 / 4 : ℝ) * ((2 : ℝ) ^ l)⁻¹ := by
      dsimp [lowerBound]
      rw [pow_add]
      norm_num
    have hp : 0 ≤ ((2 : ℝ) ^ l)⁻¹ := by positivity
    have h := hbound (realVector a)
    have h' := mul_le_mul_of_nonneg_left hanorm hp
    rw [he]
    nlinarith only [h, h', hp]
  have hprec := dyadic_center_precision (l + 2) s n
  have hsqrt : 4 / ((n : ℝ) ^ 2 * (D : ℝ) ^ 2 *
      (realVector a ⬝ᵥ (realShape A *ᵥ realVector a))) ≤ (η : ℝ) ^ 2 / 4 := by
    rw [hcast]
    apply le_trans _ hprec.1
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn₂ : 1 ≤ (n : ℝ) ^ 2 := by nlinarith
    have hprod := mul_le_mul_of_nonneg_left hq (sq_nonneg (D : ℝ))
    have hqp : 0 ≤ realVector a ⬝ᵥ (realShape A *ᵥ realVector a) := by linarith
    have h := mul_le_mul_of_nonneg_right hn₂
      (mul_nonneg (sq_nonneg (D : ℝ)) hqp)
    nlinarith only [hprod, h]
  apply roundedStep_contains n hn A hA a c ha D hD lowerBound hl η hη hlower hsqrt
  · simpa only [hcast] using hprec.2
  · exact hx
  · exact hcut

end Lax109476Proofs.EllipsoidPrecision

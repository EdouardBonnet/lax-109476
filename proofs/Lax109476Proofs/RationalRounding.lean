import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Size
import Mathlib.Analysis.Real.Sqrt
import Lax109476.RationalEncoding
import Mathlib.Tactic

/-!
Computable rational rounding primitives with real error guarantees and grid
encoding bounds. These do not yet supply a RAM implementation.
-/

namespace Lax109476Proofs.RationalRounding

/-- Round to the grid with denominator `D`, towards minus infinity. -/
def roundDown (q : ℚ) (D : ℕ) : ℚ := (Int.floor (q * D) : ℚ) / D

/-- A rational upper approximation to a square root using integer square root. -/
def sqrtUpper (q : ℚ) (D : ℕ) : ℚ :=
  ((Nat.sqrt (Nat.ceil (q * (D : ℚ) ^ 2)) + 1 : ℕ) : ℚ) / D

/-- Reducing a grid rational can only reduce its numerator and denominator. -/
theorem grid_num_den_bound (k : ℤ) (D : ℕ) (hD : 0 < D) :
    ((k : ℚ) / D).num.natAbs ≤ k.natAbs ∧ ((k : ℚ) / D).den ≤ D := by
  obtain ⟨c, hnum, hden⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den k
    (d := (D : ℤ)) (by exact_mod_cast ne_of_gt hD)
  have hc : c ≠ 0 := by
    intro h
    rw [h, zero_mul] at hden
    have hDn : (D : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt hD
    exact hDn hden
  have hcpos : 0 < c.natAbs := Int.natAbs_pos.mpr hc
  have hnumAbs : k.natAbs = c.natAbs * ((k : ℚ) / D).num.natAbs := by
    simpa only [Int.natAbs_mul, Int.cast_natCast] using congrArg Int.natAbs hnum
  have hdenAbs : D = c.natAbs * ((k : ℚ) / D).den := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast, Int.cast_natCast] using
      congrArg Int.natAbs hden
  constructor
  · calc
      _ ≤ c.natAbs * ((k : ℚ) / D).num.natAbs := Nat.le_mul_of_pos_left _ hcpos
      _ = _ := hnumAbs.symm
  · calc
      _ ≤ c.natAbs * ((k : ℚ) / D).den := Nat.le_mul_of_pos_left _ hcpos
      _ = _ := hdenAbs.symm

/-- Grid rationals have an encoding bounded by the integer numerator and grid size. -/
theorem grid_encoding_bound (k : ℤ) (D : ℕ) (hD : 0 < D) :
    Lax759944.BinaryWordEncoding.bitSize
      (Lax109476.RationalEncoding.encodeRational ((k : ℚ) / D)) ≤
        4 + Nat.size k.natAbs + Nat.size D := by
  obtain ⟨hnum, hden⟩ := grid_num_den_bound k D hD
  have hnsize := Nat.size_le_size hnum
  have hdsize := Nat.size_le_size hden
  unfold Lax759944.BinaryWordEncoding.bitSize Lax759944.BinaryWordEncoding.encode
    Lax759944.BinaryWordEncoding.encodeNat Lax109476.RationalEncoding.encodeRational
  split_ifs <;> simp [Nat.size_eq_bits_len] <;> omega

private theorem size_mul_le (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  apply Nat.size_le.mpr
  rw [pow_add]
  calc
    _ ≤ 2 ^ Nat.size a * b := Nat.mul_le_mul_right b (Nat.le_of_lt (Nat.lt_size_self a))
    _ < _ := Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self b) (by positivity)

private theorem size_add_one_le (a : ℕ) : Nat.size (a + 1) ≤ Nat.size a + 1 := by
  apply Nat.size_le.mpr
  rw [pow_succ]
  have h := Nat.lt_size_self a
  have hp : 0 < 2 ^ Nat.size a := by positivity
  omega

private theorem abs_le_num (q : ℚ) : |q| ≤ (q.num.natAbs : ℚ) := by
  have hden : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have hden₁ : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
  have hnum : (q.num.natAbs : ℚ) = |(q.num : ℚ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  conv_lhs => rw [← q.num_div_den]
  rw [abs_div, abs_of_nonneg (le_of_lt hden), ← hnum]
  apply (div_le_iff₀ hden).mpr
  simpa using mul_le_mul_of_nonneg_left hden₁ (Nat.cast_nonneg q.num.natAbs)

/-- A magnitude bound controls the grid numerator independently of the input denominator. -/
theorem roundDown_floor_magnitude_bound (q : ℚ) (M D : ℕ) (hq : |q| ≤ M) :
    (Int.floor (q * D)).natAbs ≤ M * D + 1 := by
  let k := Int.floor (q * D)
  have hab := abs_le.mp hq
  have hD : (0 : ℚ) ≤ D := Nat.cast_nonneg _
  have hupper := mul_le_mul_of_nonneg_right hab.2 hD
  have hlower := mul_le_mul_of_nonneg_right hab.1 hD
  have hfloor : (k : ℚ) ≤ q * D := Int.floor_le _
  have hfloor' : q * D < (k : ℚ) + 1 := Int.lt_floor_add_one _
  have hk : |(k : ℚ)| ≤ (M : ℚ) * D + 1 := by
    apply abs_le.mpr
    constructor <;> linarith
  have hk' : (k.natAbs : ℚ) ≤ ((M * D + 1 : ℕ) : ℚ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs, Nat.cast_add, Nat.cast_mul,
      Nat.cast_one] using hk
  exact Nat.cast_le.mp hk'

/-- The integer numerator before grid reduction has a polynomial bit bound. -/
theorem roundDown_floor_bound (q : ℚ) (D : ℕ) :
    (Int.floor (q * D)).natAbs ≤ q.num.natAbs * D + 1 :=
  roundDown_floor_magnitude_bound q q.num.natAbs D (abs_le_num q)

/-- Rounding restores a size bound depending only on magnitude and grid precision. -/
theorem roundDown_encoding_magnitude_bound (q : ℚ) (M D : ℕ) (hD : 0 < D)
    (hq : |q| ≤ M) :
    Lax759944.BinaryWordEncoding.bitSize
      (Lax109476.RationalEncoding.encodeRational (roundDown q D)) ≤
        5 + Nat.size M + 2 * Nat.size D := by
  have hgrid := grid_encoding_bound (Int.floor (q * D)) D hD
  have hfloor := Nat.size_le_size (roundDown_floor_magnitude_bound q M D hq)
  have h₁ := size_add_one_le (M * D)
  have h₂ := size_mul_le M D
  unfold roundDown
  omega

/-- The encoded rounded rational uses linearly many bits in numerator and precision size. -/
theorem roundDown_encoding_bound (q : ℚ) (D : ℕ) (hD : 0 < D) :
    Lax759944.BinaryWordEncoding.bitSize
      (Lax109476.RationalEncoding.encodeRational (roundDown q D)) ≤
        5 + Nat.size q.num.natAbs + 2 * Nat.size D := by
  exact roundDown_encoding_magnitude_bound q q.num.natAbs D hD (abs_le_num q)

/-- Integer square-root rounding also has a linear encoding-size bound. -/
theorem sqrtUpper_encoding_bound (q : ℚ) (D : ℕ) (hD : 0 < D) :
    Lax759944.BinaryWordEncoding.bitSize
      (Lax109476.RationalEncoding.encodeRational (sqrtUpper q D)) ≤
        5 + Nat.size q.num.natAbs + 3 * Nat.size D := by
  let c := Nat.ceil (q * (D : ℚ) ^ 2)
  let s := Nat.sqrt c
  have hq : q ≤ (q.num.natAbs : ℚ) := (le_abs_self q).trans (abs_le_num q)
  have hc : c ≤ q.num.natAbs * (D * D) := by
    apply Nat.ceil_le.mpr
    simpa only [Nat.cast_mul, pow_two] using
      mul_le_mul_of_nonneg_right hq (sq_nonneg (D : ℚ))
  have hs : s ≤ c := Nat.sqrt_le_self c
  have hsize := Nat.size_le_size (Nat.add_le_add_right (hs.trans hc) 1)
  have h₁ := size_add_one_le (q.num.natAbs * (D * D))
  have h₂ := size_mul_le q.num.natAbs (D * D)
  have h₃ := size_mul_le D D
  have hgrid := grid_encoding_bound ((s + 1 : ℕ) : ℤ) D hD
  simp only [Int.natAbs_natCast, Int.cast_natCast] at hgrid
  change Lax759944.BinaryWordEncoding.bitSize
    (Lax109476.RationalEncoding.encodeRational (sqrtUpper q D)) ≤
      4 + Nat.size (s + 1) + Nat.size D at hgrid
  omega

theorem roundDown_le (q : ℚ) (D : ℕ) (hD : 0 < D) : roundDown q D ≤ q := by
  unfold roundDown
  apply (div_le_iff₀ (by exact_mod_cast hD)).mpr
  exact Int.floor_le _

theorem lt_roundDown_add (q : ℚ) (D : ℕ) (hD : 0 < D) :
    q < roundDown q D + 1 / D := by
  have hp : (0 : ℚ) < D := by exact_mod_cast hD
  unfold roundDown
  rw [← add_div, lt_div_iff₀ hp]
  exact Int.lt_floor_add_one _

/-- The grid error is less than one grid spacing, including negative inputs. -/
theorem roundDown_error (q : ℚ) (D : ℕ) (hD : 0 < D) :
    0 ≤ (q : ℝ) - (roundDown q D : ℝ) ∧
      (q : ℝ) - (roundDown q D : ℝ) < 1 / (D : ℝ) := by
  have h₁ : (roundDown q D : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast roundDown_le q D hD
  have h₂ : (q : ℝ) < (roundDown q D : ℝ) + 1 / (D : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (lt_roundDown_add q D hD)
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using h
  constructor <;> linarith

/-- Coordinatewise grid rounding has a dimension-controlled squared error. -/
theorem roundDown_vector_error (n : ℕ) (x : Fin n → ℚ) (D : ℕ) (hD : 0 < D) :
    (∑ i, ((x i : ℝ) - (roundDown (x i) D : ℝ)) ^ 2) ≤
      (n : ℝ) * (1 / (D : ℝ)) ^ 2 := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  calc
    _ ≤ ∑ _i : Fin n, (1 / (D : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      obtain ⟨h₁, h₂⟩ := roundDown_error (x i) D hD
      nlinarith [show (0 : ℝ) < 1 / (D : ℝ) by positivity]
    _ = _ := by simp

/-- The computed square-root approximation has additive error less than `2 / D`. -/
theorem sqrtUpper_bounds (q : ℚ) (hq : 0 ≤ q) (D : ℕ) (hD : 0 < D) :
    Real.sqrt (q : ℝ) ≤ (sqrtUpper q D : ℝ) ∧
      (sqrtUpper q D : ℝ) < Real.sqrt (q : ℝ) + 2 / (D : ℝ) := by
  let c := Nat.ceil (q * (D : ℚ) ^ 2)
  let s := Nat.sqrt c
  have hqR : (0 : ℝ) ≤ q := by exact_mod_cast hq
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hcl : (q : ℝ) * (D : ℝ) ^ 2 ≤ c := by
    have h : q * (D : ℚ) ^ 2 ≤ (c : ℚ) := Nat.le_ceil _
    have h' := (Rat.cast_le (K := ℝ)).mpr h
    simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast] using h'
  have hcu : (c : ℝ) < (q : ℝ) * (D : ℝ) ^ 2 + 1 := by
    have h : (c : ℚ) < q * (D : ℚ) ^ 2 + 1 :=
      Nat.ceil_lt_add_one (show (0 : ℚ) ≤ q * (D : ℚ) ^ 2 by positivity)
    have h' := (Rat.cast_lt (K := ℝ)).mpr h
    simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
      Rat.cast_one] using h'
  have hsl : (s : ℝ) ^ 2 ≤ c := by
    have h : s ^ 2 ≤ c := Nat.sqrt_le' c
    have h' := (Nat.cast_le (α := ℝ)).mpr h
    simpa only [Nat.cast_pow] using h'
  have hsu : (c : ℝ) < ((s : ℝ) + 1) ^ 2 := by
    have h : c < (s + 1) ^ 2 := Nat.lt_succ_sqrt' c
    have h' := (Nat.cast_lt (α := ℝ)).mpr h
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using h'
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hroot := Real.sq_sqrt hqR
  have hrootpos := Real.sqrt_nonneg (q : ℝ)
  have hsqr : (Real.sqrt (q : ℝ) * (D : ℝ)) ^ 2 = (q : ℝ) * (D : ℝ) ^ 2 := by
    rw [mul_pow, hroot]
  have hl : Real.sqrt (q : ℝ) * D ≤ (s : ℝ) + 1 := by
    have ht : 0 ≤ Real.sqrt (q : ℝ) * (D : ℝ) := mul_nonneg hrootpos (le_of_lt hDR)
    nlinarith only [hcl, hsu, hsqr, ht, hs]
  have hu : (s : ℝ) + 1 < Real.sqrt (q : ℝ) * D + 2 := by
    have ht : 0 ≤ Real.sqrt (q : ℝ) * (D : ℝ) := mul_nonneg hrootpos (le_of_lt hDR)
    nlinarith only [hsl, hcu, hsqr, ht, hs,
      sq_nonneg ((s : ℝ) - Real.sqrt (q : ℝ) * D)]
  have heq : (sqrtUpper q D : ℝ) = ((s : ℝ) + 1) / D := by
    simp [sqrtUpper, c, s]
  rw [heq]
  constructor
  · exact (le_div_iff₀ hDR).mpr hl
  · calc
      _ < (Real.sqrt (q : ℝ) * D + 2) / D :=
        (div_lt_div_iff_of_pos_right hDR).mpr hu
      _ = _ := by field_simp

end Lax109476Proofs.RationalRounding

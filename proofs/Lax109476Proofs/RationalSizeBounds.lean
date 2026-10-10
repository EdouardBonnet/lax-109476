import Lax109476Proofs.SmallFeasiblePoint
import Mathlib.Tactic

open scoped BigOperators Matrix

namespace Lax109476Proofs.RationalSizeBounds

variable {ι : Type*} [Fintype ι]

/-- A common denominator obtained without factorization. -/
def commonDenominator (q : ι → ℚ) : ℕ := ∏ i, (q i).den

theorem commonDenominator_pos (q : ι → ℚ) : 0 < commonDenominator q := by
  exact Finset.prod_pos (fun i _ => (q i).den_pos)

theorem denominator_dvd (q : ι → ℚ) (i : ι) : (q i).den ∣ commonDenominator q := by
  classical
  exact Finset.dvd_prod_of_mem (fun i => (q i).den) (Finset.mem_univ i)

def clearedNumerator (q : ι → ℚ) (i : ι) : ℤ :=
  (q i).num * (commonDenominator q / (q i).den : ℕ)

/-- Clearing a family of denominators gives exactly the original coefficients
multiplied by one positive integer. -/
theorem clearedNumerator_cast (q : ι → ℚ) (i : ι) :
    (clearedNumerator q i : ℚ) = (commonDenominator q : ℚ) * q i := by
  have hdiv : (commonDenominator q : ℚ) =
      (commonDenominator q / (q i).den : ℕ) * ((q i).den : ℚ) := by
    exact_mod_cast (Nat.div_mul_cancel (denominator_dvd q i)).symm
  rw [clearedNumerator, Int.cast_mul, Int.cast_natCast]
  conv_rhs => rw [← (q i).num_div_den, hdiv]
  have hd : ((q i).den : ℚ) ≠ 0 := by exact_mod_cast (q i).den_ne_zero
  field_simp

theorem clearedNumerator_bound (q : ι → ℚ) (i : ι) :
    (clearedNumerator q i).natAbs ≤ (q i).num.natAbs * commonDenominator q := by
  simp only [clearedNumerator, Int.natAbs_mul, Int.natAbs_natCast]
  exact Nat.mul_le_mul_left _ (Nat.div_le_self _ _)

omit [Fintype ι] in
theorem product_le_two_pow_sum_size (s : Finset ι) (f : ι → ℕ) :
    (∏ i ∈ s, f i) ≤ 2 ^ (∑ i ∈ s, Nat.size (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, pow_add]
    exact Nat.mul_le_mul (Nat.lt_size_self (f i)).le ih

/-- The logarithm of the denominator product is bounded by the sum of encoded
denominator lengths, rather than by their number times their maximum length. -/
theorem commonDenominator_bound (q : ι → ℚ) :
    commonDenominator q ≤ 2 ^ (∑ i, Nat.size (q i).den) :=
  product_le_two_pow_sum_size Finset.univ (fun i => (q i).den)

theorem size_mul_le (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact (Nat.mul_le_mul_right b (Nat.lt_size_self a).le).trans_lt
    (Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self b) (by positivity))

theorem size_pow_le (a k : ℕ) : Nat.size (a ^ k) ≤ k * Nat.size a + 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := size_mul_le (a ^ k) a
    rw [pow_succ, Nat.succ_mul]
    omega

theorem size_factorial_le (k : ℕ) : Nat.size k.factorial ≤ k * Nat.size k + 1 :=
  (Nat.size_le_size (Nat.factorial_le_pow k)).trans (size_pow_le k k)

theorem size_add_one_le (a : ℕ) : Nat.size (a + 1) ≤ Nat.size a + 1 := by
  apply Nat.size_le.mpr
  rw [pow_succ]
  have h := Nat.lt_size_self a
  have hp : 0 < 2 ^ Nat.size a := by positivity
  omega

theorem size_add_le (a b : ℕ) : Nat.size (a + b) ≤ Nat.size a + Nat.size b + 1 := by
  apply Nat.size_le.mpr
  rw [pow_succ, pow_add]
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  have hpa : 0 < 2 ^ Nat.size a := by positivity
  have hpb : 0 < 2 ^ Nat.size b := by positivity
  have h₁ := Nat.le_mul_of_pos_right (2 ^ Nat.size a) hpb
  have h₂ := Nat.le_mul_of_pos_left (2 ^ Nat.size b) hpa
  omega

theorem size_le_self (a : ℕ) : Nat.size a ≤ a :=
  Nat.size_le.mpr (Nat.lt_two_pow_self (n := a))

/-- The common cap used by all three certificates has quadratically many bits
when the dimension and cleared coefficient bounds come from an input of size L. -/
theorem certificate_cap_size (K L : ℕ) (hK : K ≤ 2 * (L + 1)) :
    Nat.size (K.factorial * (K * (2 ^ (2 * L)) ^ 2 + 1) ^ K) ≤
      32 * (L + 1) ^ 2 := by
  let H := 2 ^ (2 * L)
  let B := K * H ^ 2 + 1
  have hH : Nat.size H = 2 * L + 1 := Nat.size_pow
  have hmul := size_mul_le K (H ^ 2)
  have hpow := size_pow_le H 2
  have hadd := size_add_one_le (K * H ^ 2)
  have hks := (size_le_self K).trans hK
  have hbs : Nat.size B ≤ 6 * (L + 1) := by
    dsimp [B]
    omega
  have hf := size_factorial_le K
  have hp := size_pow_le B K
  have ht := size_mul_le K.factorial (B ^ K)
  have h₁ : K * Nat.size K ≤ 4 * (L + 1) ^ 2 := by
    nlinarith [Nat.mul_le_mul hK hks]
  have h₂ : K * Nat.size B ≤ 12 * (L + 1) ^ 2 := by
    nlinarith [Nat.mul_le_mul hK hbs]
  change Nat.size (K.factorial * B ^ K) ≤ _
  nlinarith [sq_nonneg (L : ℤ)]

/-- Determinant magnitude bounds yield a polynomial coordinate bit bound. -/
theorem determinant_size_bound (k r H : ℕ) :
    Nat.size (k.factorial * (r * H ^ 2 + 1) ^ k) ≤
      k * Nat.size k + k * Nat.size (r * H ^ 2 + 1) + 2 := by
  have h₁ := size_mul_le k.factorial ((r * H ^ 2 + 1) ^ k)
  have h₂ := size_factorial_le k
  have h₃ := size_pow_le (r * H ^ 2 + 1) k
  omega

end Lax109476Proofs.RationalSizeBounds

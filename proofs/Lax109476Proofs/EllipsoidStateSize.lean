import Lax109476Proofs.EllipsoidSequence
import Lax109476Proofs.RationalSizeBounds
import Lax109476Proofs.EncodingSize

open scoped BigOperators

namespace Lax109476Proofs.EllipsoidStateSize

open Matrix EllipsoidBounds EllipsoidRounding EllipsoidCenter EllipsoidPrecision
open EllipsoidIteration EllipsoidSequence RationalRounding RationalSizeBounds
open Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding

theorem entry_bound_of_form {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (M : ℝ) (hM : 0 ≤ M)
    (hupper : ∀ x, x ⬝ᵥ (A *ᵥ x) ≤ M * (x ⬝ᵥ x)) (i j : Fin n) :
    |A i j| ≤ M := by
  let e : Fin n → Fin n → ℝ := fun k => Pi.single k 1
  have hne : e j ≠ 0 := by
    intro h
    have hh := congrFun h j
    simp [e] at hh
  have hcs := form_cauchy_schwarz hA (e j) (e i) hne
  have hi := hupper (e i)
  have hj := hupper (e j)
  have hip := hA.posSemidef.dotProduct_mulVec_nonneg (e i)
  have hjp := hA.posSemidef.dotProduct_mulVec_nonneg (e j)
  simp [e, Matrix.mulVec, dotProduct, Pi.single_apply] at hcs hi hj hip hjp
  have hp : A j j * A i i ≤ M * M := mul_le_mul hj hi hip hM
  have hs : (A i j) ^ 2 ≤ M ^ 2 := by nlinarith only [hcs, hp]
  exact (sq_le_sq₀ (abs_nonneg _) hM).mp (by simpa only [sq_abs] using hs)

theorem shapes_entry_magnitude (n : ℕ) (hn : 2 ≤ n) (a : ℕ → Fin n → ℚ)
    (ha : ∀ k, 1 ≤ realVector (a k) ⬝ᵥ realVector (a k))
    (k : ℕ) (i j : Fin n) : |(shapes n a k i j : ℝ)| ≤ (4 : ℝ) ^ k := by
  have h := shapes_invariant n hn a ha k
  exact entry_bound_of_form h.1 _ (by positivity) (fun x => (h.2 x).2) i j

theorem approximateCenter_displacement (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : (realShape A).PosDef)
    (a c : Fin n → ℚ) (ha : realVector a ≠ 0) (D : ℕ) (hD : 0 < D)
    (M : ℝ) (hM : 0 ≤ M)
    (hupper : ∀ x, x ⬝ᵥ (realShape A *ᵥ x) ≤ M ^ 2 * (x ⬝ᵥ x)) (i : Fin n) :
    |(approximateCenter n A a c D i : ℝ) - (c i : ℝ)| ≤ M := by
  let q := realVector a ⬝ᵥ (realShape A *ᵥ realVector a)
  let r : ℝ := sqrtUpper (a ⬝ᵥ (A *ᵥ a)) D
  let t := (realShape A *ᵥ realVector a) i
  have hq : 0 < q := hA.dotProduct_mulVec_pos ha
  have hqRat : 0 ≤ a ⬝ᵥ (A *ᵥ a) := by
    apply (Rat.cast_nonneg (K := ℝ)).mp
    rw [cast_direction_form]
    exact hq.le
  have hr : Real.sqrt q ≤ r := by
    simpa only [cast_direction_form] using (sqrtUpper_bounds _ hqRat D hD).1
  have hrp : 0 < r := (Real.sqrt_pos.mpr hq).trans_le hr
  have hrsq : q ≤ r ^ 2 := by nlinarith [Real.sqrt_nonneg q, Real.sq_sqrt hq.le]
  have hcs' := form_cauchy_schwarz hA (realVector a) (Pi.single i 1) ha
  have hii := hupper (Pi.single i 1)
  simp [single_dotProduct, dotProduct_single] at hcs' hii
  have ht : t ^ 2 ≤ r ^ 2 * M ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hii hq.le
    have hmul' := mul_le_mul_of_nonneg_right hrsq (sq_nonneg M)
    dsimp [q, t] at *
    nlinarith only [hcs', hmul, hmul']
  have hab : |t| ≤ r * M :=
    (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hrp.le hM)).mp (by
      simpa only [sq_abs, mul_pow] using ht)
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  have hden : 0 < ((n : ℝ) + 1) * r := by positivity
  have hb : |t / (((n : ℝ) + 1) * r)| ≤ M := by
    rw [abs_div, abs_of_pos hden]
    apply (div_le_iff₀ hden).mpr
    exact hab.trans (by nlinarith [mul_nonneg hrp.le hM])
  have he : (approximateCenter n A a c D i : ℝ) - (c i : ℝ) =
      -(t / (((n : ℝ) + 1) * r)) := by
    simp [approximateCenter, realShape, realVector, Matrix.mulVec, dotProduct,
      Rat.cast_sum, r, t, smul_eq_mul, div_eq_mul_inv, _root_.mul_inv_rev]
    ring
  rw [he, abs_neg]
  exact hb

theorem roundedCenter_displacement (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) (hA : (realShape A).PosDef)
    (a c : Fin n → ℚ) (ha : realVector a ≠ 0) (D : ℕ) (hD : 0 < D)
    (M : ℝ) (hM : 0 ≤ M)
    (hupper : ∀ x, x ⬝ᵥ (realShape A *ᵥ x) ≤ M ^ 2 * (x ⬝ᵥ x)) (i : Fin n) :
    |(roundedCenter n A a c D i : ℝ) - (c i : ℝ)| ≤ M + 1 := by
  have h := approximateCenter_displacement n A hA a c ha D hD M hM hupper i
  have he := roundDown_error (approximateCenter n A a c D i) D hD
  have hi : (1 : ℝ) / D ≤ 1 := by
    apply (div_le_one (by exact_mod_cast hD)).mpr
    exact_mod_cast hD
  have hround : |(roundedCenter n A a c D i : ℝ) -
      (approximateCenter n A a c D i : ℝ)| ≤ 1 := by
    change |(roundDown (approximateCenter n A a c D i) D : ℝ) - _| ≤ _
    rw [abs_sub_comm, abs_of_nonneg he.1]
    exact he.2.le.trans hi
  calc
    _ ≤ |(roundedCenter n A a c D i : ℝ) - (approximateCenter n A a c D i : ℝ)| +
      |(approximateCenter n A a c D i : ℝ) - (c i : ℝ)| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add hround h |>.trans_eq (add_comm _ _)

theorem centers_magnitude (n : ℕ) (hn : 2 ≤ n) (a : ℕ → Fin n → ℚ)
    (ha : ∀ k, 1 ≤ realVector (a k) ⬝ᵥ realVector (a k))
    (k : ℕ) (i : Fin n) : |(centers n a 0 k i : ℝ)| ≤ (2 : ℝ) ^ (k + 2) := by
  induction k with
  | zero => simp [centers]
  | succ k ih =>
    have h := shapes_invariant n hn a ha k
    have hne : realVector (a k) ≠ 0 := by
      intro he
      have hh := ha k
      rw [he, dotProduct_zero] at hh
      norm_num at hh
    have hp : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
    have hd := roundedCenter_displacement n (shapes n a k) h.1 (a k)
      (centers n a 0 k) hne (gridDenominator (2 * k + 2) (2 * n + 4) n)
      (gridDenominator_pos _ _ _) ((2 : ℝ) ^ k)
      (by positivity) (fun x => by rw [← hp]; exact (h.2 x).2) i
    change |(roundedCenter n (shapes n a k) (a k) (centers n a 0 k)
      (gridDenominator (2 * k + 2) (2 * n + 4) n) i : ℝ)| ≤ _
    have hab := abs_sub_le (roundedCenter n (shapes n a k) (a k) (centers n a 0 k)
      (gridDenominator (2 * k + 2) (2 * n + 4) n) i : ℝ)
      (centers n a 0 k i : ℝ) 0
    simp only [sub_zero] at hab
    have hpow : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    rw [show k + 1 + 2 = k + 3 by omega, pow_add]
    rw [show k + 2 = k + 2 by rfl, pow_add] at ih
    norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num,
      show (2 : ℝ) ^ 3 = 8 by norm_num] at *
    linarith

def shapeGrid (n k : ℕ) : ℕ :=
  gridDenominator (2 * k + 2) (2 * n + 4) n * (2 ^ (2 * n + 4)) ^ 2

theorem shapeGrid_pos (n k : ℕ) : 0 < shapeGrid n k := by
  unfold shapeGrid
  exact Nat.mul_pos (gridDenominator_pos _ _ _) (by positivity)

theorem shapeGrid_size (n k : ℕ) : (shapeGrid n k).size = 2 * k + 7 * n + 18 := by
  unfold shapeGrid gridDenominator
  rw [← pow_mul, ← pow_add, Nat.size_pow]
  omega

theorem stored_shape_grid (n k : ℕ) (A : Matrix (Fin n) (Fin n) ℚ)
    (a : Fin n → ℚ) (i j : Fin n) :
    ∃ z : ℤ, roundedStepShape n A a
      (gridDenominator (2 * k + 2) (2 * n + 4) n) (stepAccuracy n) i j =
        (z : ℚ) / (shapeGrid n k : ℕ) := by
  let D := gridDenominator (2 * k + 2) (2 * n + 4) n
  let S := 2 ^ (2 * n + 4)
  refine ⟨((S : ℤ) + 1) ^ 2 *
    (Int.floor (cutShape n A a i j * D) + if i = j then (n : ℤ) else 0), ?_⟩
  have hD : (D : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt (gridDenominator_pos _ _ _)
  have hS : (S : ℚ) ≠ 0 := by dsimp [S]; positivity
  simp only [roundedStepShape, roundedShape, stepAccuracy, Matrix.smul_apply,
    Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, smul_eq_mul,
    roundDown, Int.cast_mul, Int.cast_pow, Int.cast_add, Int.cast_natCast,
    Int.cast_one, Int.cast_ite, Int.cast_zero, shapeGrid, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat]
  have hScast : (2 : ℚ) ^ (2 * n + 4) = (S : ℚ) := by simp [S]
  rw [hScast]
  change ((1 + 1 / (S : ℚ)) ^ 2) *
    ((Int.floor (cutShape n A a i j * D) : ℚ) / D +
      (n : ℚ) / D * (if i = j then 1 else 0)) =
        (((S : ℚ) + 1) ^ 2 *
          ((Int.floor (cutShape n A a i j * D) : ℚ) + if i = j then (n : ℚ) else 0)) /
          ((D : ℚ) * (S : ℚ) ^ 2)
  split_ifs <;> field_simp <;> ring

theorem shapes_denominator (n : ℕ) (a : ℕ → Fin n → ℚ) (k : ℕ) (i j : Fin n) :
    (shapes n a (k + 1) i j).den ≤ shapeGrid n k := by
  obtain ⟨z, hz⟩ := stored_shape_grid n k (shapes n a k) (a k) i j
  change (roundedStepShape n (shapes n a k) (a k) _ _ i j).den ≤ _
  rw [hz]
  exact (grid_num_den_bound z _ (shapeGrid_pos n k)).2

theorem numerator_bound_of_magnitude (q : ℚ) (M D : ℕ)
    (hm : |(q : ℝ)| ≤ M) (hd : q.den ≤ D) : q.num.natAbs ≤ M * D := by
  have hnum : (q.num.natAbs : ℝ) = |(q : ℝ)| * (q.den : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    have he := congrArg (fun r : ℚ => (r : ℝ)) q.mul_den_eq_num
    simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast] at he
    rw [← he, abs_mul, abs_of_nonneg (a := (q.den : ℝ)) (Nat.cast_nonneg _)]
  have hdR : (q.den : ℝ) ≤ D := by exact_mod_cast hd
  have h := mul_le_mul hm hdR (Nat.cast_nonneg _) (Nat.cast_nonneg M)
  rw [← hnum] at h
  exact_mod_cast h

theorem encoding_bound_of_magnitude (q : ℚ) (M D : ℕ)
    (hm : |(q : ℝ)| ≤ M) (hd : q.den ≤ D) :
    bitSize (encodeRational q) ≤ 4 + M.size + 2 * D.size := by
  have hn := Nat.size_le_size (numerator_bound_of_magnitude q M D hm hd)
  have hmul := size_mul_le M D
  have hds := Nat.size_le_size hd
  have he := EncodingSize.rational_size_upper q
  omega

theorem shapes_encoding_size (n : ℕ) (hn : 2 ≤ n) (a : ℕ → Fin n → ℚ)
    (ha : ∀ k, 1 ≤ realVector (a k) ⬝ᵥ realVector (a k)) (k : ℕ) (i j : Fin n) :
    bitSize (encodeRational (shapes n a k i j)) ≤ 60 + 6 * k + 14 * n := by
  cases k with
  | zero =>
    have h := EncodingSize.rational_size_upper (shapes n a 0 i j)
    simp only [shapes, Matrix.one_apply] at h ⊢
    split_ifs at h ⊢ <;> norm_num at h <;> omega
  | succ k =>
    have hm : |(shapes n a (k + 1) i j : ℝ)| ≤ (4 ^ (k + 1) : ℕ) := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using shapes_entry_magnitude n hn a ha (k + 1) i j
    have he := encoding_bound_of_magnitude _ _ _ hm (shapes_denominator n a k i j)
    have hsizeM : (4 ^ (k + 1) : ℕ).size = 2 * (k + 1) + 1 := by
      rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul, Nat.size_pow]
    rw [hsizeM, shapeGrid_size] at he
    omega

theorem centers_denominator (n : ℕ) (a : ℕ → Fin n → ℚ) (k : ℕ) (i : Fin n) :
    (centers n a 0 (k + 1) i).den ≤ gridDenominator (2 * k + 2) (2 * n + 4) n := by
  exact (grid_num_den_bound _ _ (gridDenominator_pos _ _ _)).2

theorem centers_encoding_size (n : ℕ) (hn : 2 ≤ n) (a : ℕ → Fin n → ℚ)
    (ha : ∀ k, 1 ≤ realVector (a k) ⬝ᵥ realVector (a k)) (k : ℕ) (i : Fin n) :
    bitSize (encodeRational (centers n a 0 k i)) ≤ 60 + 6 * k + 14 * n := by
  cases k with
  | zero =>
    have h := EncodingSize.rational_size_upper (centers n a 0 0 i)
    change bitSize (encodeRational 0) ≤ _
    norm_num [centers] at h
    omega
  | succ k =>
    have hm : |(centers n a 0 (k + 1) i : ℝ)| ≤ (2 ^ (k + 1 + 2) : ℕ) := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using centers_magnitude n hn a ha (k + 1) i
    have he := encoding_bound_of_magnitude _ _ _ hm (centers_denominator n a k i)
    rw [Nat.size_pow, sequence_grid_size] at he
    omega

end Lax109476Proofs.EllipsoidStateSize

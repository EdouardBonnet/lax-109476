import Lax109476Proofs.RationalArithmeticBounds
import Lax109476Proofs.EllipsoidCenter

open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidArithmeticBounds

open RationalArithmeticBounds RationalRounding Matrix
open EllipsoidBounds EllipsoidCenter

theorem height_dot {n : ℕ} (x y : Fin n → ℚ) (B C : ℕ)
    (hx : ∀ i, Height (x i) B) (hy : ∀ i, Height (y i) C) :
    Height (x ⬝ᵥ y) ((2 * (B * C)) ^ n) := by
  simpa only [dotProduct, Finset.card_univ, Fintype.card_fin] using
    height_sum Finset.univ (fun i => x i * y i) (B * C)
      (fun i _ => height_mul _ _ B C (hx i) (hy i))

theorem height_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ)
    (B C : ℕ) (hA : ∀ i j, Height (A i j) B) (hx : ∀ i, Height (x i) C) (i : Fin n) :
    Height ((A *ᵥ x) i) ((2 * (B * C)) ^ n) := by
  exact height_dot (A i) x B C (hA i) hx

theorem height_form {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ)
    (B C : ℕ) (hA : ∀ i j, Height (A i j) B) (hx : ∀ i, Height (x i) C) :
    Height (x ⬝ᵥ (A *ᵥ x)) ((2 * (C * (2 * (B * C)) ^ n)) ^ n) :=
  height_dot x (A *ᵥ x) C ((2 * (B * C)) ^ n) hx (height_mulVec A x B C hA hx)

theorem height_roundDown (q : ℚ) (B D : ℕ) (hq : Height q B) (hD : 0 < D) :
    Height (roundDown q D) (B * D + 1) := by
  have hb : 1 ≤ B := q.den_pos.trans_le hq.2
  have hg := grid_num_den_bound (Int.floor (q * D)) D hD
  have hn := roundDown_floor_bound q D
  exact ⟨hg.1.trans (hn.trans (Nat.add_le_add_right (Nat.mul_le_mul_right D hq.1) 1)),
    hg.2.trans (by nlinarith)⟩

theorem height_sqrtUpper (q : ℚ) (B D : ℕ) (hq : Height q B) (hD : 0 < D) :
    Height (sqrtUpper q D) (B * D ^ 2 + 1) := by
  have hb : 1 ≤ B := q.den_pos.trans_le hq.2
  have hqB : q ≤ (B : ℚ) := by
    have hden : (0 : ℚ) < q.den := by positivity
    have hden1 : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
    have hn : (q.num : ℚ) ≤ B := by
      have hnabs : q.num ≤ (q.num.natAbs : ℤ) := Int.le_natAbs
      have hc' : (q.num : ℚ) ≤ ((q.num.natAbs : ℤ) : ℚ) := Int.cast_le.mpr hnabs
      have hc : (q.num : ℚ) ≤ (q.num.natAbs : ℚ) := by simpa only [Int.cast_natCast] using hc'
      exact hc.trans (by exact_mod_cast hq.1)
    rw [← q.num_div_den]
    apply (div_le_iff₀ hden).mpr
    exact hn.trans (by nlinarith)
  have hc : Nat.ceil (q * (D : ℚ) ^ 2) ≤ B * D ^ 2 := by
    apply Nat.ceil_le.mpr
    exact_mod_cast mul_le_mul_of_nonneg_right hqB (sq_nonneg (D : ℚ))
  have hs : Nat.sqrt (Nat.ceil (q * (D : ℚ) ^ 2)) ≤ B * D ^ 2 :=
    (Nat.sqrt_le_self _).trans hc
  have hg := grid_num_den_bound
    ((Nat.sqrt (Nat.ceil (q * (D : ℚ) ^ 2)) + 1 : ℕ) : ℤ) D hD
  simp only [Int.cast_natCast, Int.natAbs_natCast] at hg
  exact ⟨hg.1.trans (Nat.add_le_add_right hs 1), hg.2.trans (by nlinarith)⟩

def vectorCap (n B C : ℕ) : ℕ := (2 * (B * C)) ^ n

def formCap (n B C : ℕ) : ℕ := (2 * (C * vectorCap n B C)) ^ n

/-- Every unreduced central-cut entry has an explicit height bound built
from the input entry bounds and polynomially many arithmetic operations. -/
theorem height_cutShape {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (a : Fin n → ℚ)
    (B C : ℕ) (hA : ∀ i j, Height (A i j) B) (ha : ∀ i, Height (a i) C)
    (i j : Fin n) :
    Height (cutShape n A a i j)
      (16 * B * (n + 2) ^ 5 * formCap n B C * (vectorCap n B C) ^ 2) := by
  have hn : Height (n : ℚ) (n + 2) := height_nat n _ (by omega) (by omega)
  have h1 : Height 1 1 := by simp [Height]
  have h2 : Height 2 2 := by norm_num [Height]
  have hnp := height_mono ((n : ℚ) + 1)
    (height_add (n : ℚ) 1 (n + 2) 1 hn h1) (by omega : 2 * (n + 2) * 1 ≤ 2 * (n + 2))
  have hns := height_pow (n : ℚ) (n + 2) 2 hn
  have hden := height_sub _ _ ((n + 2) ^ 2) 1 hns h1
  have hα := height_div _ _ _ _ hns hden
  have hq := height_form A a B C hA ha
  have hv (k : Fin n) := height_mulVec A a B C hA ha k
  have hβ := height_div (2 : ℚ) (((n : ℚ) + 1) * (a ⬝ᵥ (A *ᵥ a))) 2
    ((2 * (n + 2)) * formCap n B C) h2 (height_mul _ _ _ _ hnp hq)
  have ht := height_mul _ _ _ _ hβ (height_mul _ _ _ _ (hv i) (hv j))
  have hd := height_sub _ _ _ _ (hA i j) ht
  have hf := height_mul _ _ _ _ hα hd
  convert hf using 1 <;>
    simp only [cutShape, Matrix.smul_apply, Matrix.sub_apply, Matrix.vecMulVec,
      Matrix.of_apply, smul_eq_mul, vectorCap]
  ring

theorem height_approximateCenter {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ) (B C E D : ℕ)
    (hA : ∀ i j, Height (A i j) B) (ha : ∀ i, Height (a i) C)
    (hc : ∀ i, Height (c i) E) (hD : 0 < D) (i : Fin n) :
    Height (approximateCenter n A a c D i)
      (4 * E * (n + 2) * (formCap n B C * D ^ 2 + 1) * vectorCap n B C) := by
  have hn : Height (n : ℚ) (n + 2) := height_nat n _ (by omega) (by omega)
  have h1 : Height 1 1 := by simp [Height]
  have hnp := height_mono ((n : ℚ) + 1)
    (height_add (n : ℚ) 1 (n + 2) 1 hn h1) (by omega : 2 * (n + 2) * 1 ≤ 2 * (n + 2))
  have hq := height_form A a B C hA ha
  have hs := height_sqrtUpper (a ⬝ᵥ (A *ᵥ a)) (formCap n B C) D hq hD
  have hd := height_mul _ _ _ _ hnp hs
  have hi := height_div (1 : ℚ) _ 1 _ h1 hd
  have hv := height_mulVec A a B C hA ha i
  have h := height_sub _ _ _ _ (hc i) (height_mul _ _ _ _ hi hv)
  convert h using 1 <;>
    simp only [approximateCenter, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, vectorCap]
  ring

/-- The bit sizes of the unreduced vector products grow polynomially in
dimension and the bit sizes of the operands. -/
theorem vectorCap_size (n B C : ℕ) :
    (vectorCap n B C).size ≤ n * (2 + B.size + C.size) + 1 := by
  have hp := RationalSizeBounds.size_pow_le (2 * (B * C)) n
  have hm := RationalSizeBounds.size_mul_le 2 (B * C)
  have hbc := RationalSizeBounds.size_mul_le B C
  have h2 : (2 : ℕ).size = 2 := by decide
  unfold vectorCap
  nlinarith

theorem formCap_size (n B C : ℕ) :
    (formCap n B C).size ≤ n * (3 + C.size + n * (2 + B.size + C.size)) + 1 := by
  have hp := RationalSizeBounds.size_pow_le (2 * (C * vectorCap n B C)) n
  have hm := RationalSizeBounds.size_mul_le 2 (C * vectorCap n B C)
  have hcv := RationalSizeBounds.size_mul_le C (vectorCap n B C)
  have hv := vectorCap_size n B C
  have h2 : (2 : ℕ).size = 2 := by decide
  unfold formCap
  nlinarith

end Lax109476Proofs.EllipsoidArithmeticBounds

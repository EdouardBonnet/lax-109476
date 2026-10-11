import Lax109476Proofs.BinaryOptimization
import Lax109476Proofs.RationalArithmeticBounds

namespace Lax109476Proofs.BinaryOptimizationBounds

open RationalArithmeticBounds BinaryOptimization

def DyadicBound (B k : ℕ) (q : ℚ) : Prop :=
  ∃ z : ℕ, z ≤ B * 2 ^ k ∧ q = (z : ℚ) / (2 : ℚ) ^ k

theorem dyadic_advance {B k : ℕ} {q : ℚ} (h : DyadicBound B k q) : DyadicBound B (k + 1) q := by
  obtain ⟨z, hz, he⟩ := h
  refine ⟨2 * z, ?_, ?_⟩
  · calc
      2 * z ≤ 2 * (B * 2 ^ k) := Nat.mul_le_mul_left 2 hz
      _ = B * 2 ^ (k + 1) := by rw [pow_succ]; ring
  · rw [he, pow_succ]
    push_cast
    field_simp

theorem dyadic_midpoint {B k : ℕ} {l u : ℚ} (hl : DyadicBound B k l) (hu : DyadicBound B k u) :
    DyadicBound B (k + 1) ((l + u) / 2) := by
  obtain ⟨z, hz, he⟩ := hl
  obtain ⟨t, ht, het⟩ := hu
  refine ⟨z + t, ?_, ?_⟩
  · calc
      z + t ≤ B * 2 ^ k + B * 2 ^ k := Nat.add_le_add hz ht
      _ = B * 2 ^ (k + 1) := by rw [pow_succ]; ring
  · rw [he, het, pow_succ]
    push_cast
    field_simp

theorem bisect_dyadic (query : ℚ → Bool) (B k : ℕ) :
    DyadicBound B k (bisect query 0 B k).1 ∧ DyadicBound B k (bisect query 0 B k).2 := by
  induction k with
  | zero => simp only [bisect]; exact ⟨⟨0, by simp, by simp⟩, ⟨B, by simp, by simp⟩⟩
  | succ k ih =>
    have hm := dyadic_midpoint ih.1 ih.2
    have hl := dyadic_advance ih.1
    have hu := dyadic_advance ih.2
    simp only [bisect]
    split_ifs <;> exact ⟨by assumption, by assumption⟩

theorem dyadic_height {B k : ℕ} {q : ℚ} (h : DyadicBound B k q) :
    Height q ((B + 1) * 2 ^ k) := by
  obtain ⟨z, hz, he⟩ := h
  let D : ℕ := 2 ^ k
  have hd : (D : ℤ) ≠ 0 := by dsimp [D]; positivity
  have hn : (z : ℤ).natAbs ≤ (B + 1) * D := by
    simp only [Int.natAbs_natCast]
    exact hz.trans (Nat.mul_le_mul_right D (by omega : B ≤ B + 1))
  have hden : (D : ℤ).natAbs ≤ (B + 1) * D := by
    simp only [Int.natAbs_natCast]
    exact (Nat.one_mul D).symm.trans_le (Nat.mul_le_mul_right D (by omega : 1 ≤ B + 1))
  have hrep : q = ((z : ℤ) : ℚ) / ((D : ℤ) : ℚ) := by simpa [D] using he
  rw [hrep]
  obtain ⟨hn', hd'⟩ := DeterminantBounds.integer_ratio_num_den_bound (z : ℤ) (D : ℤ) hd
  exact ⟨hn'.trans hn, hd'.trans hden⟩

theorem bisect_heights (query : ℚ → Bool) (B k : ℕ) :
    Height (bisect query 0 B k).1 ((B + 1) * 2 ^ k) ∧
      Height (bisect query 0 B k).2 ((B + 1) * 2 ^ k) := by
  obtain ⟨hl, hu⟩ := bisect_dyadic query B k
  exact ⟨dyadic_height hl, dyadic_height hu⟩

end Lax109476Proofs.BinaryOptimizationBounds

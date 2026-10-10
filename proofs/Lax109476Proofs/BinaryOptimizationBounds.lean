import Lax109476Proofs.BinaryOptimization
import Lax109476Proofs.RationalArithmeticBounds
import Lax109476Proofs.RationalRounding

namespace Lax109476Proofs.BinaryOptimizationBounds

open BinaryOptimization RationalArithmeticBounds RationalRounding

/-- The binary search stays on an explicitly bounded dyadic grid, for every
sequence of answers, including queries to infeasible auxiliary systems. -/
theorem bisect_grid (query : ℚ → Bool) (B k : ℕ) :
    ∃ a b : ℕ, a ≤ b ∧ b ≤ B * 2 ^ k ∧
      (bisect query 0 B k).1 = (a : ℚ) / 2 ^ k ∧
      (bisect query 0 B k).2 = (b : ℚ) / 2 ^ k := by
  induction k with
  | zero => exact ⟨0, B, Nat.zero_le _, by simp, by simp [bisect], by simp [bisect]⟩
  | succ k ih =>
    obtain ⟨a, b, hab, hb, ha', hb'⟩ := ih
    let mid := ((bisect query 0 B k).1 + (bisect query 0 B k).2) / 2
    have hm : mid = ((a + b : ℕ) : ℚ) / 2 ^ (k + 1) := by
      dsimp only [mid]
      rw [ha', hb', pow_succ]
      push_cast
      ring
    have hdouble (v : ℕ) : (v : ℚ) / 2 ^ k = ((2 * v : ℕ) : ℚ) / 2 ^ (k + 1) := by
      rw [pow_succ]
      push_cast
      field_simp
    change ∃ a' b' : ℕ, a' ≤ b' ∧ b' ≤ B * 2 ^ (k + 1) ∧
      (if query mid then ((bisect query 0 B k).1, mid)
        else (mid, (bisect query 0 B k).2)).1 = _ ∧
      (if query mid then ((bisect query 0 B k).1, mid)
        else (mid, (bisect query 0 B k).2)).2 = _
    by_cases h : query mid = true
    · rw [if_pos h]
      refine ⟨2 * a, a + b, by omega, ?_, ha'.trans (hdouble a), hm⟩
      rw [pow_succ]
      nlinarith
    · rw [if_neg h]
      refine ⟨a + b, 2 * b, by omega, ?_, hm, hb'.trans (hdouble b)⟩
      rw [pow_succ]
      nlinarith

theorem bisect_range (query : ℚ → Bool) (B k : ℕ) :
    0 ≤ (bisect query 0 B k).1 ∧
      (bisect query 0 B k).1 ≤ (bisect query 0 B k).2 ∧
      (bisect query 0 B k).2 ≤ B := by
  obtain ⟨a, b, hab, hb, ha', hb'⟩ := bisect_grid query B k
  rw [ha', hb']
  have hp : (0 : ℚ) < 2 ^ k := by positivity
  refine ⟨by positivity, (div_le_div_iff_of_pos_right hp).mpr (by exact_mod_cast hab), ?_⟩
  apply (div_le_iff₀ hp).mpr
  exact_mod_cast hb

theorem bisect_height (query : ℚ → Bool) (B k : ℕ) :
    Height (bisect query 0 B k).1 ((B + 1) * 2 ^ k) ∧
      Height (bisect query 0 B k).2 ((B + 1) * 2 ^ k) := by
  obtain ⟨a, b, hab, hb, ha', hb'⟩ := bisect_grid query B k
  have hg (v : ℕ) (hv : v ≤ B * 2 ^ k) :
      Height ((v : ℚ) / 2 ^ k) ((B + 1) * 2 ^ k) := by
    have h := grid_num_den_bound (v : ℤ) (2 ^ k) (by positivity)
    simp only [Int.cast_natCast, Nat.cast_pow, Nat.cast_ofNat, Int.natAbs_natCast] at h
    exact ⟨h.1.trans (by nlinarith), h.2.trans (by nlinarith)⟩
  rw [ha', hb']
  exact ⟨hg a (hab.trans hb), hg b hb⟩

/-- Successful reconstruction is bounded even when no attained minimum
exists. Thus a failed certificate branch cannot grow later query data. -/
theorem minimum_height (query : ℚ → Bool) (B : ℕ) (q : ℚ)
    (h : minimum query B = some q) : Height q (B * B + 1) := by
  obtain ⟨hd, hl, hu⟩ := RationalReconstruction.reconstruct_spec _ _ q B h
  obtain ⟨hl0, _, huB⟩ := bisect_range query B (steps B)
  have hq0 : 0 ≤ q := hl0.trans hl
  have hqB : q ≤ (B : ℚ) := hu.trans huB
  have hn : (q.num.natAbs : ℚ) ≤ (B : ℚ) * B := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast Rat.num_nonneg.mpr hq0)]
    rw [← Rat.mul_den_eq_num]
    exact mul_le_mul hqB (by exact_mod_cast hd) (by positivity) (by positivity)
  have hn' : q.num.natAbs ≤ B * B := by exact_mod_cast hn
  exact ⟨hn'.trans (Nat.le_add_right _ _),
    hd.trans (by nlinarith)⟩

end Lax109476Proofs.BinaryOptimizationBounds

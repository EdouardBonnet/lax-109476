import Lax109476Proofs.RamContinuedFractionStep

namespace Lax109476Proofs.ContinuedFractionBounds

open RationalArithmeticBounds RationalReconstruction RamContinuedFractionStep

theorem tail_nonneg (q : ℚ) : 0 ≤ tail q := by
  exact inv_nonneg.mpr (Int.fract_nonneg q)

theorem tail_height (q : ℚ) (M : ℕ) (hq : 0 ≤ q) (hh : Height q M) : Height (tail q) M := by
  have hM : 1 ≤ M := le_trans q.den_pos hh.2
  have hrep := nonnegative_representation q hq
  rw [← hrep, nonnegative_tail q.num.natAbs q.den q.den_pos]
  by_cases hz : q.num.natAbs % q.den = 0
  · simpa [hz, RamRational.fractionValue] using height_mono 0 height_zero hM
  · exact RamPrimitiveBounds.fractionValue_height 0 q.den (q.num.natAbs % q.den) M hh.2
      ((Nat.mod_lt _ q.den_pos).le.trans hh.2) (Nat.pos_of_ne_zero hz)

theorem iterated_tail_height (q : ℚ) (M j : ℕ) (hq : 0 ≤ q) (hh : Height q M) :
    0 ≤ tail^[j] q ∧ Height (tail^[j] q) M := by
  induction j with
  | zero => exact ⟨hq, hh⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨tail_nonneg _, tail_height _ M ih.1 ih.2⟩

theorem floor_height (q : ℚ) (M : ℕ) (hq : 0 ≤ q) (hh : Height q M) : Height (Int.floor q : ℚ) M := by
  have hfloor : (Int.floor q : ℚ) = ((Int.floor q).toNat : ℚ) := by
    exact_mod_cast (Int.toNat_of_nonneg (Int.floor_nonneg.mpr hq)).symm
  rw [hfloor]
  exact height_nat _ M ((floor_toNat q hq) ▸ (Nat.div_le_self _ _).trans hh.1) (le_trans q.den_pos hh.2)

/-- Tail heights stay bounded by the input height, while convergent heights
have bit length linear in the number of continued-fraction steps. -/
theorem convergent_height (q : ℚ) (M k : ℕ) (hq : 0 ≤ q) (hh : Height q M) :
    Height (convergent q k) ((2 * M) ^ (k + 1)) := by
  have hM : 1 ≤ M := le_trans q.den_pos hh.2
  induction k generalizing q with
  | zero =>
    simpa only [convergent, Nat.zero_add, pow_one] using
      height_mono _ (floor_height q M hq hh) (by omega : M ≤ 2 * M)
  | succ k ih =>
    have ht := tail_height q M hq hh
    have hi := ih (tail q) (tail_nonneg q) ht
    have ha := height_add (Int.floor q : ℚ) (convergent (tail q) k)⁻¹
      M ((2 * M) ^ (k + 1)) (floor_height q M hq hh) (height_inv _ _ hi)
    simpa only [convergent, tail, pow_succ, Nat.mul_comm] using ha

end Lax109476Proofs.ContinuedFractionBounds

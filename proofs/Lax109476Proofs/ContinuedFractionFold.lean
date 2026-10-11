import Lax109476Proofs.ContinuedFractionBounds

namespace Lax109476Proofs.ContinuedFractionFold

open RationalArithmeticBounds RationalReconstruction ContinuedFractionBounds

def fold (q : ℚ) (K : ℕ) : ℕ → ℚ
  | 0 => 0
  | t + 1 => (Int.floor (tail^[K - (t + 1)] q) : ℚ) + (fold q K t)⁻¹

theorem fold_eq_convergent (q : ℚ) (K t : ℕ) (ht : t < K) :
    fold q K (t + 1) = convergent (tail^[K - (t + 1)] q) t := by
  induction t with
  | zero => simp [fold, convergent]
  | succ t ih =>
    have ht' : t < K := by omega
    have hind := ih ht'
    have hindex : K - (t + 1) = K - (t + 1 + 1) + 1 := by omega
    rw [fold, hind, hindex, Function.iterate_succ_apply']
    rfl

theorem fold_height (q : ℚ) (M K t : ℕ) (hq : 0 ≤ q) (hh : Height q M) (ht : t ≤ K) :
    Height (fold q K t) ((2 * M) ^ (K + 1)) := by
  have hM : 1 ≤ M := le_trans q.den_pos hh.2
  cases t with
  | zero =>
    exact height_mono _ height_zero (Nat.one_le_pow _ _ (by omega))
  | succ t =>
    rw [fold_eq_convergent q K t (by omega)]
    have hr := iterated_tail_height q M (K - (t + 1)) hq hh
    exact height_mono _ (convergent_height _ M t hr.1 hr.2)
      (Nat.pow_le_pow_right (by omega) (by omega))

theorem fold_complete (q : ℚ) (k : ℕ) : fold q (k + 1) (k + 1) = convergent q k := by
  simpa using fold_eq_convergent q (k + 1) k (by omega)

end Lax109476Proofs.ContinuedFractionFold

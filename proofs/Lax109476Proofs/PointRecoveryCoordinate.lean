import Lax109476Proofs.PointRecovery

namespace Lax109476Proofs.PointRecovery

open Lax109476.LinearProgram Lax109476.RationalCertificates
open LexicographicMinima CoordinateOptimization

theorem coordinateMinimum_prefix {m n : ℕ} (P : Program ℚ m n) (D : ℕ)
    (x : Fin n → ℚ) (hx : PrimalFeasible (toReal P) (realVector x))
    (hlex : ∀ i, ∀ y, PrimalFeasible (toReal P) y →
      (∀ j, j < i → y j = (x j : ℝ)) → (x i : ℝ) ≤ y i)
    (hb : ∀ j, x j ≤ D ∧ (x j).den ≤ D) (k : ℕ) (hk : k < n) :
    coordinateMinimum (fixedPrefix P (prefixVector x k) k) ⟨k, hk⟩ D = some (x ⟨k, hk⟩) := by
  have hprev := recoverPrefix_exact P D x hx hlex hb k hk.le
  have hnext := recoverPrefix_exact P D x hx hlex hb (k + 1) hk
  simp only [recoverPrefix, hprev, Option.bind_some, dif_pos hk] at hnext
  obtain ⟨v, hv, he⟩ := Option.map_eq_some_iff.mp hnext
  have hvalue : v = x ⟨k, hk⟩ := by
    have hi := congrFun he ⟨k, hk⟩
    simpa [prefixVector] using hi
  simpa only [hvalue] using hv

end Lax109476Proofs.PointRecovery

import Lax109476Proofs.IntegerCertificates
import Lax109476Proofs.LexicographicBounds

namespace Lax109476Proofs.StandardPointCapComparison

theorem slack_cap_le (m n H : ℕ) :
    LexicographicBounds.coordinateCap m (n + m) H ≤ IntegerCertificates.coordinateCap m n H := by
  let K := 2 * (m + n) + 2
  have hnm : n + m ≤ K := by dsimp only [K]; omega
  have hm : m ≤ K := by dsimp only [K]; omega
  unfold LexicographicBounds.coordinateCap IntegerCertificates.coordinateCap
  change (n + m).factorial * (m * H ^ 2 + 1) ^ (n + m) ≤ K.factorial * (K * H ^ 2 + 1) ^ K
  apply Nat.mul_le_mul (Nat.factorial_le hnm)
  exact (Nat.pow_le_pow_left (by gcongr) _).trans (Nat.pow_le_pow_right (by omega) hnm)

end Lax109476Proofs.StandardPointCapComparison

import Lax109476Proofs.EllipsoidSequence
import Lax109476Proofs.EllipsoidBall

open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidTermination

open Lax109476.RationalCertificates
open EllipsoidRounding EllipsoidSequence EllipsoidBall

/-- A ball inside the initial ellipsoid cannot survive every cut up to the
explicit dyadic threshold budget. This uses the stored rational updates. -/
theorem cannot_retain_ball (n : ℕ) (hn : 2 ≤ n) (a : ℕ → Fin n → ℚ)
    (ha : ∀ k, 1 ≤ realVector (a k) ⬝ᵥ realVector (a k)) (c₀ : Fin n → ℚ)
    (z : Fin n → ℝ) (B : ℕ)
    (hunit : ∀ e : Fin n → ℝ, e ⬝ᵥ e ≤ (((2 : ℝ) ^ B)⁻¹) ^ 2 →
      (z + e - realVector c₀) ⬝ᵥ (z + e - realVector c₀) ≤ 1) :
    ¬ ∀ k < thresholdSteps n B, ∀ e : Fin n → ℝ,
      e ⬝ᵥ e ≤ (((2 : ℝ) ^ B)⁻¹) ^ 2 →
      realVector (a k) ⬝ᵥ (z + e - realVector (centers n a c₀ k)) ≤ 0 := by
  intro hcut
  let K := thresholdSteps n B
  have hshape := (shapes_invariant n hn a ha K).1
  have hball : ∀ e : Fin n → ℝ, e ⬝ᵥ e ≤ (((2 : ℝ) ^ B)⁻¹) ^ 2 →
      (z + e - realVector (centers n a c₀ K)) ⬝ᵥ
        ((realShape (shapes n a K))⁻¹ *ᵥ (z + e - realVector (centers n a c₀ K))) ≤ 1 := by
    intro e he
    exact preserves_points_up_to n hn a ha c₀ (z + e) (hunit e he) K
      (fun j hj => hcut j hj e he)
  have hlo := sqrt_det_lower_bound_of_ball hshape z (realVector (centers n a c₀ K))
    (((2 : ℝ) ^ B)⁻¹) (by positivity) hball
  have hhi := shapes_below_threshold n hn a ha B
  simp only [Fintype.card_fin] at hlo
  exact (not_lt_of_ge hlo) hhi

end Lax109476Proofs.EllipsoidTermination

import Lax109476.CertificateExistence
import Lax109476.CertificateSoundness
import Lax109476Proofs.CoordinateOptimization

open scoped BigOperators

namespace Lax109476Proofs.RationalMinima

open Lax109476.LinearProgram Lax109476.RationalCertificates

def minimizationProgram {m n : ℕ} (P : Program ℚ m n) (j : Fin n) : Program ℚ m n :=
  { P with c := fun k => if k = j then -1 else 0 }

theorem minimization_value {m n : ℕ} (P : Program ℚ m n) (j : Fin n)
    (y : Fin n → ℝ) : primalValue (toReal (minimizationProgram P j)) y = -y j := by
  simp [primalValue, toReal, minimizationProgram, apply_ite]

/-- Coordinate minima always exist for a nonempty nonnegative polyhedron.
Rational certificate existence supplies a rational attained minimum; this
lemma is an existence argument used to verify the executable recovery. -/
theorem exists_coordinate_minimum {m n : ℕ} (P : Program ℚ m n) (j : Fin n)
    (hf : IsFeasible (toReal P)) :
    ∃ x : Fin n → ℚ, PrimalFeasible (toReal P) (realVector x) ∧
      ∀ y, PrimalFeasible (toReal P) y → (x j : ℝ) ≤ y j := by
  let Q := minimizationProgram P j
  have hfeas : IsFeasible (toReal Q) := hf
  have hbound : IsBoundedAbove (toReal Q) := by
    refine ⟨0, fun y hy => ?_⟩
    rw [minimization_value]
    exact neg_nonpos.mpr (hy.1 j)
  obtain ⟨cert, hv⟩ := Lax109476.CertificateExistence.exists_valid_certificate m n Q
  have hc := Lax109476.CertificateSoundness.valid_certificate_correct m n Q cert hv
  cases cert with
  | optimal x y =>
    refine ⟨x, hc.1, fun z hz => ?_⟩
    have h := hc.2 z hz
    change primalValue (toReal (minimizationProgram P j)) z ≤
      primalValue (toReal (minimizationProgram P j)) (realVector x) at h
    rw [minimization_value, minimization_value] at h
    exact neg_le_neg_iff.mp h
  | infeasible y => exact False.elim (hc hfeas)
  | unbounded x d => exact False.elim (hc.2 hbound)

end Lax109476Proofs.RationalMinima

import Lax109476Proofs.Certificates
import Lax109476.PolynomialTimeSolver
import Lax109476.CertifiedOptimization
import Lax109476.ComplementarySlackness

open scoped BigOperators

namespace Lax109476Proofs.Optimization

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.RamPolytime

/--
---
conclusion: Lax109476.CertifiedOptimization.exists_certified_polynomial_time_solver
---
Keep the exact solver's program, runtime bound, and returned certificate.
Apply certificate soundness to that same certificate. The solver theorem
is the algorithmic assumption; soundness supplies the real outcome guarantee.
-/
theorem certified_optimization :
    ∃ solve : List ℕ → List ℕ, RamPolytime solve ∧
      ∀ (m n : ℕ) (P : Program ℚ m n), ∃ certificate : Certificate m n,
        solve (encodeProgram P) = encodeCertificate certificate ∧
          IsValidCertificate P certificate ∧ IsCorrectOutcome P certificate := by
  obtain ⟨solve, hruntime, hsolve⟩ :=
    Lax109476.PolynomialTimeSolver.exists_exact_polynomial_time_solver
  refine ⟨solve, hruntime, ?_⟩
  intro m n P
  obtain ⟨certificate, houtput, hvalid⟩ := hsolve m n P
  exact ⟨certificate, houtput, hvalid,
    Lax109476.CertificateSoundness.valid_certificate_correct m n P certificate hvalid⟩

private theorem gap_identity {m n : ℕ} (P : Program ℝ m n)
    (x : Fin n → ℝ) (y : Fin m → ℝ) :
    dualValue P y - primalValue P x =
      (∑ i, y i * (P.b i - rowValue P x i)) +
      ∑ j, x j * (columnValue P y j - P.c j) := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  have hid := Lax109476Proofs.Basic.transpose_identity P x y
  simp_rw [mul_comm (y _) _, mul_comm (x _) _]
  dsimp [dualValue, primalValue] at *
  linarith

/--
---
conclusion: Lax109476.ComplementarySlackness.matching_iff_slackness
---
The duality gap equals the sum of the nonnegative row and column
complementarity products. A finite sum of nonnegative real numbers
vanishes exactly when all its terms vanish.
-/
theorem complementary_slackness :
    ∀ (m n : ℕ) (P : Program ℝ m n) (x : Fin n → ℝ) (y : Fin m → ℝ),
      PrimalFeasible P x → DualFeasible P y →
        (primalValue P x = dualValue P y ↔
          (∀ i, y i * (P.b i - rowValue P x i) = 0) ∧
          (∀ j, x j * (columnValue P y j - P.c j) = 0)) := by
  intro m n P x y hx hy
  have hrow : ∀ i, 0 ≤ y i * (P.b i - rowValue P x i) :=
    fun i => mul_nonneg (hy.1 i) (sub_nonneg.mpr (hx.2 i))
  have hcol : ∀ j, 0 ≤ x j * (columnValue P y j - P.c j) :=
    fun j => mul_nonneg (hx.1 j) (sub_nonneg.mpr (hy.2 j))
  have hid := gap_identity P x y
  constructor
  · intro heq
    have hsrow := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hrow i)
    have hscol := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hcol j)
    have hzrow : (∑ i, y i * (P.b i - rowValue P x i)) = 0 := by linarith
    have hzcol : (∑ j, x j * (columnValue P y j - P.c j)) = 0 := by linarith
    constructor
    · intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hrow k)).mp hzrow i
        (Finset.mem_univ i)
    · intro j
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hcol k)).mp hzcol j
        (Finset.mem_univ j)
  · rintro ⟨hr, hc⟩
    simp only [hr, hc, Finset.sum_const_zero, add_zero] at hid
    linarith

end Lax109476Proofs.Optimization

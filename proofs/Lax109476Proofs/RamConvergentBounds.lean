import Lax109476Proofs.RamContinuedFractionConvergent
import Lax109476Proofs.RamSolverFrontEnd

namespace Lax109476Proofs.RamConvergentBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RationalReconstruction

def exponent (S K : ℕ) : ℕ := (S + 1) * (K + 2)

def wordWidth (S K : ℕ) : ℕ := RamDecoder.wordWidth (exponent S K) + K + 2

def instructionBound (S K : ℕ) : ℕ :=
  ((36 * (S + 1) + 113) + (108 * (exponent S K + 1) + 208)) * (K + 1) + 22

theorem intermediate_bound (S K k : ℕ) (hk : k ≤ K) :
    (2 * 2 ^ S) ^ (k + 2) ≤ 2 ^ exponent S K := by
  rw [show 2 * 2 ^ S = 2 ^ (S + 1) by rw [pow_succ]; omega, ← pow_mul]
  exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left (S + 1) (by omega))

/-- The same finite program computes every convergent up to a depth bound.
Both resource bounds are polynomials in the rational input bit bound and depth. -/
theorem convergent_spec (S K N k w : ℕ) (q : ℚ) (hq : 0 ≤ q) (hh : Height q (2 ^ S))
    (hk : k ≤ K) (hN : K + 1 ≤ N) (hw : wordWidth S K ≤ w) :
    Spec (2 ^ w) (fun σ => (σ.arrs "cf.stack").length = N ∧ LeftValue q σ ∧ σ.vars "cf.depth" = k)
      RamContinuedFractionConvergent.convergent
      (fun _ τ => FractionOutput (RationalReconstruction.convergent q k) τ)
      (instructionBound S K) := by
  have hwD : RamDecoder.wordWidth (exponent S K) ≤ w := by unfold wordWidth at hw; omega
  have hKB : k + 1 < 2 ^ w := (by unfold wordWidth at hw; omega : k + 1 ≤ w).trans_lt (Nat.lt_two_pow_self (n := w))
  have hR := intermediate_bound S K k hk
  have hguard := (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hR 2)) 3).trans_lt
    (RamSolverFrontEnd.clearing_word_guard (exponent S K) w hwD)
  have hcost :
      (((36 * (2 ^ S).size + 113) + (108 * ((2 * 2 ^ S) ^ (k + 2)).size + 208)) * (k + 1) + 22) ≤
        instructionBound S K := by
    have hs := Nat.size_le_size hR
    rw [Nat.size_pow] at hs
    rw [Nat.size_pow]
    unfold instructionBound
    gcongr
  exact (RamContinuedFractionConvergent.convergent_spec (2 ^ w) (2 ^ S) N k q hq hh
    hKB (by omega) hguard).mono hcost

end Lax109476Proofs.RamConvergentBounds

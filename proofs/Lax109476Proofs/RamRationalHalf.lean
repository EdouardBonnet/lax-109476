import Lax109476Proofs.RamScalarFrame

namespace Lax109476Proofs.RamRationalHalf

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RamArithmetic

def half : Com := .seq (.assign "rat.s" (.var "left.s"))
  (.seq (.assign "rat.n" (.var "left.n"))
    (.seq (.assign "rat.d" (.mul (.var "left.d") (.lit 2))) normalizeFraction))

theorem fractionValue_half (s n d : ℕ) : fractionValue s n (2 * d) = fractionValue s n d / 2 := by
  unfold fractionValue
  split_ifs <;> push_cast <;> ring

theorem half_spec (B M : ℕ) (q : ℚ) (hB : 2 * M + 3 < B) (hq : Height q M) :
    Spec B (LeftValue q) half (fun _ τ => FractionOutput (q / 2) τ) (36 * M.size + 60) := by
  have h2 : 2 < B := by omega
  have hnB := hq.1.trans_lt (by omega : M < B)
  have hdB : 2 * q.den < B := (Nat.mul_le_mul_left 2 hq.2).trans_lt (by omega)
  have hds := RationalSizeBounds.size_mul_le 2 q.den
  have h2size : (2 : ℕ).size = 2 := by decide
  -- Multiplication by two adds at most one bit, including the positive denominator.
  have hds' : (2 * q.den).size = q.den.size + 1 := by
    simpa [Nat.bit] using Nat.size_bit (show Nat.bit false q.den ≠ 0 by have := q.den_pos; simp [Nat.bit])
  rintro σ ⟨hval, hn, hd, hs⟩
  have hsB : σ.vars "left.s" < B := by omega
  have hnorm := normalizeFraction_output_spec B (σ.vars "left.s") q.num.natAbs (2 * q.den) hs hnB hdB (by positivity)
  have hsize := Nat.size_le_size hq.2
  have hcost : 8 + (36 * (2 * q.den).size + 16) ≤ 36 * M.size + 60 := by rw [hds']; omega
  have he : fractionValue (σ.vars "left.s") q.num.natAbs (2 * q.den) = q / 2 := by
    rw [fractionValue_half]
    simpa only [hn, hd] using congrArg (fun r : ℚ => r / 2) hval
  run_vcg [hnorm]
  all_goals simp_all [mul_comm]

end Lax109476Proofs.RamRationalHalf

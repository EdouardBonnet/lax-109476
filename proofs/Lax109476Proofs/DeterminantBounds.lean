import Lax109476Proofs.RationalRounding
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

open scoped BigOperators Matrix

namespace Lax109476Proofs.DeterminantBounds

/-- Cancellation in an integer quotient never enlarges numerator or denominator. -/
theorem integer_ratio_num_den_bound (a b : ℤ) (hb : b ≠ 0) :
    ((a : ℚ) / b).num.natAbs ≤ a.natAbs ∧
      ((a : ℚ) / b).den ≤ b.natAbs := by
  obtain ⟨c, hn, hd⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den a (d := b) hb
  have hc : c ≠ 0 := by
    intro h
    rw [h, zero_mul] at hd
    exact hb hd
  have hcpos := Int.natAbs_pos.mpr hc
  have hna : a.natAbs = c.natAbs * ((a : ℚ) / b).num.natAbs := by
    simpa only [Int.natAbs_mul] using congrArg Int.natAbs hn
  have hda : b.natAbs = c.natAbs * ((a : ℚ) / b).den := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using congrArg Int.natAbs hd
  constructor
  · rw [hna]
    exact Nat.le_mul_of_pos_left _ hcpos
  · rw [hda]
    exact Nat.le_mul_of_pos_left _ hcpos

theorem integer_ratio_encoding_bound (a b : ℤ) (hb : b ≠ 0) :
    Lax759944.BinaryWordEncoding.bitSize
      (Lax109476.RationalEncoding.encodeRational ((a : ℚ) / b)) ≤
        4 + Nat.size a.natAbs + Nat.size b.natAbs := by
  obtain ⟨hn, hd⟩ := integer_ratio_num_den_bound a b hb
  have hnsize := Nat.size_le_size hn
  have hdsize := Nat.size_le_size hd
  unfold Lax759944.BinaryWordEncoding.bitSize Lax759944.BinaryWordEncoding.encode
    Lax759944.BinaryWordEncoding.encodeNat Lax109476.RationalEncoding.encodeRational
  split_ifs <;> simp [Nat.size_eq_bits_len] <;> omega

/-- The permutation formula bounds an integer determinant by `k! H^k`. -/
theorem determinant_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (H : ℕ) (hA : ∀ i j, (A i j).natAbs ≤ H) :
    A.det.natAbs ≤ (Fintype.card ι).factorial * H ^ Fintype.card ι := by
  have hentry : ∀ i j, |A i j| ≤ (H : ℤ) := by
    intro i j
    simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr (hA i j))
  have hd : |A.det| ≤ ((Fintype.card ι).factorial : ℤ) * (H : ℤ) ^ Fintype.card ι := by
    rw [Matrix.det_apply']
    calc
      _ ≤ ∑ σ : Equiv.Perm ι, |(Equiv.Perm.sign σ : ℤ) * ∏ i, A (σ i) i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ σ : Equiv.Perm ι, ∏ i, |A (σ i) i| := by
        congr 1
        funext σ
        have hs : |(Equiv.Perm.sign σ : ℤ)| = 1 := by
          simpa using (abs_unit_intCast (α := ℤ) (Equiv.Perm.sign σ))
        rw [abs_mul, hs, one_mul, Finset.abs_prod]
      _ ≤ ∑ _σ : Equiv.Perm ι, ∏ _i : ι, (H : ℤ) := by
        apply Finset.sum_le_sum
        intro σ _
        exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => hentry _ i)
      _ = _ := by simp [Fintype.card_perm]
  have hd' : (A.det.natAbs : ℤ) ≤
      ((Fintype.card ι).factorial * H ^ Fintype.card ι : ℕ) := by
    simpa only [Int.natCast_natAbs, Nat.cast_mul, Nat.cast_pow] using hd
  exact Int.ofNat_le.mp hd'

end Lax109476Proofs.DeterminantBounds

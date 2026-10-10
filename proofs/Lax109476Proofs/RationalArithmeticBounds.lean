import Lax109476Proofs.DeterminantBounds
import Lax109476Proofs.RationalSizeBounds
import Lax109476Proofs.EncodingSize

open scoped BigOperators

namespace Lax109476Proofs.RationalArithmeticBounds

open DeterminantBounds RationalSizeBounds
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding

def Height (q : ℚ) (B : ℕ) : Prop := q.num.natAbs ≤ B ∧ q.den ≤ B

theorem height_zero : Height 0 1 := by simp [Height]

theorem height_mono (q : ℚ) {B C : ℕ} (hq : Height q B) (hBC : B ≤ C) : Height q C :=
  ⟨hq.1.trans hBC, hq.2.trans hBC⟩

theorem height_mul (q r : ℚ) (B C : ℕ) (hq : Height q B) (hr : Height r C) :
    Height (q * r) (B * C) := by
  have hd : (q.den : ℤ) * r.den ≠ 0 := by positivity
  have he : q * r = ((q.num * r.num : ℤ) : ℚ) / ((q.den : ℤ) * r.den) := by
    conv_lhs => rw [← q.num_div_den, ← r.num_div_den]
    push_cast
    ring
  rw [he]
  simp only [Int.cast_mul, Int.cast_natCast]
  obtain ⟨hn, hd'⟩ := integer_ratio_num_den_bound (q.num * r.num) _ hd
  simp only [Int.cast_mul, Int.cast_natCast] at hn hd'
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hn hd'
  exact ⟨hn.trans (Nat.mul_le_mul hq.1 hr.1), hd'.trans (Nat.mul_le_mul hq.2 hr.2)⟩

theorem height_add (q r : ℚ) (B C : ℕ) (hq : Height q B) (hr : Height r C) :
    Height (q + r) (2 * B * C) := by
  have hd : (q.den : ℤ) * r.den ≠ 0 := by positivity
  have he : q + r = ((q.num * r.den + r.num * q.den : ℤ) : ℚ) /
      ((q.den : ℤ) * r.den) := by
    conv_lhs => rw [← q.num_div_den, ← r.num_div_den]
    push_cast
    field_simp
  rw [he]
  obtain ⟨hn, hd'⟩ := integer_ratio_num_den_bound (q.num * r.den + r.num * q.den) _ hd
  simp only [Int.cast_mul, Int.cast_natCast] at hn hd'
  have hb : (q.num * r.den + r.num * q.den : ℤ).natAbs ≤ 2 * B * C := by
    calc
      _ ≤ (q.num * r.den : ℤ).natAbs + (r.num * q.den : ℤ).natAbs := Int.natAbs_add_le _ _
      _ = q.num.natAbs * r.den + r.num.natAbs * q.den := by simp [Int.natAbs_mul]
      _ ≤ B * C + C * B := Nat.add_le_add (Nat.mul_le_mul hq.1 hr.2) (Nat.mul_le_mul hr.1 hq.2)
      _ = _ := by ring
  refine ⟨hn.trans hb, ?_⟩
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hd'
  exact hd'.trans ((Nat.mul_le_mul hq.2 hr.2).trans (by nlinarith))

theorem height_neg (q : ℚ) (B : ℕ) (hq : Height q B) : Height (-q) B := by
  simpa only [Height, Rat.neg_num, Rat.neg_den, Int.natAbs_neg] using hq

theorem height_inv (q : ℚ) (B : ℕ) (hq : Height q B) : Height q⁻¹ B := by
  have hB : 1 ≤ B := le_trans q.den_pos hq.2
  by_cases hz : q = 0
  · subst q
    simpa using height_mono 0 height_zero hB
  · have hnum : (q⁻¹).num.natAbs ≤ q.den := by
      rw [Rat.num_inv, Int.natAbs_mul]
      have hs : q.num.sign.natAbs ≤ 1 := by
        have hsign := Int.sign_trichotomy q.num
        rcases hsign with h | h | h <;> rw [h] <;> norm_num
      simpa using Nat.mul_le_mul_right q.den hs
    exact ⟨hnum.trans hq.2, by rw [Rat.den_inv_of_ne_zero hz]; exact hq.1⟩

theorem height_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (B : ℕ)
    (hf : ∀ i ∈ s, Height (f i) B) :
    Height (∑ i ∈ s, f i) ((2 * B) ^ s.card) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using height_zero
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, pow_succ]
    have h := height_add (f i) (∑ j ∈ s, f j) B ((2 * B) ^ s.card)
      (hf i (Finset.mem_insert_self _ _)) (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    convert h using 1
    ring

theorem height_encoding (q : ℚ) (B : ℕ) (hq : Height q B) :
    bitSize (encodeRational q) ≤ 4 + 2 * B.size := by
  have hn := Nat.size_le_size hq.1
  have hd := Nat.size_le_size hq.2
  have he := EncodingSize.rational_size_upper q
  omega

end Lax109476Proofs.RationalArithmeticBounds

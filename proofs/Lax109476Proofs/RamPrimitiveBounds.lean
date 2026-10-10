import Lax109476Proofs.RamRounding
import Lax109476Proofs.RamComparison
import Lax109476Proofs.RationalArithmeticBounds

namespace Lax109476Proofs.RamPrimitiveBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRounding RationalSizeBounds RationalArithmeticBounds

theorem fractionValue_height (s n d M : ℕ) (hn : n ≤ M) (hd : d ≤ M) (hdpos : 0 < d) :
    Height (fractionValue s n d) M := by
  obtain ⟨hnum, hden⟩ := fractionValue_num_den s n d hdpos
  exact ⟨by rw [hnum]; exact (Nat.div_le_self _ _).trans hn,
    by rw [hden]; exact (Nat.div_le_self _ _).trans hd⟩

theorem upperMagnitude_le (s n d D M : ℕ) (hn : n ≤ M) (hD : D ≤ M) :
    upperMagnitude s n d D ≤ M ^ 3 + 1 := by
  have ha : n * D ^ 2 ≤ M ^ 3 := by
    calc
      _ ≤ M * M ^ 2 := Nat.mul_le_mul hn (Nat.pow_le_pow_left hD 2)
      _ = _ := by ring
  have hq := Nat.div_le_self (n * D ^ 2) d
  unfold upperMagnitude ceilQuotient
  split_ifs <;> omega

theorem upperMagnitude_size (s n d D M : ℕ) (hn : n ≤ M) (hD : D ≤ M) :
    (upperMagnitude s n d D).size ≤ 3 * M.size + 2 := by
  have hs := Nat.size_le_size (upperMagnitude_le s n d D M hn hD)
  have hp := size_pow_le M 3
  have ha := size_add_one_le (M ^ 3)
  omega

/-- One uniform cost bound for every bounded input pair, suitable for loop
invariants whose operands change on each iteration. -/
theorem multiplyFraction_uniform_spec (B M s₁ n₁ d₁ s₂ n₂ d₂ : ℕ)
    (hB : 2 * M ^ 2 + 3 < B) (hs₁ : s₁ ≤ 1) (hs₂ : s₂ ≤ 1)
    (hn₁ : n₁ ≤ M) (hd₁ : d₁ ≤ M) (hn₂ : n₂ ≤ M) (hd₂ : d₂ ≤ M)
    (hd₁pos : 0 < d₁) (hd₂pos : 0 < d₂) :
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) multiplyFraction
      (fun _ τ => FractionOutput (fractionValue s₁ n₁ d₁ * fractionValue s₂ n₂ d₂) τ)
      (72 * M.size + 64) := by
  apply (multiplyFraction_spec B M s₁ n₁ d₁ s₂ n₂ d₂ hB hs₁ hs₂ hn₁ hd₁ hn₂ hd₂
    hd₁pos hd₂pos).mono
  have hs := size_mul_le d₁ d₂
  have h₁ := Nat.size_le_size hd₁
  have h₂ := Nat.size_le_size hd₂
  omega

theorem addFraction_uniform_spec (B M s₁ n₁ d₁ s₂ n₂ d₂ : ℕ)
    (hB : 2 * M ^ 2 + 3 < B) (hs₁ : s₁ ≤ 1) (hs₂ : s₂ ≤ 1)
    (hn₁ : n₁ ≤ M) (hd₁ : d₁ ≤ M) (hn₂ : n₂ ≤ M) (hd₂ : d₂ ≤ M)
    (hd₁pos : 0 < d₁) (hd₂pos : 0 < d₂) :
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) addFraction
      (fun _ τ => FractionOutput (fractionValue s₁ n₁ d₁ + fractionValue s₂ n₂ d₂) τ)
      (72 * M.size + 96) := by
  apply (addFraction_spec B M s₁ n₁ d₁ s₂ n₂ d₂ hB hs₁ hs₂ hn₁ hd₁ hn₂ hd₂
    hd₁pos hd₂pos).mono
  have hs := size_mul_le d₁ d₂
  have h₁ := Nat.size_le_size hd₁
  have h₂ := Nat.size_le_size hd₂
  omega

theorem roundFraction_uniform_spec (B M s n d D : ℕ) (hB : 2 * M ^ 2 + 3 < B)
    (hs : s ≤ 1) (hn : n ≤ M) (hd : d ≤ M) (hD : D ≤ M)
    (hdpos : 0 < d) (hDpos : 0 < D) :
    Spec B (fun σ => σ.vars "left.s" = s ∧ σ.vars "left.n" = n ∧
      σ.vars "left.d" = d ∧ σ.vars "grid.D" = D) roundFraction
      (fun _ τ => FractionOutput (RationalRounding.roundDown (fractionValue s n d) D) τ)
      (36 * M.size + 96) := by
  apply (roundFraction_spec B M s n d D hB hs hn hd hD hdpos hDpos).mono
  have hs := Nat.size_le_size hD
  omega

theorem upperRootFraction_uniform_spec (B M s n d D : ℕ)
    (hB : (2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3 < B)
    (hs : s ≤ 1) (hn : n ≤ M) (hd : d ≤ M) (hD : D ≤ M)
    (hdpos : 0 < d) (hDpos : 0 < D) :
    Spec B (fun σ => σ.vars "left.s" = s ∧ σ.vars "left.n" = n ∧
      σ.vars "left.d" = d ∧ σ.vars "grid.D" = D) upperRootFraction
      (fun _ τ => FractionOutput (RationalRounding.sqrtUpper (fractionValue s n d) D) τ)
      (114 * M.size + 180) := by
  apply (upperRootFraction_spec B M s n d D hB hs hn hd hD hdpos hDpos).mono
  have hs := upperMagnitude_size s n d D M hn hD
  have hds := Nat.size_le_size hD
  omega

end Lax109476Proofs.RamPrimitiveBounds

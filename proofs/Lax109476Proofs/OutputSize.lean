import Lax109476.RamOutputSize
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

namespace Lax109476Proofs.OutputSize

open Lax808846.Ram Lax759944.RamPolytime Lax759944.BinaryWordEncoding

private theorem effect_output_length (w : ℕ) (i : Instr) (s s' : State)
    (h : i.effect w s = some s') : s'.out.length ≤ s.out.length + 1 := by
  cases i <;> simp_all [Instr.effect] <;> try (subst s'; simp)
  rcases h with ⟨v, _, h⟩
  subst s'
  simp

private theorem step_output_length (w : ℕ) (p : Program) (s s' : State)
    (h : step w p s = some s') : s'.out.length ≤ s.out.length + 1 := by
  unfold step at h
  cases he : p[s.pc]? with
  | none => simp [he] at h
  | some i =>
      simp only [he, Option.bind_some] at h
      exact effect_output_length w i s s' h

private theorem run_output_length (w : ℕ) (p : Program) (k : ℕ) (s s' : State)
    (h : run w p k s = some s') : s'.out.length ≤ s.out.length + k := by
  induction k generalizing s with
  | zero => simp_all [run]
  | succ k ih =>
      cases he : step w p s with
      | none => simp [run, he] at h
      | some next =>
          simp only [run, he, Option.bind_some] at h
          have hk := ih next h
          have hs := step_output_length w p s next he
          omega

private theorem runsTo_output_length (w : ℕ) (p : Program)
    (x y : List ℕ) (t : ℕ) (h : RunsTo w p x y t) : y.length ≤ t := by
  rcases h with ⟨k, s, hk, _, hout, rfl⟩
  have hlen := run_output_length w p k (initState x) s hk
  simp only [initState, List.length_nil, zero_add] at hlen
  rw [← hout]
  omega

private theorem fitting_bitSize (w : ℕ) (x : List ℕ) (h : FitsInWords w x) :
    bitSize x ≤ x.length * (w + 1) := by
  induction x with
  | nil => simp [bitSize, encode]
  | cons a x ih =>
      have ha : a.size ≤ w := Nat.size_le.mpr (h a (by simp))
      have hx : FitsInWords w x := fun b hb => h b (by simp [hb])
      have hi := ih hx
      simp only [bitSize, encode, List.flatMap_cons, List.length_append,
        encodeNat, List.length_cons, List.length_map, Nat.size_eq_bits_len] at *
      nlinarith

private theorem polynomial_power_bound (p : Polynomial ℕ) :
    ∃ C k : ℕ, 0 < C ∧ ∀ x : ℕ, p.eval x ≤ C * (x + 1) ^ k := by
  induction p using Polynomial.induction_on' with
  | monomial n a =>
      refine ⟨a + 1, n, by omega, ?_⟩
      intro x
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) n)
  | add p q hp hq =>
      obtain ⟨C, k, hC, hp⟩ := hp
      obtain ⟨D, l, hD, hq⟩ := hq
      refine ⟨C + D, k + l, by omega, ?_⟩
      intro x
      have hk : (x + 1) ^ k ≤ (x + 1) ^ (k + l) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hl : (x + 1) ^ l ≤ (x + 1) ^ (k + l) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      rw [Polynomial.eval_add, add_mul]
      exact Nat.add_le_add ((hp x).trans (Nat.mul_le_mul_left C hk))
        ((hq x).trans (Nat.mul_le_mul_left D hl))

/--
---
conclusion: Lax109476.RamOutputSize.exists_polynomial_output_bound
---
Induction on the registered RAM execution shows that output length is at
most the number of executed instructions. Every output entry fits in the
polynomially bounded word length, so its binary representation plus its
separator uses at most that word length plus one symbols. Multiply the
runtime and word-length bounds, then bound the resulting natural-coefficient
polynomial by a fixed multiple of a power of input size plus one.
-/
theorem ram_polynomial_output_size :
    ∀ f : List ℕ → List ℕ, RamPolytime f →
      ∃ C k : ℕ, 0 < C ∧ ∀ x : List ℕ,
        bitSize (f x) ≤ C * (bitSize x + 1) ^ k := by
  intro f ⟨p, wordBound, timeBound, hf⟩
  obtain ⟨C, k, hC, hpoly⟩ := polynomial_power_bound (timeBound * (wordBound + 1))
  refine ⟨C, k, hC, ?_⟩
  intro x
  obtain ⟨hfits, hrun⟩ := hf x
  obtain ⟨t, ht, hrun⟩ := hrun (wordBound.eval (bitSize x)) le_rfl
  have hout : FitsInWords (wordBound.eval (bitSize x)) (f x) := by
    intro a ha
    exact hfits a (List.mem_append_right _ ha)
  calc
    bitSize (f x) ≤ (f x).length * (wordBound.eval (bitSize x) + 1) :=
      fitting_bitSize _ _ hout
    _ ≤ timeBound.eval (bitSize x) * (wordBound.eval (bitSize x) + 1) :=
      Nat.mul_le_mul_right _ ((runsTo_output_length _ _ _ _ _ hrun).trans ht)
    _ = (timeBound * (wordBound + 1)).eval (bitSize x) := by simp
    _ ≤ C * (bitSize x + 1) ^ k := hpoly _


end Lax109476Proofs.OutputSize

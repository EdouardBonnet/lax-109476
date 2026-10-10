import Lax109476Proofs.RamBitLength
import Mathlib.Data.Nat.Factorial.Basic

namespace Lax109476Proofs.RamNaturalPower

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def powerInvariant (a n : ℕ) (σ : Env) : Prop :=
  σ.vars "power.base" = a ∧ σ.vars "power.exponent" = n ∧
    σ.vars "power.i" ≤ n ∧ σ.vars "power.value" = a ^ σ.vars "power.i"

def powerStep : Com := .seq
  (.assign "power.value" (.mul (.var "power.value") (.var "power.base")))
  (.assign "power.i" (.add (.var "power.i") (.lit 1)))

theorem powerStep_spec (B a n : ℕ) (ha : 1 ≤ a) (haB : a < B)
    (hnB : n < B) (hpB : a ^ n < B) :
    Spec B (fun σ => powerInvariant a n σ ∧ σ.vars "power.i" < n) powerStep
      (fun σ τ => powerInvariant a n τ ∧ τ.vars "power.i" = σ.vars "power.i" + 1) 8 := by
  rintro σ ⟨⟨hσa, hσn, hσiN, hσp⟩, hσi⟩
  have hiB : σ.vars "power.i" < B := hσi.trans hnB
  have hnextB : a ^ (σ.vars "power.i" + 1) < B :=
    (Nat.pow_le_pow_right ha hσi).trans_lt hpB
  have hcurB : a ^ σ.vars "power.i" < B :=
    (Nat.pow_le_pow_right ha hσiN).trans_lt hpB
  have hmulB : σ.vars "power.value" * σ.vars "power.base" < B := by
    rw [hσp, hσa, ← pow_succ]
    exact hnextB
  have h1 : 1 < B := ha.trans_lt haB
  run_vcg
  all_goals simp_all [powerInvariant, pow_succ]

def power : Com := .seq (.assign "power.value" (.lit 1))
  (.seq (.assign "power.i" (.lit 0))
    (.while (.lt (.var "power.i") (.var "power.exponent")) powerStep))

theorem power_spec (B a n : ℕ) (ha : 1 ≤ a) (haB : a < B)
    (hnB : n < B) (hpB : a ^ n < B) :
    Spec B (fun σ => σ.vars "power.base" = a ∧ σ.vars "power.exponent" = n) power
      (fun _ τ => τ.vars "power.value" = a ^ n ∧
        τ.vars "power.base" = a ∧ τ.vars "power.exponent" = n) (12 * n + 8) := by
  have hlo := Spec.forRangeZero "power.i" "power.exponent" (powerInvariant a n) n 8 hnB
    (fun _ h => h.2.2.1) (fun _ h => h.2.1) (powerStep_spec B a n ha haB hnB hpB)
  have h1 : 1 < B := ha.trans_lt haB
  rintro σ ⟨hσa, hσn⟩
  run_vcg [hlo]
  all_goals clear hlo
  all_goals simp_all [powerInvariant]

def factorialInvariant (n : ℕ) (σ : Env) : Prop :=
  σ.vars "factorial.n" = n ∧ σ.vars "factorial.i" ≤ n ∧
    σ.vars "factorial.value" = (σ.vars "factorial.i").factorial

def factorialStep : Com := .seq
  (.assign "factorial.i" (.add (.var "factorial.i") (.lit 1)))
  (.assign "factorial.value" (.mul (.var "factorial.value") (.var "factorial.i")))

theorem factorialStep_spec (B n : ℕ) (hnB : n < B) (hfB : n.factorial < B) :
    Spec B (fun σ => factorialInvariant n σ ∧ σ.vars "factorial.i" < n) factorialStep
      (fun σ τ => factorialInvariant n τ ∧ τ.vars "factorial.i" = σ.vars "factorial.i" + 1) 8 := by
  rintro σ ⟨⟨hσn, hσiN, hσf⟩, hσi⟩
  have h1 : 1 < B := lt_of_le_of_lt (Nat.factorial_pos n) hfB
  have hiB : σ.vars "factorial.i" < B := hσi.trans hnB
  have hi1B : σ.vars "factorial.i" + 1 < B := lt_of_le_of_lt hσi hnB
  have hcurB : (σ.vars "factorial.i").factorial < B := (Nat.factorial_le hσiN).trans_lt hfB
  have hnextB : (σ.vars "factorial.i" + 1).factorial < B := (Nat.factorial_le hσi).trans_lt hfB
  have hmulB : σ.vars "factorial.value" * (σ.vars "factorial.i" + 1) < B := by
    rw [hσf, Nat.mul_comm, ← Nat.factorial_succ]
    exact hnextB
  run_vcg
  all_goals simp_all [factorialInvariant, Nat.factorial_succ, Nat.mul_comm]

def factorial : Com := .seq (.assign "factorial.value" (.lit 1))
  (.seq (.assign "factorial.i" (.lit 0))
    (.while (.lt (.var "factorial.i") (.var "factorial.n")) factorialStep))

theorem factorial_spec (B n : ℕ) (hnB : n < B) (hfB : n.factorial < B) :
    Spec B (fun σ => σ.vars "factorial.n" = n) factorial
      (fun _ τ => τ.vars "factorial.value" = n.factorial ∧ τ.vars "factorial.n" = n)
      (12 * n + 8) := by
  have hlo := Spec.forRangeZero "factorial.i" "factorial.n" (factorialInvariant n) n 8 hnB
    (fun _ h => h.2.1) (fun _ h => h.1) (factorialStep_spec B n hnB hfB)
  have h1 : 1 < B := lt_of_le_of_lt (Nat.factorial_pos n) hfB
  intro σ hσ
  run_vcg [hlo]
  all_goals clear hlo
  all_goals simp_all [factorialInvariant]

end Lax109476Proofs.RamNaturalPower

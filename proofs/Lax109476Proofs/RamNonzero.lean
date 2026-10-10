import Lax109476Proofs.RamRationalArrays
import Lax109476Proofs.RationalArithmeticBounds

namespace Lax109476Proofs.RamNonzero

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RationalArithmeticBounds

def before {n : ℕ} (v : Fin n → ℚ) (k : ℕ) : Prop := ∃ j, j.val < k ∧ v j ≠ 0

theorem before_zero {n : ℕ} (v : Fin n → ℚ) : ¬ before v 0 := by simp [before]

theorem before_succ {n : ℕ} (v : Fin n → ℚ) (i : Fin n) :
    before v (i.val + 1) ↔ before v i.val ∨ v i ≠ 0 := by
  constructor
  · rintro ⟨j, hj, hv⟩
    by_cases hji : j.val < i.val
    · exact Or.inl ⟨j, hji, hv⟩
    · have heq : j = i := Fin.ext (by omega)
      exact Or.inr (heq ▸ hv)
  · rintro (⟨j, hj, hv⟩ | hi)
    · exact ⟨j, by omega, hv⟩
    · exact ⟨i, by omega, hi⟩

def Invariant {n : ℕ} (a : String) (v : Fin n → ℚ) (σ : Env) : Prop :=
  Represents a (List.ofFn v) σ ∧ σ.vars "nonzero.flag" ≤ 1 ∧
    (σ.vars "nonzero.flag" = 1 ↔ before v (σ.vars "nonzero.i")) ∧
    σ.vars "nonzero.i" ≤ n ∧ σ.vars "vec.n" = n

def scanStep (a : String) : Com :=
  .seq (.ite (.lt (.lit 0) (.get (a ++ ".n") (.var "nonzero.i")))
    (.assign "nonzero.flag" (.lit 1)) .skip)
    (.assign "nonzero.i" (.add (.var "nonzero.i") (.lit 1)))

set_option maxHeartbeats 500000 in
theorem scanStep_spec (B n M : ℕ) (a : String) (v : Fin n → ℚ)
    (hnB : n < B) (h1 : 1 < B) (hMB : M < B) (hv : ∀ i, Height (v i) M) :
    Spec B (fun σ => Invariant a v σ ∧ σ.vars "nonzero.i" < n) (scanStep a)
      (fun σ τ => Invariant a v τ ∧ τ.vars "nonzero.i" = σ.vars "nonzero.i" + 1) 12 := by
  rintro σ ⟨⟨hσv, hσflag, hσbefore, hσiN, hσn⟩, hσi⟩
  let i : Fin n := ⟨σ.vars "nonzero.i", hσi⟩
  have hiB : σ.vars "nonzero.i" < B := hσi.trans hnB
  have hi1B : σ.vars "nonzero.i" + 1 < B := lt_of_le_of_lt hσi hnB
  have hnumB : (v i).num.natAbs < B := (hv i).1.trans_lt hMB
  have hlen : σ.vars "nonzero.i" < (σ.arrs (a ++ ".n")).length := by
    rw [hσv.2.1]
    simpa using hσi
  have hget : (σ.arrs (a ++ ".n")).getD (σ.vars "nonzero.i") 0 = (v i).num.natAbs := by
    rw [hσv.2.1, map_getD _ _ _ (by simpa using hσi)]
    simp [i]
  have hne : 0 < (v i).num.natAbs ↔ v i ≠ 0 := by
    rw [Nat.pos_iff_ne_zero, Int.natAbs_ne_zero, Rat.num_ne_zero]
  have hnext := before_succ v i
  have h0 : 0 < B := by omega
  run_vcg
  all_goals simp_all [Invariant, Represents, hne, hnext, i]
  all_goals aesop

def scanLoop (a : String) : Com := .seq (.assign "nonzero.i" (.lit 0))
  (.while (.lt (.var "nonzero.i") (.var "vec.n")) (scanStep a))

def scan (a : String) : Com := .seq (.assign "nonzero.flag" (.lit 0)) (scanLoop a)

theorem scan_spec (B n M : ℕ) (a : String) (v : Fin n → ℚ)
    (hnB : n < B) (h1 : 1 < B) (hMB : M < B) (hv : ∀ i, Height (v i) M) :
    Spec B (fun σ => Represents a (List.ofFn v) σ ∧ σ.vars "vec.n" = n) (scan a)
      (fun _ τ => τ.vars "nonzero.flag" ≤ 1 ∧ (τ.vars "nonzero.flag" = 1 ↔ v ≠ 0) ∧
        Represents a (List.ofFn v) τ ∧ τ.vars "vec.n" = n) (16 * n + 8) := by
  have hlo := Spec.forRangeZero "nonzero.i" "vec.n" (Invariant a v) n 12 hnB
    (fun _ h => h.2.2.2.1) (fun _ h => h.2.2.2.2) (scanStep_spec B n M a v hnB h1 hMB hv)
  have hdone : before v n ↔ v ≠ 0 := by
    simp only [before, Fin.isLt, true_and]
    rw [ne_eq, funext_iff]
    push Not
    rfl
  have hloop : Spec B (fun σ => Represents a (List.ofFn v) σ ∧ σ.vars "vec.n" = n ∧
        σ.vars "nonzero.flag" = 0)
      (scanLoop a)
      (fun _ τ => τ.vars "nonzero.flag" ≤ 1 ∧ (τ.vars "nonzero.flag" = 1 ↔ v ≠ 0) ∧
        Represents a (List.ofFn v) τ ∧ τ.vars "vec.n" = n) (16 * n + 6) := by
    refine (hlo.pre ?_).post ?_
    · rintro σ ⟨hv', hn, hflag⟩
      simp_all [Invariant, Represents, before_zero]
    · rintro σ τ _ ⟨hτ, hi⟩
      exact ⟨hτ.2.1, by simpa only [hi, hdone] using hτ.2.2.1, hτ.1, hτ.2.2.2.2⟩
  rintro σ ⟨hσv, hσn⟩
  run_vcg [hloop]
  all_goals clear hloop hlo
  all_goals simp_all [Represents]

end Lax109476Proofs.RamNonzero

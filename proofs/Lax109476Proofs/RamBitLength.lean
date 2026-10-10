import Lax109476Proofs.RamArithmetic
import Lax109476Proofs.RationalSizeBounds

namespace Lax109476Proofs.RamBitLength

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem size_half_succ (n : ℕ) (hn : 0 < n) : (n / 2).size + 1 = n.size := by
  induction n using Nat.binaryRec' with
  | zero => omega
  | bit b n h _ =>
    rw [Nat.bit_div_two, Nat.size_bit (Nat.bit_ne_zero_iff.mpr h)]

def bitLengthStep : Com :=
  .seq (.assign "bits.v" (.div (.var "bits.v") (.lit 2)))
    (.assign "bits.k" (.add (.var "bits.k") (.lit 1)))

def bitLengthLoop : Com := .while (.lt (.lit 0) (.var "bits.v")) bitLengthStep

def bitLength : Com :=
  .seq (.assign "bits.k" (.lit 0)) bitLengthLoop

theorem bitLengthStep_spec (B v k : ℕ) (hB : 2 < B) (hv : v < B)
    (hk : k + 1 < B) :
    Spec B (fun σ => σ.vars "bits.v" = v ∧ σ.vars "bits.k" = k) bitLengthStep
      (fun _ σ' => σ'.vars "bits.v" = v / 2 ∧ σ'.vars "bits.k" = k + 1) 8 := by
  have hdiv : v / 2 < B := (Nat.div_le_self _ _).trans_lt hv
  rintro σ ⟨hσv, hσk⟩
  run_vcg
  all_goals simp_all

/-- Count bits by successive halving. The counter is bounded by the original
input, including at zero, and the instruction count is linear in bit length. -/
theorem bitLengthLoop_spec (B n : ℕ) (hB : 2 < B) (hn : n < B) :
    Spec B (fun σ => σ.vars "bits.v" = n ∧ σ.vars "bits.k" = 0) bitLengthLoop
      (fun _ σ' => σ'.vars "bits.v" = 0 ∧ σ'.vars "bits.k" = n.size)
      (12 * n.size + 4) := by
  let I := fun σ : Env => σ.vars "bits.v" ≤ n ∧
    σ.vars "bits.k" + (σ.vars "bits.v").size = n.size
  have hloop : Spec B (fun σ => σ.vars "bits.v" = n ∧ σ.vars "bits.k" = 0)
      bitLengthLoop (fun _ σ' => I σ' ∧
        (Cond.lt (.lit 0) (.var "bits.v")).evalB B σ' = some false)
      (12 * n.size + 4) := by
    apply Spec.while_count I (fun σ => (σ.vars "bits.v").size) 8
    · intro σ hI
      exact ⟨_, evalB_condLt (evalB_lit (by omega)) (evalB_var (hI.1.trans_lt hn))⟩
    · rintro σ ⟨hI, hc⟩
      have hvpos : 0 < σ.vars "bits.v" := by
        rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (hI.1.trans_lt hn))] at hc
        simpa using hc
      have hs := size_half_succ (σ.vars "bits.v") hvpos
      have hsize := RationalSizeBounds.size_le_self n
      have hk : σ.vars "bits.k" + 1 < B := by
        have hp := Nat.size_pos.mpr hvpos
        dsimp [I] at hI
        omega
      obtain ⟨τ, hr, hτv, hτk⟩ := bitLengthStep_spec B _ _ hB (hI.1.trans_lt hn) hk
        σ ⟨rfl, rfl⟩
      refine ⟨τ, hr, ?_, ?_⟩
      · dsimp [I] at hI ⊢
        rw [hτv, hτk]
        exact ⟨(Nat.div_le_self _ _).trans hI.1, by omega⟩
      · rw [hτv]; omega
    · rintro σ ⟨hσv, hσk⟩
      simp [I, hσv, hσk]
    · rintro σ ⟨hσv, _⟩
      simp only [hσv, Cond.size, Expr.size]
      omega
  apply hloop.post
  rintro σ τ _ ⟨hI, hc⟩
  have hz : τ.vars "bits.v" = 0 := by
    rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (hI.1.trans_lt hn))] at hc
    have h : ¬ 0 < τ.vars "bits.v" := of_decide_eq_false (Option.some.inj hc)
    omega
  exact ⟨hz, by simpa [I, hz] using hI.2⟩

theorem bitLength_spec (B n : ℕ) (hB : 2 < B) (hn : n < B) :
    Spec B (fun σ => σ.vars "bits.v" = n) bitLength
      (fun _ σ' => σ'.vars "bits.v" = 0 ∧ σ'.vars "bits.k" = n.size)
      (12 * n.size + 6) := by
  have hl := bitLengthLoop_spec B n hB hn
  run_vcg [hl]
  all_goals simp_all

end Lax109476Proofs.RamBitLength

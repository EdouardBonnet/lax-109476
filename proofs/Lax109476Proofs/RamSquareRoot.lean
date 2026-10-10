import Lax109476Proofs.RamArithmetic
import Mathlib.Data.Nat.Sqrt

namespace Lax109476Proofs.RamSquareRoot

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamArithmetic

def sqrtStep : Com :=
  .seq (.assign "sqrt.mid" (.div (.add (.var "sqrt.lo") (.var "sqrt.hi")) (.lit 2)))
    (.ite (.lt (.var "sqrt.n") (.mul (.var "sqrt.mid") (.var "sqrt.mid")))
      (.assign "sqrt.hi" (.var "sqrt.mid")) (.assign "sqrt.lo" (.var "sqrt.mid")))

def sqrtLoop : Com :=
  .while (.lt (.lit 1) (.sub (.var "sqrt.hi") (.var "sqrt.lo"))) sqrtStep

def squareRoot : Com :=
  .seq (.assign "sqrt.lo" (.lit 0))
    (.seq (.assign "sqrt.hi" (.add (.var "sqrt.n") (.lit 1))) sqrtLoop)

theorem sqrtStep_spec (B N l u : ℕ) (hB : (2 * (N + 1) + 1) ^ 2 < B)
    (hlu : l < u) (hu : u ≤ N + 1) (hwide : 1 < u - l)
    (hl : l * l ≤ N) (hun : N < u * u) :
    Spec B (fun σ => σ.vars "sqrt.n" = N ∧ σ.vars "sqrt.lo" = l ∧ σ.vars "sqrt.hi" = u)
      sqrtStep (fun _ σ' => σ'.vars "sqrt.n" = N ∧
        σ'.vars "sqrt.lo" < σ'.vars "sqrt.hi" ∧ σ'.vars "sqrt.hi" ≤ N + 1 ∧
        σ'.vars "sqrt.lo" * σ'.vars "sqrt.lo" ≤ N ∧
        N < σ'.vars "sqrt.hi" * σ'.vars "sqrt.hi" ∧
        (σ'.vars "sqrt.hi" - σ'.vars "sqrt.lo" - 1).size < (u - l - 1).size) 20 := by
  let m := (l + u) / 2
  have hquot := Nat.div_add_mod (l + u) 2
  have hrem : (l + u) % 2 < 2 := Nat.mod_lt _ (by decide)
  have hm : l < m ∧ m < u := by dsimp [m]; omega
  have hN : N < B := by nlinarith
  have hlB : l < B := by nlinarith
  have huB : u < B := by nlinarith
  have hsum : l + u < B := by nlinarith
  have hmB : m < B := hm.2.trans huB
  have hmSq : m * m < B := by nlinarith
  have h2 : 2 < B := by nlinarith
  have hdropLeft : m - l - 1 ≤ (u - l - 1) / 2 := by dsimp [m]; omega
  have hdropRight : u - m - 1 ≤ (u - l - 1) / 2 := by dsimp [m]; omega
  have hgap : 0 < u - l - 1 := by omega
  have hsLeft := (Nat.size_le_size hdropLeft).trans_lt (size_half_lt _ hgap)
  have hsRight := (Nat.size_le_size hdropRight).trans_lt (size_half_lt _ hgap)
  rintro σ ⟨hσn, hσl, hσu⟩
  run_vcg
  all_goals simp_all [m]
  all_goals omega

def SqrtInvariant (N : ℕ) (σ : Env) : Prop :=
  σ.vars "sqrt.n" = N ∧ σ.vars "sqrt.lo" < σ.vars "sqrt.hi" ∧
    σ.vars "sqrt.hi" ≤ N + 1 ∧
    σ.vars "sqrt.lo" * σ.vars "sqrt.lo" ≤ N ∧
    N < σ.vars "sqrt.hi" * σ.vars "sqrt.hi"

theorem sqrtLoop_spec (B N l u : ℕ) (hB : (2 * (N + 1) + 1) ^ 2 < B)
    (hlu : l < u) (hu : u ≤ N + 1) (hl : l * l ≤ N) (hun : N < u * u) :
    Spec B (fun σ => σ.vars "sqrt.n" = N ∧ σ.vars "sqrt.lo" = l ∧ σ.vars "sqrt.hi" = u)
      sqrtLoop (fun _ σ' => σ'.vars "sqrt.n" = N ∧
        σ'.vars "sqrt.lo" = Nat.sqrt N ∧ σ'.vars "sqrt.hi" = Nat.sqrt N + 1)
      (26 * (u - l - 1).size + 6) := by
  have h1 : 1 < B := by nlinarith
  have huB : N + 1 < B := by nlinarith
  have hdef (σ : Env) (hI : SqrtInvariant N σ) :
      ∃ v, (Cond.lt (.lit 1) (.sub (.var "sqrt.hi") (.var "sqrt.lo"))).evalB B σ = some v := by
    have hhi := hI.2.2.1.trans_lt huB
    have hlo := hI.2.1.trans hhi
    exact ⟨_, evalB_condLt (evalB_lit h1)
      (evalB_bin (evalB_var hhi) (evalB_var hlo) ((Nat.sub_le _ _).trans_lt hhi))⟩
  have hloop : Spec B
      (fun σ => σ.vars "sqrt.n" = N ∧ σ.vars "sqrt.lo" = l ∧ σ.vars "sqrt.hi" = u)
      sqrtLoop (fun _ σ' => SqrtInvariant N σ' ∧
        (Cond.lt (.lit 1) (.sub (.var "sqrt.hi") (.var "sqrt.lo"))).evalB B σ' = some false)
      (26 * (u - l - 1).size + 6) := by
    apply Spec.while_count (SqrtInvariant N)
      (fun σ => (σ.vars "sqrt.hi" - σ.vars "sqrt.lo" - 1).size) 20 hdef
    · rintro σ ⟨hI, hc⟩
      have hhi := hI.2.2.1.trans_lt huB
      have hlo := hI.2.1.trans hhi
      have hwide : 1 < σ.vars "sqrt.hi" - σ.vars "sqrt.lo" := by
        rw [evalB_condLt (evalB_lit h1)
          (evalB_bin (evalB_var hhi) (evalB_var hlo) ((Nat.sub_le _ _).trans_lt hhi))] at hc
        exact of_decide_eq_true (Option.some.inj hc)
      obtain ⟨τ, hr, hτ⟩ := sqrtStep_spec B N _ _ hB hI.2.1 hI.2.2.1 hwide
        hI.2.2.2.1 hI.2.2.2.2 σ ⟨hI.1, rfl, rfl⟩
      exact ⟨τ, hr, ⟨hτ.1, hτ.2.1, hτ.2.2.1, hτ.2.2.2.1, hτ.2.2.2.2.1⟩,
        hτ.2.2.2.2.2⟩
    · rintro σ ⟨hσn, hσl, hσu⟩
      simp only [SqrtInvariant, hσn, hσl, hσu]
      exact ⟨True.intro, hlu, hu, hl, hun⟩
    · rintro σ ⟨_, hσl, hσu⟩
      simp [hσl, hσu]
  apply hloop.post
  rintro σ τ _ ⟨hI, hc⟩
  have hhi := hI.2.2.1.trans_lt huB
  have hlo := hI.2.1.trans hhi
  have hnarrow : τ.vars "sqrt.hi" - τ.vars "sqrt.lo" ≤ 1 := by
    rw [evalB_condLt (evalB_lit h1)
      (evalB_bin (evalB_var hhi) (evalB_var hlo) ((Nat.sub_le _ _).trans_lt hhi))] at hc
    have hn := of_decide_eq_false (Option.some.inj hc)
    change ¬1 < τ.vars "sqrt.hi" - τ.vars "sqrt.lo" at hn
    omega
  have he : τ.vars "sqrt.hi" = τ.vars "sqrt.lo" + 1 := by have := hI.2.1; omega
  have hs : τ.vars "sqrt.lo" = Nat.sqrt N := Nat.eq_sqrt.mpr
    ⟨hI.2.2.2.1, by simpa only [he] using hI.2.2.2.2⟩
  exact ⟨hI.1, hs, by rw [he, hs]⟩

/-- The exact integer square root, with a linear bit-length cost and explicit
bounds on every intermediate product, compiled through Lax's RAM compiler. -/
theorem squareRoot_spec (B N : ℕ) (hB : (2 * (N + 1) + 1) ^ 2 < B) :
    Spec B (fun σ => σ.vars "sqrt.n" = N) squareRoot
      (fun _ σ' => σ'.vars "sqrt.lo" = Nat.sqrt N) (26 * N.size + 12) := by
  have hN : N < B := by nlinarith
  have h1 : 1 < B := by nlinarith
  have hNp : N + 1 < B := by nlinarith
  have hs := sqrtLoop_spec B N 0 (N + 1) hB (by omega) le_rfl
    (by simp) (by nlinarith)
  intro σ hσ
  run_vcg [hs]
  all_goals simp_all

end Lax109476Proofs.RamSquareRoot

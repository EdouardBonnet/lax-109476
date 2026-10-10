import Lax808846Proofs.Spec
import Mathlib.Tactic

namespace Lax109476Proofs.RamInput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- The physical length prefix makes end-of-input checks available to the
structured RAM program without reading from an exhausted tape. -/
def safeRead (x : String) : Com := .ite (.lt (.lit 0) (.var "input.remaining"))
  (.seq (.read x) (.assign "input.remaining" (.sub (.var "input.remaining") (.lit 1))))
  (.seq (.assign "input.valid" (.lit 0)) (.assign x (.lit 0)))

theorem safeRead_spec (B : ℕ) (x : String) (xs : List ℕ) (v : ℕ)
    (h1 : 1 < B) (hxsB : xs.length < B) (hv : v ≤ 1)
    (hxv : x ≠ "input.valid") (hxr : x ≠ "input.remaining") :
    Spec B (fun σ => σ.inp = xs ∧ σ.vars "input.remaining" = xs.length ∧
        σ.vars "input.valid" = v ∧ σ.InpBounded B)
      (safeRead x)
      (fun _ τ => τ.vars x = xs.headD 0 ∧ τ.inp = xs.tail ∧
        τ.vars "input.remaining" = xs.length - 1 ∧
        τ.vars "input.valid" = if xs = [] then 0 else v) 9 := by
  rintro σ ⟨hσinp, hσlen, hσvalid, hσbound⟩
  have hrv : "input.remaining" ≠ x := Ne.symm hxr
  have hvx : "input.valid" ≠ x := Ne.symm hxv
  cases xs with
  | nil =>
    have hb : (Cond.lt (.lit 0) (.var "input.remaining")).evalB B σ = some false := by
      simpa [hσlen] using (evalB_condLt (evalB_lit (by omega : 0 < B))
        (evalB_var (B := B) (σ := σ) (x := "input.remaining") (by simpa [hσlen] using hxsB)))
    have hr₁ : Run B (.assign "input.valid" (.lit 0)) σ (σ.setVar "input.valid" 0) 2 :=
      Run.assign (evalB_lit (by omega))
    have hr₂ : Run B (.assign x (.lit 0)) (σ.setVar "input.valid" 0)
        ((σ.setVar "input.valid" 0).setVar x 0) 2 := Run.assign (evalB_lit (by omega))
    refine ⟨_, (Run.ite_false hb (hr₁.seq hr₂)).mono (by simp only [Cond.size, Expr.size]; omega), ?_⟩
    simp_all [hxv, hxr, Env.setVar]
  | cons a rest =>
    have hrestB : rest.length < B := by simp only [List.length_cons] at hxsB; omega
    have haB : a < B := by
      apply hσbound a
      rw [hσinp]
      simp
    have hb : (Cond.lt (.lit 0) (.var "input.remaining")).evalB B σ = some true := by
      simpa [hσlen] using (evalB_condLt (evalB_lit (by omega : 0 < B))
        (evalB_var (B := B) (σ := σ) (x := "input.remaining") (by simpa [hσlen] using hxsB)))
    have hr₁ : Run B (.read x) σ {σ.setVar x a with inp := rest} 1 := Run.read hσinp
    have he : (Expr.sub (.var "input.remaining") (.lit 1)).evalB B {σ.setVar x a with inp := rest} =
        some rest.length := by
      have hvar : ({σ.setVar x a with inp := rest} : Env).vars "input.remaining" = rest.length + 1 := by
        simp [Env.setVar, hrv, hσlen]
      apply evalB_bin_iff.mpr
      refine ⟨rest.length + 1, 1, ?_, evalB_lit h1, by simp [Bop.apply], hrestB⟩
      apply evalB_var_iff.mpr
      exact ⟨hvar.symm, by rw [hvar]; exact hxsB⟩
    have hr₂ := Run.assign (x := "input.remaining") he
    refine ⟨_, (Run.ite_true hb (hr₁.seq hr₂)).mono (by simp only [Cond.size, Expr.size]; omega), ?_⟩
    simp_all [hxv, hxr, Env.setVar]

def startInput : Com := .seq (.read "input.remaining") (.assign "input.valid" (.lit 1))

theorem startInput_spec (B : ℕ) (xs : List ℕ) (h1 : 1 < B) :
    Spec B (fun σ => σ.inp = xs.length :: xs ∧ σ.InpBounded B) startInput
      (fun _ τ => τ.inp = xs ∧ τ.vars "input.remaining" = xs.length ∧
        τ.vars "input.valid" = 1 ∧ τ.InpBounded B ∧ xs.length < B) 3 := by
  rintro σ ⟨hinp, hbound⟩
  have hlenB : xs.length < B := hbound _ (by rw [hinp]; simp)
  have hr₁ : Run B (.read "input.remaining") σ {σ.setVar "input.remaining" xs.length with inp := xs} 1 :=
    Run.read hinp
  have hr₂ : Run B (.assign "input.valid" (.lit 1)) {σ.setVar "input.remaining" xs.length with inp := xs}
      (({σ.setVar "input.remaining" xs.length with inp := xs} : Env).setVar "input.valid" 1) 2 :=
    Run.assign (evalB_lit h1)
  have hr := hr₁.seq hr₂
  refine ⟨_, hr, ?_, ?_, ?_, hr.inpBounded hbound, hlenB⟩
  all_goals simp [Env.setVar]

end Lax109476Proofs.RamInput

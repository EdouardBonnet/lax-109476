import Lax109476Proofs.RamScalarFrame

namespace Lax109476Proofs.RamResultNegation

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface

def negateResult : Com := .assign "rat.s" (.sub (.lit 1) (.var "rat.s"))

theorem negateResult_spec (B : ℕ) (q : ℚ) (h1 : 1 < B) :
    Spec B (FractionOutput q) negateResult (fun _ τ => FractionOutput (-q) τ) 4 := by
  rintro σ ⟨hval, hn, hd, hs⟩
  have hsB : σ.vars "rat.s" < B := hs.trans_lt h1
  have hflip := fractionValue_flip (σ.vars "rat.s") (σ.vars "rat.n") (σ.vars "rat.d") hs
  rw [hval] at hflip
  run_vcg
  all_goals simp_all [FractionOutput]

end Lax109476Proofs.RamResultNegation

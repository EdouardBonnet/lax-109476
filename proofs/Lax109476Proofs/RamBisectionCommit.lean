import Lax109476Proofs.RamScalarCopy
import Lax109476Proofs.RamRationalMidpoint

namespace Lax109476Proofs.RamBisectionCommit

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RamRationalScalars RamScalarFrame

def condition : Cond := .eq (.var "search.found") (.lit 1)

def commit : Com := .ite condition (RamScalarCopy.copy "bisect.mid" "bisect.hi")
  (RamScalarCopy.copy "bisect.mid" "bisect.lo")

theorem commit_spec (B : ℕ) (l u t : ℚ) (answer : Bool) (h1 : 1 < B)
    (hn : t.num.natAbs < B) (hd : t.den < B) :
    Spec B (fun σ => Value "bisect.lo" l σ ∧ Value "bisect.hi" u σ ∧ Value "bisect.mid" t σ ∧
      condition.evalB B σ = some answer) commit
      (fun _ τ => Value "bisect.lo" (if answer then l else t) τ ∧
        Value "bisect.hi" (if answer then t else u) τ) 10 := by
  rintro σ ⟨hσl, hσu, hσt, hσanswer⟩
  cases answer with
  | true =>
    obtain ⟨τ, hr, hτ⟩ := RamScalarCopy.copy_spec B "bisect.mid" "bisect.hi" t h1 hn hd
      (by simp [RamCopy.Disjoint, RamCopy.suffixes]) σ hσt
    exact ⟨τ, Run.ite_true hσanswer hr,
      value_frame hr "bisect.lo" l hσl (by decide) (by decide) (by decide), hτ⟩
  | false =>
    obtain ⟨τ, hr, hτ⟩ := RamScalarCopy.copy_spec B "bisect.mid" "bisect.lo" t h1 hn hd
      (by simp [RamCopy.Disjoint, RamCopy.suffixes]) σ hσt
    exact ⟨τ, Run.ite_false hσanswer hr, hτ,
      value_frame hr "bisect.hi" u hσu (by decide) (by decide) (by decide)⟩

end Lax109476Proofs.RamBisectionCommit

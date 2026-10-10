import Lax109476Proofs.RamRational
import Lax109476.RationalEncoding

namespace Lax109476Proofs.RamEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open Lax109476.RationalEncoding

theorem fractionValue_sign (s n d : ℕ) (hs : s ≤ 1) (hd : 0 < d) :
    (if (fractionValue s n d).num < 0 then 1 else 0 : ℕ) =
      if n = 0 then 0 else s := by
  have hscases : s = 0 ∨ s = 1 := by omega
  rcases hscases with rfl | rfl
  · have hq : 0 ≤ fractionValue 0 n d := by change (0 : ℚ) ≤ (n : ℚ) / d; positivity
    have hnum := Rat.num_nonneg.mpr hq
    simp [not_lt.mpr hnum]
  · by_cases hz : n = 0
    · simp [fractionValue, hz]
    · have hq : fractionValue 1 n d < 0 := by
        change -(n : ℚ) / d < 0
        have hp : (0 : ℚ) < (n : ℚ) / d := by positivity
        rw [neg_div]
        linarith
      have hnum : (fractionValue 1 n d).num < 0 := by
        rw [← not_le, Rat.num_nonneg]
        exact not_le_of_gt hq
      simp [hz, hnum]

/-- Emit the registered canonical triple, removing a possible internal
negative sign on zero. All three writes are part of the proved cost. -/
def writeReducedFraction : Com :=
  .seq (.ite (.eq (.var "rat.n") (.lit 0)) (.write (.lit 0)) (.write (.var "rat.s")))
    (.seq (.write (.var "rat.n")) (.write (.var "rat.d")))

theorem writeReducedFraction_spec (B : ℕ) (q : ℚ) (hB : 1 < B)
    (hn : q.num.natAbs < B) (hd : q.den < B) :
    Spec B (FractionOutput q) writeReducedFraction
      (fun σ τ => τ.out = σ.out ++ encodeRational q) 10 := by
  intro σ hσ
  obtain ⟨hv, hσn, hσd, hσs⟩ := hσ
  have hnB : σ.vars "rat.n" < B := hσn ▸ hn
  have hdB : σ.vars "rat.d" < B := hσd ▸ hd
  have hsB : σ.vars "rat.s" < B := hσs.trans_lt hB
  have hsign := fractionValue_sign (σ.vars "rat.s") (σ.vars "rat.n")
    (σ.vars "rat.d") hσs (hσd ▸ q.den_pos)
  rw [hv] at hsign
  run_vcg
  all_goals simp_all [encodeRational, List.append_assoc]

end Lax109476Proofs.RamEncoding

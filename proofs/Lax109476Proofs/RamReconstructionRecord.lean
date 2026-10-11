import Lax109476Proofs.RamConvergentCandidate
import Lax109476Proofs.ReconstructionPrefix

namespace Lax109476Proofs.RamReconstructionRecord

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RamRationalScalars RamScalarFrame

def Output (r : Option ℚ) (σ : Env) : Prop := match r with
  | none => σ.vars "recon.found" = 0
  | some q => σ.vars "recon.found" = 1 ∧ Value "recon.result" q σ

def record : Com := .seq (save "recon.result") (.assign "recon.found" (.lit 1))

theorem record_spec (B : ℕ) (q : ℚ) (h1 : 1 < B) (hn : q.num.natAbs < B) (hd : q.den < B) :
    Spec B (FractionOutput q) record (fun _ τ => Output (some q) τ) 8 := by
  intro σ hσ
  obtain ⟨τ, hr₁, hτ⟩ := save_spec B "recon.result" q h1 hn hd
    (by simp) σ hσ
  have hr₂ : Run B (.assign "recon.found" (.lit 1)) τ (τ.setVar "recon.found" 1) 2 :=
    Run.assign (evalB_lit h1)
  exact ⟨_, hr₁.seq hr₂, by simp [Output], value_frame hr₂ "recon.result" q hτ (by decide) (by decide) (by decide)⟩

def candidate : Com := .seq RamConvergentCandidate.testCandidate
  (.ite (.eq (.var "recon.accept") (.lit 1)) record .skip)

theorem candidate_spec (S K N j w D : ℕ) (l u : ℚ) (hu0 : 0 ≤ u)
    (hl : Height l (2 ^ S)) (hu : Height u (2 ^ S)) (hj : j ≤ K) (hN : K + 1 ≤ N)
    (hw : RamConvergentBounds.wordWidth S K ≤ w) (hDB : D < 2 ^ w) :
    Spec (2 ^ w) (fun σ => Value "recon.lo" l σ ∧ Value "recon.hi" u σ ∧
      σ.vars "recon.bound" = D ∧ σ.vars "recon.i" = j ∧ (σ.arrs "cf.stack").length = N ∧
      σ.vars "recon.found" = 0) candidate
      (fun _ τ => Output (if ReconstructionPrefix.acceptable l u D (RationalReconstruction.convergent u j)
        then some (RationalReconstruction.convergent u j) else none) τ)
      (RamConvergentBounds.instructionBound S K + 144) := by
  let q := RationalReconstruction.convergent u j
  let E := RamConvergentBounds.exponent S K
  have hheight : Height q (2 ^ E) := height_mono _
    (ContinuedFractionBounds.convergent_height u (2 ^ S) j hu0 hu)
    ((Nat.pow_le_pow_right (by positivity) (show j + 1 ≤ j + 2 by omega)).trans
      (RamConvergentBounds.intermediate_bound S K j hj))
  have hwD : RamDecoder.wordWidth E ≤ w := by dsimp only [E]; unfold RamConvergentBounds.wordWidth at hw; omega
  have hRB : 2 ^ E < 2 ^ w := Nat.pow_lt_pow_right (by decide)
    (by unfold RamDecoder.wordWidth at hwD; omega)
  have h1 : 1 < 2 ^ w := (Nat.one_le_pow _ _ (by decide)).trans_lt hRB
  rintro σ ⟨hσl, hσu, hσD, hσj, hσN, hσfound⟩
  obtain ⟨τ, hr₁, hτaccept, hτq⟩ := RamConvergentCandidate.testCandidate_spec S K N j w D l u hu0
    hl hu hj hN hw hDB σ ⟨hσl, hσu, hσD, hσj, hσN⟩
  have hτfound := (hr₁.frame_var "recon.found" (by decide)).trans hσfound
  have hflag : τ.vars "recon.accept" = if q.den ≤ D ∧ l ≤ q ∧ q ≤ u then 1 else 0 := hτaccept
  have hflagB : τ.vars "recon.accept" < 2 ^ w := by rw [hflag]; split_ifs <;> omega
  have hcond := evalB_condEq (evalB_var (B := 2 ^ w) (σ := τ) (x := "recon.accept") hflagB) (evalB_lit h1)
  by_cases hp : q.den ≤ D ∧ l ≤ q ∧ q ≤ u
  · have ht : (Cond.eq (.var "recon.accept") (.lit 1)).evalB (2 ^ w) τ = some true := by simpa [hflag, hp] using hcond
    obtain ⟨υ, hr₂, hυ⟩ := record_spec (2 ^ w) q h1 (hheight.1.trans_lt hRB) (hheight.2.trans_lt hRB) τ hτq
    refine ⟨υ, (hr₁.seq (Run.ite_true (d := .skip) ht hr₂)).mono (by simp only [Cond.size, Expr.size]; omega), ?_⟩
    change Output (if decide (q.den ≤ D ∧ l ≤ q ∧ q ≤ u) then some q else none) υ
    simpa [hp] using hυ
  · have ht : (Cond.eq (.var "recon.accept") (.lit 1)).evalB (2 ^ w) τ = some false := by simpa [hflag, hp] using hcond
    refine ⟨τ, (hr₁.seq (Run.ite_false (c := record) ht Run.skip)).mono
      (by simp only [Cond.size, Expr.size]; omega), ?_⟩
    change Output (if decide (q.den ≤ D ∧ l ≤ q ∧ q ≤ u) then some q else none) τ
    simpa [hp, Output] using hτfound

end Lax109476Proofs.RamReconstructionRecord

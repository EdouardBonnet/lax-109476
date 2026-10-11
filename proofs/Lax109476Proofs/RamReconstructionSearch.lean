import Lax109476Proofs.RamReconstructionRecord

namespace Lax109476Proofs.RamReconstructionSearch

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RamRationalScalars RamScalarFrame
open RamReconstructionRecord ReconstructionPrefix

def searchStep : Com := .seq (.ite (.eq (.var "recon.found") (.lit 1)) .skip candidate)
  (.assign "recon.i" (.add (.var "recon.i") (.lit 1)))

def Invariant (l u : ℚ) (D N K : ℕ) (σ : Env) : Prop :=
  Value "recon.lo" l σ ∧ Value "recon.hi" u σ ∧ σ.vars "recon.bound" = D ∧
    σ.vars "recon.limit" = K ∧ (σ.arrs "cf.stack").length = N ∧ σ.vars "recon.i" ≤ K ∧
    Output (scan l u D (σ.vars "recon.i")) σ

theorem output_frame {B k : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ k)
    (r : Option ℚ) (h : Output r σ) (hf : "recon.found" ∉ c.wvars)
    (hs : "recon.result.s" ∉ c.wvars) (hn : "recon.result.n" ∉ c.wvars)
    (hd : "recon.result.d" ∉ c.wvars) : Output r τ := by
  cases r with
  | none => exact (hr.frame_var _ hf).trans h
  | some q => exact ⟨(hr.frame_var _ hf).trans h.1, value_frame hr "recon.result" q h.2 hs hn hd⟩

set_option maxHeartbeats 800000 in
theorem searchStep_spec (S K N w D : ℕ) (l u : ℚ) (hu0 : 0 ≤ u)
    (hl : Height l (2 ^ S)) (hu : Height u (2 ^ S)) (hN : K + 1 ≤ N)
    (hw : RamConvergentBounds.wordWidth S K ≤ w) (hDB : D < 2 ^ w) :
    Spec (2 ^ w) (fun σ => Invariant l u D N K σ ∧ σ.vars "recon.i" < K)
      searchStep (fun σ τ => Invariant l u D N K τ ∧ τ.vars "recon.i" = σ.vars "recon.i" + 1)
      (RamConvergentBounds.instructionBound S K + 152) := by
  have hKB : K + 1 < 2 ^ w := (by unfold RamConvergentBounds.wordWidth at hw; omega : K + 1 ≤ w).trans_lt
    (Nat.lt_two_pow_self (n := w))
  have h1 : 1 < 2 ^ w := by omega
  rintro σ ⟨⟨hσl, hσu, hσD, hσK, hσN, hσi, hσout⟩, hi⟩
  let j := σ.vars "recon.i"
  have hphase : ∃ τ, Run (2 ^ w) (.ite (.eq (.var "recon.found") (.lit 1)) .skip candidate) σ τ
      (RamConvergentBounds.instructionBound S K + 148) ∧ Output (scan l u D (j + 1)) τ := by
    cases hp : scan l u D j with
    | none =>
      have hfound : σ.vars "recon.found" = 0 := by
        change Output (scan l u D j) σ at hσout
        simpa only [hp, Output] using hσout
      have hcond : (Cond.eq (.var "recon.found") (.lit 1)).evalB (2 ^ w) σ = some false := by
        simpa [hfound] using evalB_condEq (evalB_var (B := 2 ^ w) (σ := σ) (x := "recon.found") (by rw [hfound]; omega)) (evalB_lit h1)
      obtain ⟨τ, hr, ht⟩ := candidate_spec S K N j w D l u hu0 hl hu hσi hN hw hDB σ
        ⟨hσl, hσu, hσD, rfl, hσN, hfound⟩
      refine ⟨τ, (Run.ite_false (c := .skip) hcond hr).mono (by simp only [Cond.size, Expr.size]; omega), ?_⟩
      simpa only [scan_succ, hp] using ht
    | some q =>
      have hout : σ.vars "recon.found" = 1 ∧ Value "recon.result" q σ := by
        change Output (scan l u D j) σ at hσout
        simpa only [hp, Output] using hσout
      have hcond : (Cond.eq (.var "recon.found") (.lit 1)).evalB (2 ^ w) σ = some true := by
        simpa [hout.1] using evalB_condEq (evalB_var (B := 2 ^ w) (σ := σ) (x := "recon.found") (by rw [hout.1]; omega)) (evalB_lit h1)
      refine ⟨σ, (Run.ite_true (d := candidate) hcond Run.skip).mono
        (by simp only [Cond.size, Expr.size]; omega), ?_⟩
      simpa only [scan_succ, hp, Output] using hout
  obtain ⟨τ, hr₁, hτout⟩ := hphase
  have hτi : τ.vars "recon.i" = j := hr₁.frame_var _ (by decide)
  have hjB : j < 2 ^ w := hi.trans (by omega)
  have hsumB : Bop.add.apply (τ.vars "recon.i") 1 < 2 ^ w := by
    simpa [hτi] using (show j + 1 < 2 ^ w by dsimp only [j]; omega)
  have hr₂ : Run (2 ^ w) (.assign "recon.i" (.add (.var "recon.i") (.lit 1))) τ
      (τ.setVar "recon.i" (j + 1)) 4 := Run.assign (by
        simpa only [hτi, Bop.apply_add] using (evalB_bin
          (evalB_var (B := 2 ^ w) (σ := τ) (x := "recon.i") (hτi ▸ hjB)) (evalB_lit h1) hsumB))
  have hr := hr₁.seq hr₂
  have hout := output_frame hr₂ (scan l u D (j + 1)) hτout (by decide) (by decide) (by decide) (by decide)
  refine ⟨_, hr, ⟨value_frame hr "recon.lo" l hσl (by decide) (by decide) (by decide),
    value_frame hr "recon.hi" u hσu (by decide) (by decide) (by decide),
    (hr.frame_var _ (by decide)).trans hσD, (hr.frame_var _ (by decide)).trans hσK,
    ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨t, _, ht⟩ := hr.bigStep
    exact (RamAdvanceState.array_length_of_bigStep ht "cf.stack").trans hσN
  · change j + 1 ≤ K; omega
  · simpa only [vars_setVar, ite_true] using hout
  · simp [j]

def search : Com := .seq (.assign "recon.found" (.lit 0))
  (.seq (.assign "recon.i" (.lit 0))
    (.while (.lt (.var "recon.i") (.var "recon.limit")) searchStep))

theorem search_spec (S K N w D : ℕ) (l u : ℚ) (hu0 : 0 ≤ u)
    (hl : Height l (2 ^ S)) (hu : Height u (2 ^ S)) (hN : K + 1 ≤ N)
    (hw : RamConvergentBounds.wordWidth S K ≤ w) (hDB : D < 2 ^ w) :
    Spec (2 ^ w) (fun σ => Value "recon.lo" l σ ∧ Value "recon.hi" u σ ∧
      σ.vars "recon.bound" = D ∧ σ.vars "recon.limit" = K ∧ (σ.arrs "cf.stack").length = N)
      search (fun _ τ => Output (scan l u D K) τ)
      ((RamConvergentBounds.instructionBound S K + 156) * K + 8) := by
  have hKB : K < 2 ^ w := (by unfold RamConvergentBounds.wordWidth at hw; omega : K ≤ w).trans_lt
    (Nat.lt_two_pow_self (n := w))
  have hlo := Spec.forRangeZero "recon.i" "recon.limit" (Invariant l u D N K) K
    (RamConvergentBounds.instructionBound S K + 152) hKB
    (fun _ h => h.2.2.2.2.2.1) (fun _ h => h.2.2.2.1)
    (searchStep_spec S K N w D l u hu0 hl hu hN hw hDB)
  rintro σ ⟨hσl, hσu, hσD, hσK, hσN⟩
  have hr₁ : Run (2 ^ w) (.assign "recon.found" (.lit 0)) σ (σ.setVar "recon.found" 0) 2 :=
    Run.assign (evalB_lit (by omega))
  have hinit : Invariant l u D N K ((σ.setVar "recon.found" 0).setVar "recon.i" 0) := by
    refine ⟨?_, ?_, ?_, ?_, hσN, by simp, ?_⟩
    · simpa [Value, vars_setVar] using hσl
    · simpa [Value, vars_setVar] using hσu
    · simpa using hσD
    · simpa using hσK
    · simp [scan_zero, Output]
  obtain ⟨τ, hr₂, hτ, hcounter⟩ := hlo (σ.setVar "recon.found" 0) hinit
  refine ⟨τ, (hr₁.seq hr₂).mono (by simp only [Nat.add_assoc, Nat.reduceAdd]; omega), ?_⟩
  simpa only [hcounter] using hτ.2.2.2.2.2.2

end Lax109476Proofs.RamReconstructionSearch

import Lax109476Proofs.RamContinuedFractionFoldStep

namespace Lax109476Proofs.RamContinuedFractionConvergent

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RationalReconstruction
open RamContinuedFractionStack ContinuedFractionBounds ContinuedFractionFold RamContinuedFractionFoldStep

def zeroResult : Com := .seq (.assign "rat.s" (.lit 0))
  (.seq (.assign "rat.n" (.lit 0)) (.assign "rat.d" (.lit 1)))

def foldStack : Com := .seq zeroResult (.seq (.assign "cf.done" (.lit 0))
  (.while (.lt (.var "cf.done") (.var "cf.limit")) foldStep))

theorem zeroResult_spec (B : ℕ) (h1 : 1 < B) :
    Spec B (fun _ => True) zeroResult (fun _ τ => FractionOutput 0 τ) 6 := by
  intro σ _
  run_vcg
  all_goals simp_all [FractionOutput, fractionValue]

theorem foldStack_spec (B M N K : ℕ) (q : ℚ) (hq : 0 ≤ q) (hh : Height q M)
    (hKB : K < B) (hKN : K ≤ N) (hB : 2 * ((2 * M) ^ (K + 1)) ^ 2 + 3 < B) :
    Spec B (fun σ => Stack q K σ ∧ (σ.arrs "cf.stack").length = N ∧ σ.vars "cf.limit" = K)
      foldStack (fun _ τ => FractionOutput (ContinuedFractionFold.fold q K K) τ)
      ((108 * ((2 * M) ^ (K + 1)).size + 208) * K + 12) := by
  have h1 : 1 < B := by omega
  have hlo := Spec.forRangeZero "cf.done" "cf.limit" (RamContinuedFractionFoldStep.Invariant q N K) K
    (108 * ((2 * M) ^ (K + 1)).size + 204) hKB
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2.1)
    (foldStep_spec B M N K q hq hh hKB hKN hB)
  have hloop : Spec B
      (fun σ => Stack q K σ ∧ (σ.arrs "cf.stack").length = N ∧ σ.vars "cf.limit" = K ∧ FractionOutput 0 σ)
      (.seq (.assign "cf.done" (.lit 0)) (.while (.lt (.var "cf.done") (.var "cf.limit")) foldStep))
      (fun _ τ => FractionOutput (ContinuedFractionFold.fold q K K) τ)
      ((108 * ((2 * M) ^ (K + 1)).size + 208) * K + 6) := by
    refine (hlo.pre ?_).post ?_
    · rintro σ ⟨hstack, hlen, hK, hresult⟩
      refine ⟨?_, hlen, by simp, hK, ?_⟩
      · simpa only [Stack, arrs_setVar] using hstack
      · simpa [FractionOutput, vars_setVar, ContinuedFractionFold.fold] using hresult
    · rintro σ τ _ ⟨hτ, hcounter⟩
      simpa only [hcounter] using hτ.2.2.2.2
  rintro σ ⟨hσstack, hσlen, hσK⟩
  obtain ⟨τ, hr₁, hτresult⟩ := zeroResult_spec B h1 σ trivial
  have hτstack : Stack q K τ := by
    intro i hi
    rw [hr₁.frame_arr "cf.stack" (by decide)]
    exact hσstack i hi
  have hτlen : (τ.arrs "cf.stack").length = N := by
    rw [hr₁.frame_arr "cf.stack" (by decide)]; exact hσlen
  have hτK := (hr₁.frame_var "cf.limit" (by decide)).trans hσK
  obtain ⟨υ, hr₂, hυ⟩ := hloop τ ⟨hτstack, hτlen, hτK, hτresult⟩
  exact ⟨υ, (hr₁.seq hr₂).mono (by omega), hυ⟩

def convergent : Com := .seq (.assign "cf.limit" (.add (.var "cf.depth") (.lit 1)))
  (.seq RamContinuedFractionStack.forward foldStack)

theorem convergent_spec (B M N k : ℕ) (q : ℚ) (hq : 0 ≤ q) (hh : Height q M)
    (hKB : k + 1 < B) (hKN : k + 1 ≤ N) (hB : 2 * ((2 * M) ^ (k + 2)) ^ 2 + 3 < B) :
    Spec B (fun σ => (σ.arrs "cf.stack").length = N ∧ LeftValue q σ ∧ σ.vars "cf.depth" = k)
      convergent (fun _ τ => FractionOutput (RationalReconstruction.convergent q k) τ)
      (((36 * M.size + 113) + (108 * ((2 * M) ^ (k + 2)).size + 208)) * (k + 1) + 22) := by
  have hM : 1 ≤ M := le_trans q.den_pos hh.2
  have hR : M ≤ (2 * M) ^ (k + 2) := (by omega : M ≤ 2 * M).trans
    (le_self_pow (by omega : 1 ≤ 2 * M) (by omega : k + 2 ≠ 0))
  have hMB : M < B := by nlinarith
  have h1 : 1 < B := by omega
  rintro σ ⟨hσlen, hσleft, hσk⟩
  have hr₁ : Run B (.assign "cf.limit" (.add (.var "cf.depth") (.lit 1))) σ
      (σ.setVar "cf.limit" (k + 1)) 4 := by
    apply Run.assign
    simpa only [hσk, Bop.apply_add] using (evalB_bin
      (evalB_var (B := B) (σ := σ) (x := "cf.depth") (hσk ▸ (by omega : k < B)))
      (evalB_lit h1) (show Bop.add.apply (σ.vars "cf.depth") 1 < B by simpa [hσk] using hKB))
  obtain ⟨τ, hr₂, hτstack, hτlen, hτleft, hτi⟩ := forward_spec B M N (k + 1) q hq hh h1 hMB hKB hKN
    (σ.setVar "cf.limit" (k + 1)) ⟨hσlen, by simpa [LeftValue, vars_setVar] using hσleft, by simp⟩
  have hτK : τ.vars "cf.limit" = k + 1 :=
    (hr₂.frame_var _ (by decide)).trans (by simp)
  obtain ⟨υ, hr₃, hυ⟩ := foldStack_spec B M N (k + 1) q hq hh hKB hKN hB τ ⟨hτstack, hτlen, hτK⟩
  refine ⟨υ, (hr₁.seq (hr₂.seq hr₃)).mono ?_, ?_⟩
  · simp only [Nat.add_mul, Nat.add_assoc, Nat.reduceAdd]
    omega
  · simpa only [fold_complete] using hυ

end Lax109476Proofs.RamContinuedFractionConvergent

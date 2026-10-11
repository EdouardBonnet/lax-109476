import Lax109476Proofs.RamPointRecoveryStep

namespace Lax109476Proofs.RamPointRecovery

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRecoveryThreshold RamPointRecoveryStep RationalArithmeticBounds PointRecovery

/-- Arithmetic and fixed-workspace requirements for the complete coordinate
loop. They are ordinary inequalities, not assumptions about a solver. -/
structure Bounds (S N w D M m n : ℕ) : Prop where
  midpoint : 4 * M ^ 2 + 3 < 2 ^ w
  steps : BinaryOptimization.steps D < 2 ^ w
  interval : (D + 1) * 2 ^ BinaryOptimization.steps D ≤ M
  height : M ≤ 2 ^ S
  stack : RamRationalReconstruction.depthBound S + 1 ≤ N
  reconstruction : RamRationalReconstruction.wordWidth S ≤ w
  cap : D < 2 ^ w
  dimensions : ((m + (n + n)) + 1) * n + m + (n + n) + 4 < 2 ^ w
  query : RamStoredFeasibility.wordWidth (sizeBound m n (4 * M ^ 2)) ≤ w

def Invariant {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (D N : ℕ) (σ : Env) : Prop :=
  Persistent P (prefixVector x (σ.vars "point.k")) (σ.vars "point.k") σ ∧
    σ.vars "minimum.bound" = D ∧ (σ.arrs "cf.stack").length = N ∧ σ.vars "point.k" ≤ n

def recover : Com := .seq (.assign "point.k" (.lit 0))
  (.while (.lt (.var "point.k") (.var "point.n")) RamPointRecoveryStep.step)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem recover_spec (S N w D M m n : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ)
    (b : Bounds S N w D M m n)
    (hA : ∀ i j, Height (P.A i j) M) (hb : ∀ i, Height (P.b i) M)
    (hxHeight : ∀ j, Height (x j) M) (hc : ∀ j, P.c j = 0)
    (hx : PrimalFeasible (toReal P) (realVector x))
    (hlex : ∀ i, ∀ y, PrimalFeasible (toReal P) y →
      (∀ j, j < i → y j = (x j : ℝ)) → (x i : ℝ) ≤ y i)
    (hxBound : ∀ j, x j ≤ D ∧ (x j).den ≤ D) :
    Spec (2 ^ w) (fun σ => Persistent P (prefixVector x 0) 0 σ ∧
      σ.vars "minimum.bound" = D ∧ (σ.arrs "cf.stack").length = N) recover
      (fun _ τ => Persistent P x n τ ∧ τ.vars "minimum.bound" = D ∧ (τ.arrs "cf.stack").length = N)
      ((coordinateCost S D M m n + 29) * n + 6) := by
  have hnB : n < 2 ^ w := by have := b.dimensions; omega
  have hstep : Spec (2 ^ w) (fun σ => Invariant P x D N σ ∧ σ.vars "point.k" < n)
      RamPointRecoveryStep.step (fun σ τ => Invariant P x D N τ ∧ τ.vars "point.k" = σ.vars "point.k" + 1)
      (coordinateCost S D M m n + 25) := by
    rintro σ ⟨⟨hσP, hσD, hσN, hσk⟩, hi⟩
    obtain ⟨τ, hr, hτP, hτD, hτN, hτcounter⟩ := RamPointRecoveryStep.step_spec S N w D M m n (σ.vars "point.k") P x
      hi b.midpoint b.steps b.interval b.height b.stack b.reconstruction b.cap b.dimensions b.query
      hA hb hxHeight hc hx hlex hxBound σ ⟨hσP, hσD, hσN⟩
    have hτk := hτP.1.2.2.2.2.2
    refine ⟨τ, hr, ⟨?_, hτD, hτN, ?_⟩, hτcounter⟩
    · simpa only [hτk] using hτP
    · rw [hτk]; omega
  have hlo := Spec.forRangeZero "point.k" "point.n" (Invariant P x D N) n
    (coordinateCost S D M m n + 25) hnB
    (fun _ h => h.2.2.2) (fun _ h => h.1.1.2.2.2.2.1) hstep
  refine ((hlo.pre ?_).post ?_).mono (by simp only [Nat.add_assoc, Nat.reduceAdd]; omega)
  · rintro σ ⟨hσP, hσD, hσN⟩
    refine ⟨?_, by simpa using hσD, by simpa using hσN, by simp⟩
    constructor
    · change State P (prefixVector x 0) 0 (σ.setVar "point.k" 0)
      rcases hσP.1 with ⟨hA, hb, hx, hm, hn, hk⟩
      exact ⟨hA, hb, hx, by simpa using hm, by simpa using hn, by simp⟩
    · exact hσP.2
  · rintro σ τ _ ⟨hτ, hτcounter⟩
    dsimp only [Invariant] at hτ
    rw [hτcounter] at hτ
    have he : prefixVector x n = x := by funext j; simp [prefixVector, j.isLt]
    exact ⟨by simpa only [he] using hτ.1, hτ.2.1, hτ.2.2.1⟩

end Lax109476Proofs.RamPointRecovery

import Lax109476Proofs.RamPointRecovery

namespace Lax109476Proofs.RamPointRecoveryBounds

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RationalArithmeticBounds RamPointRecovery RamRecoveryThreshold

def querySize (m n S : ℕ) : ℕ :=
  ((m + (n + n)) + 1) + n + 2 +
    ((((m + (n + n)) + 1) * n) + ((m + (n + n)) + 1) + n) * (4 + 2 * (2 * S + 3))

def queryCost (m n S : ℕ) : ℕ :=
  142 * (((m + (n + n)) + 1) * n) + 138 * ((m + (n + n)) + 1) + 33 * n + 106 +
    RamStoredFeasibility.instructionBound (querySize m n S)

def wordWidth (m n S : ℕ) : ℕ := RamDecoder.wordWidth (S + 1) +
  RamRationalReconstruction.wordWidth S + RamStoredFeasibility.wordWidth (querySize m n S) +
    (((m + (n + n)) + 1) * n + m + (n + n) + 4) + S + 4

def instructionBound (m n S C : ℕ) : ℕ :=
  ((144 * (S + 1) + 342 + queryCost m n S) * (3 * C + 2) + 12 * C +
    RamRationalReconstruction.instructionBound S + 77) * n + 6

theorem threshold_size (m n S : ℕ) : sizeBound m n (4 * (2 ^ S) ^ 2) = querySize m n S := by
  have he : 4 * (2 ^ S) ^ 2 = 2 ^ (2 * S + 2) := by
    rw [← pow_mul, pow_add]; norm_num; ring
  simp only [sizeBound, querySize, he, Nat.size_pow]

theorem resource_bounds (m n S C N D w : ℕ) (hD : D.size ≤ C) (hS : 4 * C + 2 ≤ S)
    (hN : RamRationalReconstruction.depthBound S + 1 ≤ N) (hw : wordWidth m n S ≤ w) :
    Bounds S N w D (2 ^ S) m n := by
  have hdecode : RamDecoder.wordWidth (S + 1) ≤ w := by unfold wordWidth at hw; omega
  have hclear := RamSolverFrontEnd.clearing_word_guard (S + 1) w hdecode
  have hpow : 2 ^ (S + 1) = 2 ^ S * 2 := by rw [pow_succ]
  have hmid : 4 * (2 ^ S) ^ 2 + 3 < 2 ^ w := by rw [hpow] at hclear; nlinarith
  have hsteps : BinaryOptimization.steps D ≤ 3 * C + 2 := by unfold BinaryOptimization.steps; omega
  have hstepsw : BinaryOptimization.steps D ≤ w := by unfold wordWidth RamDecoder.wordWidth at hw; omega
  have hdim : ((m + (n + n)) + 1) * n + m + (n + n) + 4 ≤ w := by unfold wordWidth at hw; omega
  have hDw : D.size ≤ w := by unfold wordWidth RamDecoder.wordWidth at hw; omega
  have hsmall := Nat.lt_size_self D
  have hinterval : (D + 1) * 2 ^ BinaryOptimization.steps D ≤ 2 ^ S := by
    calc
      (D + 1) * 2 ^ BinaryOptimization.steps D ≤ 2 ^ C * 2 ^ (3 * C + 2) :=
        Nat.mul_le_mul ((by omega : D + 1 ≤ 2 ^ D.size).trans
          (Nat.pow_le_pow_right (by decide) hD)) (Nat.pow_le_pow_right (by decide) hsteps)
      _ = 2 ^ (4 * C + 2) := by rw [← pow_add]; congr 1; omega
      _ ≤ 2 ^ S := Nat.pow_le_pow_right (by decide) hS
  refine ⟨hmid, hstepsw.trans_lt (Nat.lt_two_pow_self (n := w)), hinterval, le_rfl, hN, ?_,
    (Nat.lt_size_self D).trans_le (Nat.pow_le_pow_right (by decide) hDw),
    hdim.trans_lt (Nat.lt_two_pow_self (n := w)), ?_⟩
  · unfold wordWidth at hw; omega
  · rw [threshold_size]; unfold wordWidth at hw; omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem recover_bounded_spec (m n S C N D w : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ)
    (hD : D.size ≤ C) (hS : 4 * C + 2 ≤ S)
    (hN : RamRationalReconstruction.depthBound S + 1 ≤ N) (hw : wordWidth m n S ≤ w)
    (hA : ∀ i j, Height (P.A i j) (2 ^ S)) (hb : ∀ i, Height (P.b i) (2 ^ S))
    (hxHeight : ∀ j, Height (x j) (2 ^ S)) (hc : ∀ j, P.c j = 0)
    (hx : PrimalFeasible (toReal P) (realVector x))
    (hlex : ∀ i, ∀ y, PrimalFeasible (toReal P) y →
      (∀ j, j < i → y j = (x j : ℝ)) → (x i : ℝ) ≤ y i)
    (hxBound : ∀ j, x j ≤ D ∧ (x j).den ≤ D) :
    Spec (2 ^ w) (fun σ => Persistent P (PointRecovery.prefixVector x 0) 0 σ ∧
      σ.vars "minimum.bound" = D ∧ (σ.arrs "cf.stack").length = N) recover
      (fun _ τ => Persistent P x n τ ∧ τ.vars "minimum.bound" = D ∧ (τ.arrs "cf.stack").length = N)
      (instructionBound m n S C) := by
  have hr := recover_spec S N w D (2 ^ S) m n P x (resource_bounds m n S C N D w hD hS hN hw)
    hA hb hxHeight hc hx hlex hxBound
  refine hr.mono ?_
  unfold RamPointRecoveryStep.coordinateCost instructionBound queryCost
  dsimp only [RamRecoveryThreshold.instructionBound]
  rw [Nat.size_pow, threshold_size]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  have hsteps : BinaryOptimization.steps D ≤ 3 * C + 2 := by unfold BinaryOptimization.steps; omega
  gcongr

end Lax109476Proofs.RamPointRecoveryBounds

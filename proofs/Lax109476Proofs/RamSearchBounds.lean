import Lax109476Proofs.RamSearchLoop

namespace Lax109476Proofs.RamSearchBounds

open RamTrajectoryBounds RamEllipsoidBitBounds RamEllipsoidStep RamEllipsoidWordBounds
open RamDotProduct RamEllipsoidForm

def wordWidth (m n N l : ℕ) : ℕ :=
  RamEllipsoidBitBounds.wordWidth n (stateBits n N l) N + m + n + m * n + N + 2

theorem wordWidth_parameters (m n N l w : ℕ) (hn : 2 ≤ n) (hw : wordWidth m n N l ≤ w) :
    N < 2 ^ w ∧ RamEllipsoidBitBounds.wordWidth n (stateBits n N l) N ≤ w ∧
      m + n + m * n + 1 < 2 ^ w ∧
      2 * (cap n (2 ^ stateBits n N l)) ^ 2 + 3 < 2 ^ w := by
  have hcut : RamEllipsoidBitBounds.wordWidth n (stateBits n N l) N ≤ w := by unfold wordWidth at hw; omega
  have hNB : N < 2 ^ w := by
    have hN : N < 2 ^ N := Nat.lt_two_pow_self
    exact hN.trans_le (Nat.pow_le_pow_right (by decide) (by unfold wordWidth at hw; omega))
  have hdims : m + n + m * n + 1 < 2 ^ w := by
    have hd : m + n + m * n + 1 < 2 ^ (m + n + m * n + 1) := Nat.lt_two_pow_self
    exact hd.trans_le (Nat.pow_le_pow_right (by decide) (by unfold wordWidth at hw; omega))
  have hp := magnitude_parameters n (stateBits n N l) N
  have hg := wordWidth_sufficient n (stateBits n N l) N w hcut
  have hb := unified_word_bounds _ _ n hn hp.1 hg
  have hH : 1 ≤ 2 ^ stateBits n N l := Nat.one_le_pow _ _ (by decide)
  have hc := (formHeight_ge n (2 ^ stateBits n N l) hH).trans hp.2.1
  have hprim := hb.2.2.2.2.2.2.1
  have hsq := Nat.pow_le_pow_left hc 2
  refine ⟨hNB, hcut, hdims, ?_⟩
  omega

def rowBound (n N l : ℕ) : ℕ :=
  (144 * ((n + 1) * (2 * (stateBits n N l + 1) + 3) + 1) + 220) * n + 95

def stepBound (m n N l : ℕ) : ℕ := rowBound n N l * m + 126 * n + instructionBound n N l + 103

def instructionBound (m n N l : ℕ) : ℕ :=
  33 * n + 76 * (n * n) + (stepBound m n N l + 4) * N + 64

theorem stepBound_sufficient (m n N l : ℕ) : RamSearchStep.cost m n N l ≤ stepBound m n N l := by
  have hs := RamSeparation.separateRows_cost_polynomial m n (2 ^ stateBits n N l)
  rw [Nat.size_pow] at hs
  simp only [Nat.add_assoc, Nat.reduceAdd] at hs
  have hc := RamTrajectoryBounds.instructionBound_polynomial n N l
  have htotal := Nat.add_le_add hs hc
  unfold RamSearchStep.cost stepBound rowBound
  omega

theorem instructionBound_sufficient (m n N l : ℕ) :
    33 * n + 76 * (n * n) + (RamSearchStep.cost m n N l + 4) * N + 64 ≤ instructionBound m n N l := by
  have hstep := Nat.mul_le_mul_right N (Nat.add_le_add_right (stepBound_sufficient m n N l) 4)
  unfold instructionBound
  omega

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamMatrixRows RamRationalArrays RamEllipsoidStep

def Input {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ) (N : ℕ) (σ : Env) : Prop :=
  MatrixRows "search.rows" (fun i j => (A i j : ℚ)) σ ∧ Represents "search.rhs" (List.ofFn b) σ ∧
    Extents "ell.center" n σ ∧ Extents "ell.shape" (n * n) σ ∧ Workspace n σ ∧
    Extents "ell.normal" n σ ∧ σ.vars "vec.n" = n ∧ σ.vars "row.m" = m ∧ σ.vars "search.budget" = N

/-- Polynomial word and instruction bounds cover the initialized bounded
search, uniformly in the input dimensions and in every larger word width. -/
theorem search_bounded_spec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ)
    (hn : 2 ≤ n) (N l w : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ l)
    (hb : ∀ i, RationalArithmeticBounds.Height (b i) (2 ^ l))
    (hw : wordWidth m n N l ≤ w) :
    Spec (2 ^ w) (Input A b N) RamSearchLoop.search
      (fun _ τ => RamSearchLoop.Invariant A b N τ ∧
        EllipsoidSearch.findFirst
          (fun j => decide (RationalSeparation.firstViolation A b (EllipsoidSearch.trajectory A b j).2 = none)) 0 N =
          if τ.vars "search.found" = 1 then some (τ.vars "iter.k") else none)
      (instructionBound m n N l) := by
  have hp := wordWidth_parameters m n N l w hn hw
  exact (RamSearchLoop.search_spec A b hn N l w hp.1 hA hb hp.2.1 hp.2.2.1 hp.2.2.2).mono
    (instructionBound_sufficient m n N l)

end Lax109476Proofs.RamSearchBounds

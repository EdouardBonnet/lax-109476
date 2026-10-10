import Lax109476Proofs.RamEllipsoidBitBounds
import Lax109476Proofs.EllipsoidStateSize
import Lax109476Proofs.EllipsoidSearch

open scoped Matrix BigOperators

namespace Lax109476Proofs.RamTrajectoryBounds

open Lax759944.BinaryWordEncoding Lax109476.RationalEncoding Lax109476.RationalCertificates
open RationalArithmeticBounds EncodingSize EllipsoidSearch EllipsoidSequence EllipsoidStateSize
open RamEllipsoidBitBounds RamEllipsoidStep RamAdvanceState RamRationalArrays RamMatrixStorage
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def stateBits (n K l : ℕ) : ℕ := 60 + 6 * K + 14 * n + l

def instructionBound (n K l : ℕ) : ℕ :=
  let h := stateBits n K l
  let e := magnitudeExponent n h K
  (144 * ((n + 1) * (2 * (h + 1) + 3) + 1) + 220) * n ^ 2 +
    (144 * ((n + 1) * (2 * ((n + 1) * (2 * (h + 1) + 3) + 1) + 3) + 1) + 292) * n +
    (2880 * (e + 1) + 7559) * n + (14976 * (e + 1) + 36767) * (n * n) +
    582 * (e + 1) + 1060 + 71 * n + 71 * (n * n)

set_option maxRecDepth 6000 in
theorem instructionBound_polynomial (n K l : ℕ) :
    stepCost n (2 ^ stateBits n K l) (2 ^ magnitudeExponent n (stateBits n K l) K) +
      71 * n + 71 * (n * n) + 60 ≤ instructionBound n K l := by
  have h := stepCost_polynomial n (2 ^ stateBits n K l)
    (2 ^ magnitudeExponent n (stateBits n K l) K)
  rw [Nat.size_pow, Nat.size_pow] at h
  have htotal := Nat.add_le_add_right h (71 * n + 71 * (n * n) + 60)
  dsimp only [instructionBound]
  omega

theorem height_of_encoding (q : ℚ) (h : ℕ) (hq : bitSize (encodeRational q) ≤ h) :
    Height q (2 ^ h) := by
  have hs := (rational_size_bounds q).2
  have hn : q.num.natAbs < 2 ^ q.num.natAbs.size := Nat.lt_size_self _
  have hd : q.den < 2 ^ q.den.size := Nat.lt_size_self _
  exact ⟨hn.le.trans (Nat.pow_le_pow_right (by decide) (by omega)),
    hd.le.trans (Nat.pow_le_pow_right (by decide) (by omega))⟩

theorem selectedNormal_height {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ)
    (c : Fin n → ℚ) (H : ℕ) (hH : 1 ≤ H) (hA : ∀ i j, (A i j).natAbs ≤ H) :
    ∀ j, Height (selectedNormal A b c j) H := by
  intro j
  cases hf : RationalSeparation.firstViolation A b c with
  | none =>
    simp only [selectedNormal, hf]
    unfold fallbackNormal
    split_ifs <;> simp_all [Height]
  | some i =>
    simp only [selectedNormal, hf]
    by_cases hz : A i = 0
    · simp only [if_pos hz]
      unfold fallbackNormal
      split_ifs <;> simp_all [Height]
    · simp only [if_neg hz]
      simpa [RationalSeparation.rationalRow, Height] using And.intro (hA i j) hH

theorem trajectory_heights {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ)
    (hn : 2 ≤ n) (K l k : ℕ) (hk : k ≤ K) :
    (∀ i j, Height ((trajectory A b k).1 i j) (2 ^ stateBits n K l)) ∧
      (∀ i, Height ((trajectory A b k).2 i) (2 ^ stateBits n K l)) := by
  have heq := trajectory_eq_sequences A b k
  have hnorm := fun t => selectedNormal_norm A b (trajectory A b t).2 (by omega : 0 < n)
  constructor
  · intro i j
    apply height_of_encoding
    rw [heq.1]
    exact (shapes_encoding_size n hn (normalSchedule A b) hnorm k i j).trans (by unfold stateBits; omega)
  · intro i
    apply height_of_encoding
    rw [heq.2]
    exact (centers_encoding_size n hn (normalSchedule A b) hnorm k i).trans (by unfold stateBits; omega)

theorem trajectory_posDef {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ)
    (hn : 2 ≤ n) (k : ℕ) : (EllipsoidRounding.realShape (trajectory A b k).1).PosDef := by
  rw [(trajectory_eq_sequences A b k).1]
  exact (shapes_invariant n hn (normalSchedule A b)
    (fun t => selectedNormal_norm A b (trajectory A b t).2 (by omega)) k).1

theorem selectedNormal_ne_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ)
    (c : Fin n → ℚ) (hn : 0 < n) : selectedNormal A b c ≠ 0 := by
  intro heq
  have h := selectedNormal_norm A b c hn
  rw [heq] at h
  have hz : realVector (0 : Fin n → ℚ) = 0 := by funext j; simp [realVector]
  rw [hz, dotProduct_zero] at h
  norm_num at h

/-- One fixed RAM command follows the actual trajectory. The word and cost
bounds use the global state-size theorem rather than a recursively amplified height cap. -/
theorem trajectory_advance_spec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ)
    (hn : 2 ≤ n) (K l k w : ℕ) (hk : k ≤ K) (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ l)
    (hw : wordWidth n (stateBits n K l) K ≤ w) :
    Spec (2 ^ w) (fun σ => Represents "ell.shape" (flatten (trajectory A b k).1) σ ∧
        Represents "ell.normal" (List.ofFn (selectedNormal A b (trajectory A b k).2)) σ ∧
        Represents "ell.center" (List.ofFn (trajectory A b k).2) σ ∧ Workspace n σ ∧
        σ.vars "vec.n" = n ∧ σ.vars "iter.k" = k)
      advanceState
      (fun _ τ => Represents "ell.center" (List.ofFn (trajectory A b (k + 1)).2) τ ∧
        Represents "ell.shape" (flatten (trajectory A b (k + 1)).1) τ ∧
        Workspace n τ ∧ τ.vars "vec.n" = n ∧ τ.vars "iter.k" = k + 1)
      (stepCost n (2 ^ stateBits n K l) (2 ^ magnitudeExponent n (stateBits n K l) K) +
        71 * n + 71 * (n * n) + 60) := by
  let h := stateBits n K l
  have hH : 1 ≤ 2 ^ h := Nat.one_le_pow _ _ (by decide)
  have hstate := trajectory_heights A b hn K l k hk
  have hnormal : ∀ j, Height (selectedNormal A b (trajectory A b k).2 j) (2 ^ h) := by
    intro j
    apply height_mono _ (selectedNormal_height A b _ (2 ^ l) (Nat.one_le_pow _ _ (by decide)) hA j)
    apply Nat.pow_le_pow_right (by decide)
    unfold h stateBits
    omega
  have hq := form_pos_of_posDef (trajectory A b k).1 (selectedNormal A b (trajectory A b k).2)
    (trajectory_posDef A b hn k) (selectedNormal_ne_zero A b _ (by omega))
  have hparams := magnitude_parameters n h K
  have hD : 2 ^ (2 * k + 3 * n + 9) ≤ 2 ^ magnitudeExponent n h K :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans hparams.2.2.1
  have hs := advanceState_spec (2 ^ w) n (2 ^ h) (2 ^ magnitudeExponent n h K) k
    (trajectory A b k).1 (selectedNormal A b (trajectory A b k).2) (trajectory A b k).2
    hn hH hstate.1 hnormal hstate.2 hq hparams.1 hparams.2.1 hD hparams.2.2.2
    (wordWidth_sufficient n h K w hw)
  apply hs.post
  rintro σ τ _ ⟨hc, hshape, hw', hn', hk'⟩
  refine ⟨?_, ?_, hw', hn', hk'⟩
  · simpa only [trajectory, nextState, cacheState_eq, EllipsoidPrecision.gridDenominator,
      show (2 * k + 2) + (2 * n + 4) + n + 3 = 2 * k + 3 * n + 9 by omega] using hc
  · simpa only [trajectory, nextState, cacheState_eq, EllipsoidPrecision.gridDenominator,
      show (2 * k + 2) + (2 * n + 4) + n + 3 = 2 * k + 3 * n + 9 by omega] using hshape

end Lax109476Proofs.RamTrajectoryBounds

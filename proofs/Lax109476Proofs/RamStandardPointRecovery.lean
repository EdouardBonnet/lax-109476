import Lax109476Proofs.RamPointInitialization

open scoped Matrix

namespace Lax109476Proofs.RamStandardPointRecovery

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RationalArithmeticBounds LexicographicMinima LexicographicSupport LexicographicBounds
open RamRecoveryThreshold

def program {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) : Program ℚ (m + m) n :=
  equationProgram (C.map (fun z => (z : ℚ))) (fun i => (b i : ℚ))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem recover_spec (m n H S K N w : ℕ) (C : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hC : ∀ i j, (C i j).natAbs ≤ H) (hb : ∀ i, (b i).natAbs ≤ H)
    (hH : H ≤ 2 ^ S) (hK : (coordinateCap m n H).size ≤ K) (hS : 4 * K + 2 ≤ S)
    (hN : RamRationalReconstruction.depthBound S + 1 ≤ N)
    (hw : RamPointRecoveryBounds.wordWidth (m + m) n S ≤ w)
    (hf : ∃ x, Feasible (C.map (fun z => (z : ℚ))) (fun i => (b i : ℚ)) x) :
    Spec (2 ^ w) (fun σ => RamPointInitialization.Base (program C b) σ ∧
      Workspace (m + m) n σ ∧ RamEllipsoidStep.Extents "point.x" n σ ∧
      σ.vars "minimum.bound" = coordinateCap m n H ∧ (σ.arrs "cf.stack").length = N)
      RamPointInitialization.recover
      (fun _ τ => ∃ x : Fin n → ℚ, Persistent (program C b) x n τ ∧
        Feasible (C.map (fun z => (z : ℚ))) (fun i => (b i : ℚ)) x ∧
        ∀ j, Height (x j) (coordinateCap m n H))
      (33 * n + 22 + RamPointRecoveryBounds.instructionBound (m + m) n S K) := by
  have hpow : 1 ≤ 2 ^ S := Nat.one_le_pow _ _ (by decide)
  have hcap : coordinateCap m n H ≤ 2 ^ S := (Nat.lt_size_self _).le.trans
    (Nat.pow_le_pow_right (by decide) (by omega : (coordinateCap m n H).size ≤ S))
  obtain ⟨x, hx, hxBound, hlex⟩ := exists_bounded_lex_point C b H hC hb hf
  have hA : ∀ i j, Height ((program C b).A i j) (2 ^ S) := by
    intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · change Height (Fin.addCases (motive := fun _ : Fin (m + m) => Fin n → ℚ)
        (fun i j => (C i j : ℚ)) (fun i j => -(C i j : ℚ)) (Fin.castAdd m i) j) (2 ^ S)
      rw [Fin.addCases_left (motive := fun _ : Fin (m + m) => Fin n → ℚ)]
      exact ⟨by simpa using (hC i j).trans hH, by simpa using hpow⟩
    · change Height (Fin.addCases (motive := fun _ : Fin (m + m) => Fin n → ℚ)
        (fun i j => (C i j : ℚ)) (fun i j => -(C i j : ℚ)) (Fin.natAdd m i) j) (2 ^ S)
      rw [Fin.addCases_right (motive := fun _ : Fin (m + m) => Fin n → ℚ)]
      apply height_neg
      exact ⟨by simpa using (hC i j).trans hH, by simpa using hpow⟩
  have hbound : ∀ i, Height ((program C b).b i) (2 ^ S) := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [program, equationProgram, Fin.addCases_left]
      exact ⟨by simpa using (hb i).trans hH, by simpa using hpow⟩
    · simp only [program, equationProgram, Fin.addCases_right]
      apply height_neg
      exact ⟨by simpa using (hb i).trans hH, by simpa using hpow⟩
  have hxHeight : ∀ j, Height (x j) (2 ^ S) := fun j => height_mono _ (hxBound j) hcap
  have hxD : ∀ j, x j ≤ coordinateCap m n H ∧ (x j).den ≤ coordinateCap m n H := by
    intro j
    refine ⟨?_, (hxBound j).2⟩
    have he := Relaxation.rational_magnitude_bound (x j) (coordinateCap m n H) (hxBound j).1
    exact (Rat.cast_le (K := ℝ)).mp ((le_abs_self _).trans he)
  have hr := RamPointInitialization.recover_spec (m + m) n S K N (coordinateCap m n H) w (program C b) x
    hK hS hN hw hA hbound hxHeight (by intro j; rfl) ((cast_standard_feasible _ _ x).mp hx) hlex hxD
  refine hr.post ?_
  rintro σ τ _ ⟨hτ, _, _⟩
  exact ⟨x, hτ, hx, hxBound⟩

end Lax109476Proofs.RamStandardPointRecovery

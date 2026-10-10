import Lax109476Proofs.RamIntegerFeasibility
import Lax109476Proofs.RamQueryPadding
import Lax109476Proofs.RationalFeasibilityDecision

namespace Lax109476Proofs.RamPaddedFeasibility

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamMatrixStorage IntegerEncoding RationalArithmeticBounds

 theorem rationalProgram_pad {m n : ℕ} (P : Program ℤ m n) :
    rationalProgram (FeasibilityPadding.pad P) = FeasibilityPadding.pad (rationalProgram P) := by
  unfold FeasibilityPadding.pad rationalProgram
  congr 1
  · funext i j
    refine Fin.addCases ?_ ?_ i
    · intro i
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp
    · intro i
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [apply_ite]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro i <;> simp
  · funext j
    refine Fin.addCases ?_ ?_ j <;> intro j <;> simp

def decideFeasible : Com := .seq RamQueryPadding.padQuery RamIntegerFeasibility.decideFeasible

def wordWidth (S : ℕ) : ℕ := RamIntegerFeasibility.wordWidth (S + 4) +
  RamDecoder.wordWidth (2 * S) + (S + 4) ^ 2 + S + 5

def instructionBound (S : ℕ) : ℕ := 111 * (S + 4) ^ 2 + 77 * (S + 4) + 78 +
  RamIntegerFeasibility.uniformInstructionBound (S + 4)

def Input {m n : ℕ} (P : Program ℤ m n) (S : ℕ) (σ : Env) : Prop :=
  RamQueryPadding.Input (rationalProgram P) S σ ∧
    Extents "search.rows" (((m + 2) + (n + 2)) * (n + 2)) σ ∧
    Extents "search.rhs" ((m + 2) + (n + 2)) σ ∧
    Extents "ell.center" (n + 2) σ ∧ Extents "ell.shape" ((n + 2) * (n + 2)) σ ∧
    Workspace (n + 2) σ ∧ Extents "ell.normal" (n + 2) σ

set_option maxHeartbeats 800000 in
theorem decideFeasible_spec (m n S w : ℕ) (P : Program ℤ m n) (hdim : m + n ≤ S)
    (hA : ∀ i j, (P.A i j).natAbs ≤ 2 ^ (2 * S))
    (hb : ∀ i, (P.b i).natAbs ≤ 2 ^ (2 * S)) (hw : wordWidth S ≤ w) :
    Spec (2 ^ w) (Input P S) decideFeasible
      (fun _ τ => decide (τ.vars "search.found" = 1) = FeasibilityPadding.feasible P (2 ^ (2 * (S + 4))))
      (instructionBound S) := by
  let H := 2 ^ (2 * S)
  have hH : 1 ≤ H := Nat.one_le_pow _ _ (by decide)
  have hwInt : RamIntegerFeasibility.wordWidth (S + 4) ≤ w := by unfold wordWidth at hw; omega
  have hwDec : RamDecoder.wordWidth (2 * S) ≤ w := by unfold wordWidth at hw; omega
  have hHB : H < 2 ^ w := Nat.pow_lt_pow_right (by decide)
    (by unfold RamDecoder.wordWidth at hwDec; omega)
  have hdims : (m + 2) * (n + 2) + m + n + 4 < 2 ^ w := by
    have hmn : (m + 2) * (n + 2) ≤ (S + 4) ^ 2 := by
      have h := Nat.mul_le_mul (show m + 2 ≤ S + 4 by omega) (show n + 2 ≤ S + 4 by omega)
      simpa only [pow_two] using h
    have hh := (Nat.lt_two_pow_self (n := (S + 4) ^ 2 + S + 5)).trans_le
      (Nat.pow_le_pow_right (by decide) (show (S + 4) ^ 2 + S + 5 ≤ w by unfold wordWidth at hw; omega))
    omega
  have hSB : S + 4 < 2 ^ w :=
    (Nat.lt_two_pow_self (n := S + 4)).trans_le
      (Nat.pow_le_pow_right (by decide) (by unfold wordWidth at hw; omega))
  have hAH : ∀ i j, Height ((rationalProgram P).A i j) H := by
    intro i j
    simpa [Height, rationalProgram, H] using And.intro (hA i j) hH
  have hbH : ∀ i, Height ((rationalProgram P).b i) H := by
    intro i
    simpa [Height, rationalProgram, H] using And.intro (hb i) hH
  have hlarge : H ≤ 2 ^ (2 * (S + 4)) := Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨hpadA, hpadb⟩ := FeasibilityPadding.padded_bounds P H hH hA hb
  rintro σ ⟨hσpad, hσrows, hσrhs, hσcenter, hσshape, hσworkspace, hσnormal⟩
  obtain ⟨τ, hr₁, hτA, hτb, hτsourceA, hτsourceb, hτm, hτn, hτbits⟩ :=
    RamQueryPadding.padQuery_spec (2 ^ w) H m n S (rationalProgram P)
      hH hHB hdims hSB hAH hbH σ hσpad
  have hτinput : RamFeasibilitySetup.Input (FeasibilityPadding.pad P) (S + 4) τ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hτm, hτn, hτbits⟩
    · simpa only [rationalProgram_pad] using hτA
    · simpa only [rationalProgram_pad] using hτb
    · exact RamAdvanceState.extents_of_run hr₁ _ _ hσrows
    · exact RamAdvanceState.extents_of_run hr₁ _ _ hσrhs
    · exact RamAdvanceState.extents_of_run hr₁ _ _ hσcenter
    · exact RamAdvanceState.extents_of_run hr₁ _ _ hσshape
    · exact RamAdvanceState.workspace_of_run hr₁ _ hσworkspace
    · exact RamAdvanceState.extents_of_run hr₁ _ _ hσnormal
  obtain ⟨υ, hr₂, hυ⟩ := RamIntegerFeasibility.decideFeasible_uniform_spec (m + 2) (n + 2) (S + 4) w
    (FeasibilityPadding.pad P) (by omega) (by omega)
    (fun i j => (hpadA i j).trans hlarge) (fun i => (hpadb i).trans hlarge) hwInt τ hτinput
  have hprod : (m + 2) * (n + 2) ≤ (S + 4) ^ 2 := by
    have h := Nat.mul_le_mul (show m + 2 ≤ S + 4 by omega) (show n + 2 ≤ S + 4 by omega)
    simpa only [pow_two] using h
  have hm := Nat.mul_le_mul_left 111 hprod
  have hbcount := Nat.mul_le_mul_left 77 (show m + 2 ≤ S + 4 by omega)
  exact ⟨υ, (hr₁.seq hr₂).mono (by unfold instructionBound; omega), hυ⟩

end Lax109476Proofs.RamPaddedFeasibility

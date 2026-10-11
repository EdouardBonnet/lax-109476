import Lax109476Proofs.RamEquationMatrix
import Lax109476Proofs.RamEquationBound

namespace Lax109476Proofs.RamEquationBuilder

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEquationData RamEllipsoidStep RationalArithmeticBounds

def metadata : Com := .seq (.assign "point.m" (.add (.var "system.m") (.var "system.m")))
  (.assign "point.n" (.add (.var "system.n") (.var "system.m")))

/-- Add slack coordinates and the negated inequalities that express each
equation. The stored integer system remains immutable during point recovery. -/
def buildSystem : Com := .seq RamEquationMatrix.matrix (.seq RamEquationBound.buildBound metadata)

theorem metadata_spec (B m n : ℕ) (hB : m + m + n + 4 < B) :
    Spec B (fun σ => σ.vars "system.m" = m ∧ σ.vars "system.n" = n) metadata
      (fun _ τ => τ.vars "point.m" = m + m ∧ τ.vars "point.n" = n + m) 8 := by
  rintro σ ⟨hm, hn⟩
  run_vcg
  all_goals simp_all
  all_goals omega

set_option maxHeartbeats 1000000 in
theorem buildSystem_spec (B M m n : ℕ) (P : Program ℤ m n)
    (hM : 1 ≤ M) (hMB : M < B) (hB : (m + m) * (n + m) + m + m + n + 4 < B)
    (hA : ∀ i j, (P.A i j).natAbs ≤ M) (hb : ∀ i, (P.b i).natAbs ≤ M) :
    Spec B (fun σ => Data P σ ∧ Extents "point.A" ((m + m) * (n + m)) σ ∧ Extents "point.b" (m + m) σ)
      buildSystem (fun _ τ => Data P τ ∧ RamPointInitialization.Base
        (RamStandardPointRecovery.program (IntegerPointRecovery.slackMatrix P) P.b) τ)
      (118 * ((m + m) * (n + m)) + 91 * (m + m) + 72) := by
  let C := RamStandardPointRecovery.program (IntegerPointRecovery.slackMatrix P) P.b
  rintro σ ⟨hσData, hσA, hσb⟩
  obtain ⟨τ, hr₁, hτData, hτA⟩ := RamEquationMatrix.matrix_spec B M m n P hM hMB (by omega) hA σ ⟨hσData, hσA⟩
  obtain ⟨υ, hr₂, hυData, hυb⟩ := RamEquationBound.buildBound_spec B M m n P hM hMB (by omega) hb τ
    ⟨hτData, RamAdvanceState.extents_of_run hr₁ _ _ hσb⟩
  have hυA := RamReadBody.represents_frame "point.A" (RamMatrixStorage.flatten C.A) hτA hr₂
    (by intro s hs; simp at hs; rcases hs with rfl | rfl | rfl <;> decide)
  obtain ⟨ρ, hr₃, hρm, hρn⟩ := metadata_spec B m n (by omega) υ ⟨hυData.2.2.1, hυData.2.2.2⟩
  have hρData := data_frame hr₃ P hυData
    (by intro a ha; simp [RamEquationData.fields] at ha; rcases ha with rfl | rfl <;> decide)
    (by intro a ha s hs; simp [metadata, Com.warrs])
  have hρA := RamReadBody.represents_frame "point.A" (RamMatrixStorage.flatten C.A) hυA hr₃
    (by intro s hs; simp [metadata, Com.warrs])
  have hρb := RamReadBody.represents_frame "point.b" (List.ofFn C.b) hυb hr₃
    (by intro s hs; simp [metadata, Com.warrs])
  exact ⟨ρ, (hr₁.seq (hr₂.seq hr₃)).mono (by omega), hρData, hρA, hρb, hρm, hρn⟩

end Lax109476Proofs.RamEquationBuilder

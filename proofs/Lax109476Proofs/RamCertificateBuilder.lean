import Lax109476Proofs.RamCertificateMatrix
import Lax109476Proofs.RamCertificateBound
import Lax109476Proofs.RamEquationData

namespace Lax109476Proofs.RamCertificateBuilder

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds IntegerEncoding RamEllipsoidStep
open RamCertificateContext

def buildSystem (matrixSelector boundSelector : Com) : Com :=
  .seq (RamCertificateMatrix.matrix matrixSelector) (RamCertificateBound.buildBound boundSelector)

set_option maxHeartbeats 1000000 in
theorem buildSystem_spec (B M m n r s matrixCost boundCost : ℕ) (P : Program ℤ m n) (F : Program ℤ r s)
    (matrixSelector boundSelector : Com) (hM : 1 ≤ M) (hMB : M < B)
    (hB : r * s + r + s + 4 < B)
    (hA : ∀ i j, (F.A i j).natAbs ≤ M) (hb : ∀ i, (F.b i).natAbs ≤ M)
    (hMatrix : ∀ i j, Spec B
      (fun σ => RamCertificateSource.Data P σ ∧ σ.vars "query.row" = i.val ∧ σ.vars "query.col" = j.val)
      matrixSelector (fun _ τ => RamCertificateSource.Data P τ ∧ FractionOutput (F.A i j : ℚ) τ) matrixCost)
    (hBound : ∀ i, Spec B (fun σ => RamCertificateSource.Data P σ ∧ σ.vars "query.row" = i.val)
      boundSelector (fun _ τ => RamCertificateSource.Data P τ ∧ FractionOutput (F.b i : ℚ) τ) boundCost)
    (hfm : ∀ a ∈ fields, a ∉ matrixSelector.wvars)
    (hfb : ∀ a ∈ fields, a ∉ boundSelector.wvars)
    (him : "build.i" ∉ matrixSelector.wvars) (hnm : "build.count" ∉ matrixSelector.wvars)
    (hib : "build.i" ∉ boundSelector.wvars) (hnb : "build.count" ∉ boundSelector.wvars)
    (ham : matrixSelector.warrs = []) (hab : boundSelector.warrs = []) :
    Spec B (fun σ => Context P r s σ ∧ Extents "system.A" (r * s) σ ∧ Extents "system.b" r σ)
      (buildSystem matrixSelector boundSelector)
      (fun _ τ => RamCertificateSource.Data P τ ∧ RamEquationData.Data F τ)
      ((matrixCost + 70) * (r * s) + (boundCost + 58) * r + 62) := by
  have h1 : 1 < B := by omega
  have hm := RamCertificateMatrix.matrix_spec B M m n r s matrixCost P F matrixSelector hM hMB hB hA hMatrix hfm
    (by intro a ha t ht; rw [ham]; simp) him hnm (by intro t ht; rw [ham]; simp)
  have hbound := RamCertificateBound.buildBound_spec B M m n r s boundCost P F boundSelector h1 hMB (by omega)
    (fun i => ⟨by simpa using hb i, by simpa using hM⟩) hBound hfb hib hnb
    (by intro t ht; rw [hab]; simp)
  rintro σ ⟨hσContext, hσA, hσb⟩
  obtain ⟨τ, hr₁, hτContext, hτA⟩ := hm σ ⟨hσContext, hσA⟩
  obtain ⟨υ, hr₂, hυContext, hυb⟩ := hbound τ
    ⟨hτContext, RamAdvanceState.extents_of_run hr₁ "system.b" r hσb⟩
  have hυA := RamReadBody.represents_frame "system.A" (RamMatrixStorage.flatten (rationalProgram F).A) hτA hr₂
    (by
      intro t ht
      simp [RamCopy.suffixes] at ht
      rcases ht with rfl | rfl | rfl
      all_goals simp [RamCertificateBound.buildBound, RamCertificateBound.prepare, RamCertificateBound.selectCoordinate,
        RamBuildVector.build, RamBuildVector.loop, RamBuildVector.step, RamBuildVector.coordinate,
        RamZeroArray.zeroRationalArray, RamZeroArray.fillConstant, Lib.Fill.put, storeReduced, Com.warrs, hab])
  exact ⟨υ, (hr₁.seq hr₂).mono (by omega), hυContext.1, hυA, hυb, hυContext.2⟩

end Lax109476Proofs.RamCertificateBuilder

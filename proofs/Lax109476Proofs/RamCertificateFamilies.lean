import Lax109476Proofs.RamCertificateBuilder
import Lax109476Proofs.RamCertificateMetadata
import Lax109476Proofs.RamPairSelector
import Lax109476Proofs.RamFarkasSelector
import Lax109476Proofs.RamRaySelector
import Lax109476Proofs.CertificateFamilyHeight

namespace Lax109476Proofs.RamCertificateFamilies

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamCertificateSource CertificateFamilyPrograms CertificateFamilyEntries

def withMetadata (metadata matrixSelector boundSelector : Com) : Com :=
  .seq metadata (RamCertificateBuilder.buildSystem matrixSelector boundSelector)

def optimal : Com := withMetadata RamCertificateMetadata.optimal RamPairSelector.selectEntry RamPairSelector.selectBound
def infeasible : Com := withMetadata RamCertificateMetadata.infeasible RamFarkasSelector.selectEntry RamFarkasSelector.selectBound
def unbounded : Com := withMetadata RamCertificateMetadata.unbounded RamRaySelector.selectEntry RamRaySelector.selectBound

def Input {m n : ℕ} (P : Program ℤ m n) (r s : ℕ) (σ : Env) : Prop :=
  Data P σ ∧ Extents "system.A" (r * s) σ ∧ Extents "system.b" r σ

theorem withMetadata_spec (B m n r s metadataCost buildCost : ℕ) (P : Program ℤ m n) (F : Program ℤ r s)
    (metadata matrixSelector boundSelector : Com)
    (hmetadata : Spec B (Data P) metadata (fun _ τ => RamCertificateContext.Context P r s τ) metadataCost)
    (hbuild : Spec B (fun σ => RamCertificateContext.Context P r s σ ∧ Extents "system.A" (r * s) σ ∧ Extents "system.b" r σ)
      (RamCertificateBuilder.buildSystem matrixSelector boundSelector)
      (fun _ τ => Data P τ ∧ RamEquationData.Data F τ) buildCost) :
    Spec B (Input P r s) (withMetadata metadata matrixSelector boundSelector)
      (fun _ τ => Data P τ ∧ RamEquationData.Data F τ) (metadataCost + buildCost) := by
  rintro σ ⟨hσData, hσA, hσb⟩
  obtain ⟨τ, hr₁, hτContext⟩ := hmetadata σ hσData
  obtain ⟨υ, hr₂, hυ⟩ := hbuild τ ⟨hτContext,
    RamAdvanceState.extents_of_run hr₁ "system.A" (r * s) hσA,
    RamAdvanceState.extents_of_run hr₁ "system.b" r hσb⟩
  exact ⟨υ, hr₁.seq hr₂, hυ⟩

theorem optimal_spec (B M m n : ℕ) (P : Program ℤ m n)
    (hM : 1 ≤ M) (hMB : M < B) (hSource : m * n + 2 * m + 2 * n + 8 < B)
    (hSystem : (m + (n + 2)) * (n + m) + (m + (n + 2)) + (n + m) + 4 < B)
    (hA : ∀ i j, (P.A i j).natAbs ≤ M) (hb : ∀ i, (P.b i).natAbs ≤ M)
    (hc : ∀ j, (P.c j).natAbs ≤ M) :
    Spec B (Input P (m + (n + 2)) (n + m)) optimal
      (fun _ τ => Data P τ ∧ RamEquationData.Data (CertificateFamilyPrograms.optimal P) τ)
      (142 * ((m + (n + 2)) * (n + m)) + 98 * (m + (n + 2)) + 72) := by
  have hbuild := RamCertificateBuilder.buildSystem_spec B M m n (m + (n + 2)) (n + m) 72 40 P
    (CertificateFamilyPrograms.optimal P) RamPairSelector.selectEntry RamPairSelector.selectBound hM hMB hSystem
    (CertificateFamilyHeight.optimal_A_bound P M hA hb hc) (CertificateFamilyHeight.optimal_b_bound P M hb hc)
    (fun i j => by simpa only [pairEntry_eq] using RamPairSelector.selectEntry_spec B M m n P i j hM hMB hSource hA hb hc)
    (fun i => by simpa only [pairRhs_eq] using RamPairSelector.selectBound_spec B M m n P i hM hMB (by omega) hb hc)
    (by intro a ha; simp [RamCertificateContext.fields] at ha; rcases ha with rfl | rfl | rfl | rfl <;> decide)
    (by intro a ha; simp [RamCertificateContext.fields] at ha; rcases ha with rfl | rfl | rfl | rfl <;> decide)
    (by decide) (by decide) (by decide) (by decide) (by rfl) (by rfl)
  exact (withMetadata_spec B m n (m + (n + 2)) (n + m) 10 _ P (CertificateFamilyPrograms.optimal P)
    RamCertificateMetadata.optimal RamPairSelector.selectEntry RamPairSelector.selectBound
    (RamCertificateMetadata.optimal_spec B m n P (by omega)) hbuild).mono (by omega)

theorem infeasible_spec (B M m n : ℕ) (P : Program ℤ m n)
    (hM : 1 ≤ M) (hMB : M < B) (hSource : m * n + 2 * m + 2 * n + 8 < B)
    (hSystem : (n + 1) * m + (n + 1) + m + 4 < B)
    (hA : ∀ i j, (P.A i j).natAbs ≤ M) (hb : ∀ i, (P.b i).natAbs ≤ M) :
    Spec B (Input P (n + 1) m) infeasible
      (fun _ τ => Data P τ ∧ RamEquationData.Data (CertificateFamilyPrograms.infeasible P) τ)
      (110 * ((n + 1) * m) + 74 * (n + 1) + 68) := by
  have hbuild := RamCertificateBuilder.buildSystem_spec B M m n (n + 1) m 40 16 P
    (CertificateFamilyPrograms.infeasible P) RamFarkasSelector.selectEntry RamFarkasSelector.selectBound hM hMB hSystem
    (CertificateFamilyHeight.infeasible_A_bound P M hA hb) (CertificateFamilyHeight.infeasible_b_bound P M hM)
    (fun i j => by simpa only [farkasEntry_eq] using RamFarkasSelector.selectEntry_spec B M m n P i j hM hMB hSource hA hb)
    (fun i => by simpa only [farkasRhs_eq P i] using RamFarkasSelector.selectBound_spec B m n P i (by omega))
    (by intro a ha; simp [RamCertificateContext.fields] at ha; rcases ha with rfl | rfl | rfl | rfl <;> decide)
    (by intro a ha; simp [RamCertificateContext.fields] at ha; rcases ha with rfl | rfl | rfl | rfl <;> decide)
    (by decide) (by decide) (by decide) (by decide) (by rfl) (by rfl)
  exact (withMetadata_spec B m n (n + 1) m 6 _ P (CertificateFamilyPrograms.infeasible P)
    RamCertificateMetadata.infeasible RamFarkasSelector.selectEntry RamFarkasSelector.selectBound
    (RamCertificateMetadata.infeasible_spec B m n P (by omega)) hbuild).mono (by omega)

theorem unbounded_spec (B M m n : ℕ) (P : Program ℤ m n)
    (hM : 1 ≤ M) (hMB : M < B) (hSource : m * n + 2 * m + 2 * n + 8 < B)
    (hSystem : (m + (m + 1)) * (n + n) + (m + (m + 1)) + (n + n) + 4 < B)
    (hA : ∀ i j, (P.A i j).natAbs ≤ M) (hb : ∀ i, (P.b i).natAbs ≤ M)
    (hc : ∀ j, (P.c j).natAbs ≤ M) :
    Spec B (Input P (m + (m + 1)) (n + n)) unbounded
      (fun _ τ => Data P τ ∧ RamEquationData.Data (CertificateFamilyPrograms.unbounded P) τ)
      (134 * ((m + (m + 1)) * (n + n)) + 90 * (m + (m + 1)) + 74) := by
  have hbuild := RamCertificateBuilder.buildSystem_spec B M m n (m + (m + 1)) (n + n) 64 32 P
    (CertificateFamilyPrograms.unbounded P) RamRaySelector.selectEntry RamRaySelector.selectBound hM hMB hSystem
    (CertificateFamilyHeight.unbounded_A_bound P M hA hc) (CertificateFamilyHeight.unbounded_b_bound P M hM hb)
    (fun i j => by simpa only [rayEntry_eq] using RamRaySelector.selectEntry_spec B M m n P i j hM hMB hSource hA hc)
    (fun i => by simpa only [rayRhs_eq] using RamRaySelector.selectBound_spec B M m n P i hM hMB (by omega) hb)
    (by intro a ha; simp [RamCertificateContext.fields] at ha; rcases ha with rfl | rfl | rfl | rfl <;> decide)
    (by intro a ha; simp [RamCertificateContext.fields] at ha; rcases ha with rfl | rfl | rfl | rfl <;> decide)
    (by decide) (by decide) (by decide) (by decide) (by rfl) (by rfl)
  exact (withMetadata_spec B m n (m + (m + 1)) (n + n) 12 _ P (CertificateFamilyPrograms.unbounded P)
    RamCertificateMetadata.unbounded RamRaySelector.selectEntry RamRaySelector.selectBound
    (RamCertificateMetadata.unbounded_spec B m n P (by omega)) hbuild).mono (by omega)

end Lax109476Proofs.RamCertificateFamilies

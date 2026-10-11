import Lax109476Proofs.RamEquationBoundSelector

namespace Lax109476Proofs.RamEquationBound

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds RamEquationData EquationQueryEntries RamEllipsoidStep

def selectCoordinate : Com := .seq (.assign "query.row" (.var "build.i")) RamEquationBoundSelector.selectBound

set_option maxHeartbeats 1000000 in
theorem selectCoordinate_spec (B M m n : ℕ) (P : Program ℤ m n) (i : Fin (m + m))
    (hM : 1 ≤ M) (hMB : M < B) (hB : m + m + n + 4 < B)
    (hb : ∀ r, (P.b r).natAbs ≤ M) :
    Spec B (fun σ => Data P σ ∧ σ.vars "build.i" = i.val ∧ σ.vars "build.count" = m + m)
      selectCoordinate (fun _ τ => Data P τ ∧ FractionOutput (bound P i) τ) 35 := by
  have hiB : i.val < B := i.isLt.trans (by omega)
  have hselector := RamEquationBoundSelector.selectBound_spec B M m n P i hM hMB hB hb
  have hbase : Spec B (fun σ => Data P σ ∧ σ.vars "build.i" = i.val ∧ σ.vars "build.count" = m + m)
      selectCoordinate (fun _ τ => FractionOutput (bound P i) τ) 35 := by
    rintro σ ⟨⟨hσA, hσb, hσm, hσn⟩, hσi, hσcount⟩
    run_vcg [hselector]
    all_goals clear hselector
    all_goals simp_all [Data, Represents, arrs_setVar]
    all_goals aesop
  intro σ hσ
  obtain ⟨τ, hr, hτ⟩ := hbase σ hσ
  refine ⟨τ, hr, data_frame hr P hσ.1 ?_ ?_, hτ⟩
  · intro a ha; simp [RamEquationData.fields] at ha; rcases ha with rfl | rfl <;> decide
  · intro a ha s hs; change a ++ s ∉ ([] : List String); simp

def prepare : Com := .assign "build.count" (.add (.var "system.m") (.var "system.m"))
def buildBound : Com := .seq prepare (RamBuildVector.build "point.b" selectCoordinate)

set_option maxHeartbeats 1000000 in
theorem buildBound_spec (B M m n : ℕ) (P : Program ℤ m n)
    (hM : 1 ≤ M) (hMB : M < B) (hB : m + m + n + 4 < B)
    (hb : ∀ r, (P.b r).natAbs ≤ M) :
    Spec B (fun σ => Data P σ ∧ Extents "point.b" (m + m) σ) buildBound
      (fun _ τ => Data P τ ∧ Represents "point.b"
        (List.ofFn (RamStandardPointRecovery.program (IntegerPointRecovery.slackMatrix P) P.b).b) τ)
      (91 * (m + m) + 30) := by
  let N := m + m
  have h1 : 1 < B := by omega
  have hNB : N < B := by dsimp only [N]; omega
  have hbuild := RamBuildVector.build_spec B M N 35 "point.b" (bound P) selectCoordinate (Data P)
    h1 hNB hMB (bound_height P M hM hb)
    (selectCoordinate_spec B M m n P · hM hMB hB hb) (by decide) (by decide)
    (by intro s hs; change "point.b" ++ s ∉ ([] : List String); simp)
    (preserves_data B P (storeReduced "point.b")
      (by intro a ha; simp [RamEquationData.fields] at ha; rcases ha with rfl | rfl <;> decide)
      (by
        intro a ha s hs
        simp [RamEquationData.arrays] at ha
        simp [RamCopy.suffixes] at hs
        rcases ha with rfl | rfl <;> rcases hs with rfl | rfl | rfl <;> decide))
    (preserves_data B P (RamZeroArray.zeroRationalArray "point.b")
      (by intro a ha; simp [RamEquationData.fields] at ha; rcases ha with rfl | rfl <;> decide)
      (by
        intro a ha s hs
        simp [RamEquationData.arrays] at ha
        simp [RamCopy.suffixes] at hs
        rcases ha with rfl | rfl <;> rcases hs with rfl | rfl | rfl <;> decide))
    (fun σ z h => data_setVar P σ "build.i" z (by decide) h)
    (fun σ z h => data_setVar P σ "vec.i" z (by decide) h)
    (fun σ z h => data_setVar P σ "vec.n" z (by decide) h)
  have hvalues : List.ofFn (bound P) = List.ofFn
      (RamStandardPointRecovery.program (IntegerPointRecovery.slackMatrix P) P.b).b := by
    congr 1; funext i; exact bound_eq P i
  have hmeta : Spec B (fun σ => σ.vars "system.m" = m) prepare (fun _ τ => τ.vars "build.count" = N) 4 := by
    intro σ hm
    run_vcg
    all_goals simp_all [N]
    all_goals omega
  rintro σ ⟨hσData, hσtarget⟩
  obtain ⟨τ, hr₁, hτcount⟩ := hmeta σ hσData.2.2.1
  have hτData := data_frame hr₁ P hσData
    (by intro a ha; simp [RamEquationData.fields] at ha; rcases ha with rfl | rfl <;> decide)
    (by intro a ha s hs; simp [Com.warrs, prepare])
  obtain ⟨υ, hr₂, hυData, hυtarget, hυcount⟩ := hbuild τ
    ⟨hτData, RamAdvanceState.extents_of_run hr₁ "point.b" N hσtarget, hτcount⟩
  refine ⟨υ, (hr₁.seq hr₂).mono ?_, hυData, ?_⟩
  · dsimp only [N]; omega
  · simpa only [hvalues] using hυtarget

end Lax109476Proofs.RamEquationBound

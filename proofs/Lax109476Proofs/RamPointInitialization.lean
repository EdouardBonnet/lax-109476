import Lax109476Proofs.RamPointRecoveryBounds

namespace Lax109476Proofs.RamPointInitialization

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamRecoveryThreshold RamEllipsoidStep RationalArithmeticBounds

def Base {m n : ℕ} (P : Program ℚ m n) (σ : Env) : Prop :=
  Represents "point.A" (RamMatrixStorage.flatten P.A) σ ∧ Represents "point.b" (List.ofFn P.b) σ ∧
    σ.vars "point.m" = m ∧ σ.vars "point.n" = n

def prepare : Com := .seq (.assign "vec.n" (.var "point.n"))
  (.seq (RamZeroArray.zeroRationalArray "point.x") (.assign "point.k" (.lit 0)))

theorem prepare_spec (B m n : ℕ) (P : Program ℚ m n) (hnB : n < B) (h1 : 1 < B) :
    Spec B (fun σ => Base P σ ∧ Workspace m n σ ∧ Extents "point.x" n σ) prepare
      (fun _ τ => Persistent P 0 0 τ) (33 * n + 22) := by
  have hz := RamZeroArray.zeroRationalArray_spec B n "point.x" hnB h1
  have hbase : Spec B (fun σ => σ.vars "point.n" = n ∧ Extents "point.x" n σ) prepare
      (fun _ τ => Represents "point.x" (List.replicate n 0) τ ∧ τ.vars "point.k" = 0)
      (33 * n + 22) := by
    rintro σ ⟨hn, he⟩
    have hs := he ".s" (by simp)
    have hnum := he ".n" (by simp)
    have hd := he ".d" (by simp)
    run_vcg [hz]
    all_goals clear hz
    all_goals simp_all [Represents, arrs_setVar]
  rintro σ ⟨⟨hσA, hσb, hσm, hσn⟩, hσW, hσx⟩
  obtain ⟨τ, hr, hτx, hτk⟩ := hbase σ ⟨hσn, hσx⟩
  have hτA := RamReadBody.represents_frame "point.A" (RamMatrixStorage.flatten P.A) hσA hr
    (by intro s hs; simp at hs; rcases hs with rfl | rfl | rfl <;> decide)
  have hτb := RamReadBody.represents_frame "point.b" (List.ofFn P.b) hσb hr
    (by intro s hs; simp at hs; rcases hs with rfl | rfl | rfl <;> decide)
  refine ⟨τ, hr, ⟨hτA, hτb, ?_, (hr.frame_var _ (by decide)).trans hσm,
    (hr.frame_var _ (by decide)).trans hσn, hτk⟩, workspace_frame hr _ _ hσW⟩
  change Represents "point.x" (List.ofFn (fun _ : Fin n => (0 : ℚ))) τ
  simpa using hτx

def recover : Com := .seq prepare RamPointRecovery.recover

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem recover_spec (m n S C N D w : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ)
    (hD : D.size ≤ C) (hS : 4 * C + 2 ≤ S)
    (hN : RamRationalReconstruction.depthBound S + 1 ≤ N)
    (hw : RamPointRecoveryBounds.wordWidth m n S ≤ w)
    (hA : ∀ i j, Height (P.A i j) (2 ^ S)) (hb : ∀ i, Height (P.b i) (2 ^ S))
    (hxHeight : ∀ j, Height (x j) (2 ^ S)) (hc : ∀ j, P.c j = 0)
    (hx : PrimalFeasible (toReal P) (realVector x))
    (hlex : ∀ i, ∀ y, PrimalFeasible (toReal P) y →
      (∀ j, j < i → y j = (x j : ℝ)) → (x i : ℝ) ≤ y i)
    (hxBound : ∀ j, x j ≤ D ∧ (x j).den ≤ D) :
    Spec (2 ^ w) (fun σ => Base P σ ∧ Workspace m n σ ∧ Extents "point.x" n σ ∧
      σ.vars "minimum.bound" = D ∧ (σ.arrs "cf.stack").length = N) recover
      (fun _ τ => Persistent P x n τ ∧ τ.vars "minimum.bound" = D ∧ (τ.arrs "cf.stack").length = N)
      (33 * n + 22 + RamPointRecoveryBounds.instructionBound m n S C) := by
  have b := RamPointRecoveryBounds.resource_bounds m n S C N D w hD hS hN hw
  have hn : n < 2 ^ w := by have := b.dimensions; omega
  have h1 : 1 < 2 ^ w := by have := b.midpoint; omega
  rintro σ ⟨hσBase, hσWork, hσx, hσD, hσN⟩
  obtain ⟨τ, hr₁, hτ⟩ := prepare_spec (2 ^ w) m n P hn h1 σ ⟨hσBase, hσWork, hσx⟩
  have hτD := (hr₁.frame_var "minimum.bound" (by decide)).trans hσD
  have hτN : (τ.arrs "cf.stack").length = N := by rw [hr₁.frame_arr _ (by decide)]; exact hσN
  have hp : PointRecovery.prefixVector x 0 = 0 := by funext j; simp [PointRecovery.prefixVector]
  obtain ⟨υ, hr₂, hυ⟩ := RamPointRecoveryBounds.recover_bounded_spec m n S C N D w P x hD hS hN hw
    hA hb hxHeight hc hx hlex hxBound τ ⟨by simpa only [hp] using hτ, hτD, hτN⟩
  exact ⟨υ, hr₁.seq hr₂, hυ⟩

end Lax109476Proofs.RamPointInitialization

import Lax109476Proofs.RamRecoveryMinimum
import Lax109476Proofs.PointRecoveryCoordinate
import Lax109476Proofs.RamArrayResult

namespace Lax109476Proofs.RamPointRecoveryStep

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamRationalScalars RamScalarFrame RamRecoveryThreshold
open RationalArithmeticBounds PointRecovery

def install : Com := .seq (RamScalarCopy.copy "recon.result" "rat")
  (.seq (.assign "vec.i" (.var "point.k"))
    (.seq (storeReduced "point.x") (.assign "point.k" (.add (.var "point.k") (.lit 1)))))

def step : Com := .seq RamRecoveryMinimum.recoverCoordinate install

def coordinateCost (S D M m n : ℕ) : ℕ :=
  (144 * M.size + 342 + instructionBound m n (4 * M ^ 2)) * BinaryOptimization.steps D +
    12 * D.size + RamRationalReconstruction.instructionBound S + 48

theorem prefix_height {n : ℕ} (x : Fin n → ℚ) (k M : ℕ) (hM : 1 ≤ M)
    (hx : ∀ j, Height (x j) M) : ∀ j, Height (prefixVector x k j) M := by
  intro j
  dsimp only [prefixVector]
  split_ifs
  · exact hx j
  · exact height_mono 0 height_zero (by omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1500000 in
theorem step_spec (S N w D M m n k : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ)
    (hk : k < n) (hB : 4 * M ^ 2 + 3 < 2 ^ w) (hKB : BinaryOptimization.steps D < 2 ^ w)
    (hM : (D + 1) * 2 ^ BinaryOptimization.steps D ≤ M) (hMS : M ≤ 2 ^ S)
    (hN : RamRationalReconstruction.depthBound S + 1 ≤ N)
    (hw : RamRationalReconstruction.wordWidth S ≤ w) (hDB : D < 2 ^ w)
    (hsize : ((m + (n + n)) + 1) * n + m + (n + n) + 4 < 2 ^ w)
    (hwQuery : RamStoredFeasibility.wordWidth (sizeBound m n (4 * M ^ 2)) ≤ w)
    (hA : ∀ i j, Height (P.A i j) M) (hb : ∀ i, Height (P.b i) M)
    (hxHeight : ∀ j, Height (x j) M) (hc : ∀ j, P.c j = 0)
    (hx : PrimalFeasible (toReal P) (realVector x))
    (hlex : ∀ i, ∀ y, PrimalFeasible (toReal P) y →
      (∀ j, j < i → y j = (x j : ℝ)) → (x i : ℝ) ≤ y i)
    (hxBound : ∀ j, x j ≤ D ∧ (x j).den ≤ D) :
    Spec (2 ^ w) (fun σ => Persistent P (prefixVector x k) k σ ∧
      σ.vars "minimum.bound" = D ∧ (σ.arrs "cf.stack").length = N) step
      (fun σ τ => Persistent P (prefixVector x (k + 1)) (k + 1) τ ∧
        τ.vars "minimum.bound" = D ∧ (τ.arrs "cf.stack").length = N ∧
        τ.vars "point.k" = σ.vars "point.k" + 1)
      (coordinateCost S D M m n + 25) := by
  have hM1 : 1 ≤ M := by
    have hp : 1 ≤ 2 ^ BinaryOptimization.steps D := Nat.one_le_pow _ _ (by decide)
    nlinarith
  have hMB : M < 2 ^ w := by nlinarith
  have hnB : n < 2 ^ w := by omega
  have hkB : k < 2 ^ w := hk.trans hnB
  have h1 : 1 < 2 ^ w := by omega
  have hcoord := coordinateMinimum_prefix P D x hx hlex hxBound k hk
  let i : Fin n := ⟨k, hk⟩
  rintro σ ⟨hσP, hσD, hσN⟩
  obtain ⟨τ, hr₁, hτP, hτout⟩ := RamRecoveryMinimum.recoverCoordinate_spec S N w D M m n k P (prefixVector x k)
    hk hB hKB hM hMS hN hw hDB hsize hwQuery hA hb (prefix_height x k M hM1 hxHeight) hc σ ⟨hσP, hσD, hσN⟩
  rw [hcoord] at hτout
  change τ.vars "recon.found" = 1 ∧ Value "recon.result" (x i) τ at hτout
  obtain ⟨υ, hr₂, hυrat⟩ := RamArrayResult.copyResult_spec (2 ^ w) "recon.result" (x i) h1
    ((hxHeight i).1.trans_lt hMB) ((hxHeight i).2.trans_lt hMB)
    (by simp [RamCopy.Disjoint, RamCopy.suffixes]) τ hτout.2
  have hυk : υ.vars "point.k" = k := (hr₂.frame_var _ (by decide)).trans hτP.1.2.2.2.2.2
  have hr₃ : Run (2 ^ w) (.assign "vec.i" (.var "point.k")) υ (υ.setVar "vec.i" k) 2 :=
    Run.assign (by simpa only [hυk] using (evalB_var (B := 2 ^ w) (σ := υ) (x := "point.k") (hυk ▸ hkB)))
  have hυx := RamReadBody.represents_frame "point.x" (List.ofFn (prefixVector x k)) hτP.1.2.2.1 hr₂
    (by intro s hs; change "point.x" ++ s ∉ ([] : List String); simp)
  obtain ⟨ρ, hr₄, hρx⟩ := storeReduced_spec (2 ^ w) "point.x" (List.ofFn (prefixVector x k)) (x i) k
    (by simpa using hk) h1 hkB ((hxHeight i).1.trans_lt hMB) ((hxHeight i).2.trans_lt hMB)
    (υ.setVar "vec.i" k) ⟨hυx, by simp, value_frame hr₃ "rat" (x i) hυrat (by decide) (by decide) (by decide)⟩
  have hρk : ρ.vars "point.k" = k :=
    (hr₄.frame_var _ (by decide)).trans ((hr₃.frame_var _ (by decide)).trans hυk)
  have hsum : Bop.add.apply (ρ.vars "point.k") 1 < 2 ^ w := by simpa [hρk] using (show k + 1 < 2 ^ w by omega)
  have hr₅ : Run (2 ^ w) (.assign "point.k" (.add (.var "point.k") (.lit 1))) ρ (ρ.setVar "point.k" (k + 1)) 4 :=
    Run.assign (by simpa only [hρk, Bop.apply_add] using (evalB_bin
      (evalB_var (B := 2 ^ w) (σ := ρ) (x := "point.k") (hρk ▸ hkB)) (evalB_lit h1) hsum))
  let ξ := ρ.setVar "point.k" (k + 1)
  have hrRest := hr₂.seq (hr₃.seq (hr₄.seq hr₅))
  have hr := hr₁.seq hrRest
  have hξA := RamReadBody.represents_frame "point.A" (RamMatrixStorage.flatten P.A) hτP.1.1 hrRest
    (by intro s hs; simp [RamCopy.suffixes] at hs; rcases hs with rfl | rfl | rfl <;> decide)
  have hξb := RamReadBody.represents_frame "point.b" (List.ofFn P.b) hτP.1.2.1 hrRest
    (by intro s hs; simp [RamCopy.suffixes] at hs; rcases hs with rfl | rfl | rfl <;> decide)
  have hξx : Represents "point.x" (List.ofFn (prefixVector x (k + 1))) ξ := by
    have he : (List.ofFn (prefixVector x k)).set k (x i) = List.ofFn (prefixVector x (k + 1)) :=
      RamCenterUpdate.filled_step x i
    rw [he] at hρx
    simpa only [ξ, Represents, arrs_setVar] using hρx
  have hξm := (hrRest.frame_var "point.m" (by decide)).trans hτP.1.2.2.2.1
  have hξn := (hrRest.frame_var "point.n" (by decide)).trans hτP.1.2.2.2.2.1
  have hξD := (hr.frame_var "minimum.bound" (by decide)).trans hσD
  have hξN : (ξ.arrs "cf.stack").length = N := by
    obtain ⟨_, _, hs⟩ := hr.bigStep
    exact (RamAdvanceState.array_length_of_bigStep hs "cf.stack").trans hσN
  refine ⟨ξ, hr.mono (by dsimp only [coordinateCost]; omega),
    ⟨⟨hξA, hξb, hξx, hξm, hξn, by simp [ξ]⟩, workspace_frame hr _ _ hσP.2⟩, hξD, hξN, ?_⟩
  simp [ξ, hσP.1.2.2.2.2.2]

end Lax109476Proofs.RamPointRecoveryStep

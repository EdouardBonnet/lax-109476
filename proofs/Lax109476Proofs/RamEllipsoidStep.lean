import Lax109476Proofs.RamEllipsoidUpdate
import Lax109476Proofs.RamEllipsoidWordBounds
import Lax109476Proofs.RamEllipsoidPrecision

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamEllipsoidStep

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds
open RamEllipsoidUpdate RamEllipsoidWordBounds RamEllipsoidPrecision RamEllipsoidCoefficients
open RamEllipsoidScalars RamEllipsoidForm RamMatrixVector RamMatrixRows RamDotProduct RamMatrixStorage

/-- Three equal extents for the sign, numerator, and denominator arrays. -/
def Extents (a : String) (n : ℕ) (σ : Env) : Prop :=
  ∀ s ∈ [".s", ".n", ".d"], (σ.arrs (a ++ s)).length = n

def Workspace (n : ℕ) (σ : Env) : Prop :=
  Extents "ell.u" n σ ∧ Extents "ell.coeff" 5 σ ∧
    Extents "ell.nextcenter" n σ ∧ Extents "ell.nextshape" (n * n) σ

theorem extents_frame {B K : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ K)
    (a : String) (n : ℕ) (hσ : Extents a n σ)
    (ha : ∀ s ∈ [".s", ".n", ".d"], a ++ s ∉ c.warrs) : Extents a n τ := by
  intro s hs
  rw [hr.frame_arr _ (ha s hs)]
  exact hσ s hs

theorem form_no_other_writes (b : String)
    (hb : b ∉ ["ell.u.s", "ell.u.n", "ell.u.d"]) : b ∉ ellipsoidForm.warrs := by
  simp at hb
  simp [ellipsoidForm, ellipsoidMulVecInitialized, ellipsoidMulVec, matrixVectorStep, storeDotAtRow,
    RamZeroArray.zeroRationalArray, RamZeroArray.fillConstant, Lib.Fill.put, saveForm,
    matrixRowDot, rowDotProduct, rowDotStep, multiplyRowAt, loadRowLeft,
    RamDotProduct.dotProduct, dotStep, multiplyAt, addToAccumulator, loadLeft, loadRight,
    storeReduced, multiplyFraction, addFraction, RamArithmetic.normalizeFraction,
    RamArithmetic.gcdLoop, RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.warrs,
    hb.1, hb.2.1, hb.2.2]

theorem form_iter_frame {B K : ℕ} {σ τ : Env} (hr : Run B ellipsoidForm σ τ K) :
    τ.vars "iter.k" = σ.vars "iter.k" := by
  apply hr.frame_var
  simp [ellipsoidForm, ellipsoidMulVecInitialized, ellipsoidMulVec, matrixVectorStep, storeDotAtRow,
    RamZeroArray.zeroRationalArray, RamZeroArray.fillConstant, Lib.Fill.put, saveForm,
    matrixRowDot, rowDotProduct, rowDotStep, multiplyRowAt, loadRowLeft,
    RamDotProduct.dotProduct, dotStep, multiplyAt, addToAccumulator, loadLeft, loadRight,
    storeReduced, multiplyFraction, addFraction, RamArithmetic.normalizeFraction,
    RamArithmetic.gcdLoop, RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.wvars]

theorem coefficients_no_other_writes (b : String)
    (hb : b ∉ ["ell.coeff.s", "ell.coeff.n", "ell.coeff.d"]) : b ∉ prepareCoefficients.warrs := by
  simp at hb
  simp [prepareCoefficients, initializeCoefficients, computeCoefficients, computeAndStore,
    storeCoefficient, storeReduced, RamZeroArray.zeroRationalArray, RamZeroArray.fillConstant,
    Lib.Fill.put, alphaFraction, betaFraction, gammaFraction, scaledInverseFraction, inflationFraction,
    diagonalFraction, RamRounding.upperRootFraction, RamSquareRoot.squareRoot, RamSquareRoot.sqrtLoop,
    RamSquareRoot.sqrtStep, RamArithmetic.normalizeFraction, RamArithmetic.gcdLoop,
    RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.warrs, hb.1, hb.2.1, hb.2.2]

theorem form_height (n H : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (a : Fin n → ℚ)
    (hH : 1 ≤ H) (hA : ∀ i j, Height (A i j) H) (ha : ∀ i, Height (a i) H) :
    Height (a ⬝ᵥ (A *ᵥ a)) (formHeight n H) := by
  have hcap := (cap_ge n H hH).2
  have hna : (List.ofFn a).length = n := by simp
  have hnu : (List.ofFn (A *ᵥ a)).length = n := by simp
  have han : ∀ q ∈ List.ofFn a, Height q (cap n H) := by
    intro q hq
    simp only [List.mem_ofFn] at hq
    obtain ⟨i, rfl⟩ := hq
    exact height_mono _ (ha i) hcap
  have hun : ∀ q ∈ List.ofFn (A *ᵥ a), Height q (cap n H) := by
    intro q hq
    simp only [List.mem_ofFn] at hq
    obtain ⟨i, rfl⟩ := hq
    exact mulVec_height n H A a hH hA ha i
  change Height (∑ j, a j * (A *ᵥ a) j) (formHeight n H)
  rw [← prefix_ofFn]
  exact prefix_height _ _ n (cap n H) n (hH.trans hcap) hna hnu le_rfl han hun

def formCost (n H : ℕ) : ℕ :=
  33 * n + 18 + (((4 + ((144 * (cap n H).size + 216 + 4) * n + 12) + 21 + 4) + 4) * n + 8) +
    (((144 * (formHeight n H).size + 210 + 4) * n + 12) + 6)

def updateCost (n M : ℕ) : ℕ :=
  (33 * n + 18 + ((180 * (RamCenterCoordinate.centerCap M).size + 318 + 4 + 4) * n + 6)) +
    (33 * (n * n) + 26 + ((468 * (RamShapeCoordinate.shapeCap M).size + 690 + 4 + 4) * (n * n) + 10))

def stepCost (n H M : ℕ) : ℕ := formCost n H + 20 + (582 * M.size + 876) + updateCost n (coefficientCap M)

def ellipsoidStep : Com :=
  .seq ellipsoidForm (.seq preparePrecision (.seq prepareCoefficients roundedUpdate))



set_option maxRecDepth 6000 in
set_option maxHeartbeats 1200000 in
theorem ellipsoidStep_spec (B n H M k : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ)
    (hn : 2 ≤ n) (hH : 1 ≤ H) (hA : ∀ i j, Height (A i j) H)
    (ha : ∀ i, Height (a i) H) (hc : ∀ i, Height (c i) H)
    (hqpos : 0 < a ⬝ᵥ (A *ᵥ a)) (hnM : n * n ≤ M) (hFM : formHeight n H ≤ M)
    (hDM : 2 ^ (2 * k + 3 * n + 9) ≤ M) (hEM : 2 ^ (2 * n + 4) ≤ M)
    (hB : 2 * (RamShapeCoordinate.shapeCap (coefficientCap M)) ^ 2 + 3 < B) :
    Spec B (fun σ => Represents "ell.shape" (flatten A) σ ∧ Represents "ell.normal" (List.ofFn a) σ ∧
        Represents "ell.center" (List.ofFn c) σ ∧ Workspace n σ ∧
        σ.vars "vec.n" = n ∧ σ.vars "iter.k" = k)
      ellipsoidStep
      (fun _ τ => Represents "ell.nextcenter"
          (List.ofFn (EllipsoidCenter.roundedCenter n A a c (2 ^ (2 * k + 3 * n + 9)))) τ ∧
        Represents "ell.nextshape"
          (flatten (EllipsoidCenter.roundedStepShape n A a (2 ^ (2 * k + 3 * n + 9))
            (EllipsoidIteration.stepAccuracy n))) τ ∧
        Represents "ell.shape" (flatten A) τ ∧ Represents "ell.center" (List.ofFn c) τ ∧
        τ.vars "vec.n" = n ∧ τ.vars "grid.D" = 2 ^ (2 * k + 3 * n + 9))
      (stepCost n H M) := by
  let D := 2 ^ (2 * k + 3 * n + 9)
  let E := 2 ^ (2 * n + 4)
  let q := a ⬝ᵥ (A *ᵥ a)
  let N := coefficientCap M
  let gs := coefficients n q D E
  have hcapM : cap n H ≤ M := (formHeight_ge n H hH).trans hFM
  have hHM : H ≤ M := (cap_ge n H hH).2.trans hcapM
  have hM : 1 ≤ M := hH.trans hHM
  have hMN : M ≤ N := (coefficientCap_bounds M).1
  have hN : 1 ≤ N := hM.trans hMN
  have hbounds := unified_word_bounds B M n hn hnM hB
  have hNB : N < B := hbounds.1
  have hMB : M < B := hbounds.2.1
  have hnnB : n ^ 2 < B := hbounds.2.2.1
  have hnB : n < B := hbounds.2.2.2.1
  have h5B : 5 < B := hbounds.2.2.2.2.1
  have hdims := hbounds.2.2.2.2.2.1
  have hPrimB := hbounds.2.2.2.2.2.2.1
  have hRootB := hbounds.2.2.2.2.2.2.2.1
  have hCenterB := hbounds.2.2.2.2.2.2.2.2
  have hnleM : n ≤ M := by
    have hnp : n ≤ n * n := by
      simpa only [pow_two] using le_self_pow (by omega : 1 ≤ n) (by decide : (2 : ℕ) ≠ 0)
    exact hnp.trans hnM
  have hDpos : 0 < D := Nat.pow_pos (by decide)
  have hEpos : 0 < E := Nat.pow_pos (by decide)
  have hDB : D < B := hDM.trans_lt hMB
  have hEB : E < B := hEM.trans_lt hMB
  have hInflB : (E + 1) ^ 2 < B := by
    have hp := (Nat.pow_le_pow_left (Nat.add_le_add_right hEM 1) 2).trans
      (Nat.pow_le_pow_right (by omega : 1 ≤ M + 1) (by decide : (2 : ℕ) ≤ 4))
    have htoN : (M + 1) ^ 4 ≤ N := by dsimp [N, coefficientCap]; omega
    exact hp.trans htoN |>.trans_lt hNB
  have hFormB : 2 * (formHeight n H) ^ 2 + 3 < B := by
    have hp := Nat.pow_le_pow_left hFM 2
    exact lt_of_le_of_lt (by omega) hPrimB
  have hq : Height q M := height_mono _ (form_height n H A a hH hA ha) hFM
  have hu : ∀ i, Height ((A *ᵥ a) i) N := fun i =>
    height_mono _ (mulVec_height n H A a hH hA ha i) (hcapM.trans hMN)
  have hAc : ∀ i j, Height (A i j) N := fun i j => height_mono _ (hA i j) (hHM.trans hMN)
  have hcc : ∀ i, Height (c i) N := fun i => height_mono _ (hc i) (hHM.trans hMN)
  have hgs : ∀ v ∈ gs, Height v N := coefficients_height n M D E q hq hnleM hDM hEM hDpos
  have hg : 4 < gs.length := by simp [gs, coefficients]
  have hα := hgs gs[0] (by simp [gs, coefficients])
  have hβ := hgs gs[1] (by simp [gs, coefficients])
  have hγ := hgs gs[2] (by simp [gs, coefficients])
  have hρ := hgs gs[3] (by simp [gs, coefficients])
  have hδ := hgs gs[4] (by simp [gs, coefficients])
  rintro σ ⟨hσA, hσa, hσc, ⟨hσuExt, hσgExt, hσcExt, hσAExt⟩, hσn, hσk⟩
  obtain ⟨τ, hr₁, hτq, hτu, _, _, hτn⟩ := ellipsoidForm_spec B n H A a hH hA ha hdims hFormB
    σ ⟨rows_of_represents "ell.shape" A σ hσA, hσa,
      hσuExt ".s" (by simp), hσuExt ".n" (by simp), hσuExt ".d" (by simp), hσn⟩
  have hτA := represents_frame hr₁ "ell.shape" _ hσA
    (form_no_other_writes _ (by simp)) (form_no_other_writes _ (by simp)) (form_no_other_writes _ (by simp))
  have hτc := represents_frame hr₁ "ell.center" _ hσc
    (form_no_other_writes _ (by simp)) (form_no_other_writes _ (by simp)) (form_no_other_writes _ (by simp))
  have hτgExt := extents_frame hr₁ "ell.coeff" 5 hσgExt (by
    intro s hs; simp at hs; rcases hs with rfl | rfl | rfl <;> exact form_no_other_writes _ (by simp))
  have hτcExt := extents_frame hr₁ "ell.nextcenter" n hσcExt (by
    intro s hs; simp at hs; rcases hs with rfl | rfl | rfl <;> exact form_no_other_writes _ (by simp))
  have hτAExt := extents_frame hr₁ "ell.nextshape" (n * n) hσAExt (by
    intro s hs; simp at hs; rcases hs with rfl | rfl | rfl <;> exact form_no_other_writes _ (by simp))
  have hτk : τ.vars "iter.k" = k := (form_iter_frame hr₁).trans hσk
  obtain ⟨υ, hr₂, hυE, hυD, hυn, _, hυarr⟩ := preparePrecision_spec B k n hEB hDB τ ⟨hτn, hτk⟩
  have hυq := precision_form_frame hr₂ q hτq
  have hυA : Represents "ell.shape" (flatten A) υ := by simpa only [Represents, hυarr] using hτA
  have hυc : Represents "ell.center" (List.ofFn c) υ := by simpa only [Represents, hυarr] using hτc
  have hυu : Represents "ell.u" (List.ofFn (A *ᵥ a)) υ := by simpa only [Represents, hυarr] using hτu
  have hυgExt : Extents "ell.coeff" 5 υ := by simpa only [Extents, hυarr] using hτgExt
  have hυcExt : Extents "ell.nextcenter" n υ := by simpa only [Extents, hυarr] using hτcExt
  have hυAExt : Extents "ell.nextshape" (n * n) υ := by simpa only [Extents, hυarr] using hτAExt
  obtain ⟨ρ, hr₃, hρg, hρinput⟩ := prepareCoefficients_spec B n M D E q hn hqpos hq hnleM hDM hEM
    hDpos hEpos hnnB hInflB hPrimB hRootB hNB h5B υ
    ⟨⟨hυq, hυn, hυD, hυE⟩, hυgExt ".s" (by simp), hυgExt ".n" (by simp), hυgExt ".d" (by simp)⟩
  have hρA := represents_frame hr₃ "ell.shape" _ hυA
    (coefficients_no_other_writes _ (by simp)) (coefficients_no_other_writes _ (by simp)) (coefficients_no_other_writes _ (by simp))
  have hρc := represents_frame hr₃ "ell.center" _ hυc
    (coefficients_no_other_writes _ (by simp)) (coefficients_no_other_writes _ (by simp)) (coefficients_no_other_writes _ (by simp))
  have hρu := represents_frame hr₃ "ell.u" _ hυu
    (coefficients_no_other_writes _ (by simp)) (coefficients_no_other_writes _ (by simp)) (coefficients_no_other_writes _ (by simp))
  have hρcExt := extents_frame hr₃ "ell.nextcenter" n hυcExt (by
    intro s hs; simp at hs; rcases hs with rfl | rfl | rfl <;> exact coefficients_no_other_writes _ (by simp))
  have hρAExt := extents_frame hr₃ "ell.nextshape" (n * n) hυAExt (by
    intro s hs; simp at hs; rcases hs with rfl | rfl | rfl <;> exact coefficients_no_other_writes _ (by simp))
  obtain ⟨ξ, hr₄, hξc, hξA, _, hξoldc, hξoldA, _, hξn, hξD⟩ := roundedUpdate_ellipsoid_spec B n N D E A a c gs hg
    hN (hnM.trans hMN) hu hcc hAc hα hβ hγ hρ hδ (hDM.trans hMN) hDpos
    (by simpa only [pow_two] using hnnB) hnB hCenterB hB rfl ρ
    ⟨hρu, hρc, hρA, hρg, hρcExt ".s" (by simp), hρcExt ".n" (by simp), hρcExt ".d" (by simp),
      hρAExt ".s" (by simp), hρAExt ".n" (by simp), hρAExt ".d" (by simp), hρinput.2.1, hρinput.2.2.1⟩
  have hη : (1 / (E : ℚ)) = EllipsoidIteration.stepAccuracy n := by
    simp [E, EllipsoidIteration.stepAccuracy]
  refine ⟨ξ, (hr₁.seq (hr₂.seq (hr₃.seq hr₄))).mono ?_, ?_, ?_, hξoldA, hξoldc, hξn, hξD⟩
  · change formCost n H + (20 + (582 * M.size + 876 + updateCost n N)) ≤ stepCost n H M
    simp only [stepCost, N]
    omega
  · exact hξc
  · simpa only [hη] using hξA



theorem coefficientCap_size (M : ℕ) : (coefficientCap M).size ≤ 4 * M.size + 8 := by
  have hb := RationalSizeBounds.size_add_one_le M
  have hp := RationalSizeBounds.size_pow_le (M + 1) 4
  have hm := RationalSizeBounds.size_mul_le 4 ((M + 1) ^ 4)
  have hfour : Nat.size 4 = 3 := by decide
  unfold coefficientCap
  omega

theorem stepCost_polynomial (n H M : ℕ) :
    stepCost n H M ≤
      (144 * ((n + 1) * (2 * H.size + 3) + 1) + 220) * n ^ 2 +
      (144 * ((n + 1) * (2 * ((n + 1) * (2 * H.size + 3) + 1) + 3) + 1) + 292) * n +
      (2880 * M.size + 7559) * n + (14976 * M.size + 36767) * (n * n) + 582 * M.size + 1000 := by
  have hcap := coefficientCap_size M
  have hlin := Nat.mul_le_mul_right n (Nat.add_le_add_right (Nat.mul_le_mul_left 720 hcap) 1799)
  have hquad := Nat.mul_le_mul_right (n * n) (Nat.add_le_add_right (Nat.mul_le_mul_left 3744 hcap) 6815)
  have hupdate := roundedUpdate_cost_polynomial n (coefficientCap M)
  have hupdate' : updateCost n (coefficientCap M) ≤
      (2880 * M.size + 7559) * n + (14976 * M.size + 36767) * (n * n) + 60 := by
    have hp := Nat.add_le_add_right (Nat.add_le_add hlin hquad) 60
    have hpay := hupdate.trans hp
    convert hpay using 1 <;> first | rfl | ring | (simp only [updateCost] <;> ring)
  let P := (144 * ((n + 1) * (2 * H.size + 3) + 1) + 220) * n ^ 2 +
    (144 * ((n + 1) * (2 * ((n + 1) * (2 * H.size + 3) + 1) + 3) + 1) + 292) * n + 44
  let R := (2880 * M.size + 7559) * n + (14976 * M.size + 36767) * (n * n) + 60
  have hform : formCost n H ≤ P := ellipsoidForm_cost_polynomial n H
  have htotal : formCost n H + updateCost n (coefficientCap M) ≤ P + R := Nat.add_le_add hform hupdate'
  calc
    stepCost n H M = (formCost n H + updateCost n (coefficientCap M)) + (20 + (582 * M.size + 876)) := by
      unfold stepCost
      omega
    _ ≤ (P + R) + (20 + (582 * M.size + 876)) := Nat.add_le_add_right htotal _
    _ = _ := by dsimp only [P, R]; ring



theorem form_pos_of_posDef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (a : Fin n → ℚ)
    (hA : (EllipsoidRounding.realShape A).PosDef) (ha : a ≠ 0) : 0 < a ⬝ᵥ (A *ᵥ a) := by
  have hreal : Lax109476.RationalCertificates.realVector a ≠ 0 := by
    intro h
    apply ha
    funext i
    have hi := congrFun h i
    change (a i : ℝ) = 0 at hi
    exact_mod_cast hi
  have hpos := hA.dotProduct_mulVec_pos hreal
  have hpos' : 0 < Lax109476.RationalCertificates.realVector a ⬝ᵥ
      (EllipsoidRounding.realShape A *ᵥ Lax109476.RationalCertificates.realVector a) := by simpa using hpos
  rw [← EllipsoidCenter.cast_direction_form n A a] at hpos'
  exact_mod_cast hpos' 

end Lax109476Proofs.RamEllipsoidStep

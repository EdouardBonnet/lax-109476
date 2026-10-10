import Lax109476Proofs.RamShapeUpdate
import Lax109476Proofs.RamCenterUpdate
import Lax109476Proofs.RamEllipsoidCoefficients

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamEllipsoidUpdate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds
open RamCenterCoordinate RamCenterUpdate RamShapeCoordinate RamShapeUpdate
open RamEllipsoidCoefficients RamMatrixStorage

theorem represents_frame {B K : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ K)
    (a : String) (qs : List ℚ) (hσ : Represents a qs σ)
    (hs : a ++ ".s" ∉ c.warrs) (hn : a ++ ".n" ∉ c.warrs) (hd : a ++ ".d" ∉ c.warrs) :
    Represents a qs τ := by
  simpa only [Represents, hr.frame_arr (a ++ ".s") hs,
    hr.frame_arr (a ++ ".n") hn, hr.frame_arr (a ++ ".d") hd] using hσ

theorem center_no_other_writes (a : String)
    (ha : a ∉ ["ell.nextcenter.s", "ell.nextcenter.n", "ell.nextcenter.d"]) : a ∉ updateCenter.warrs := by
  simp at ha
  simp [updateCenter, centerLoop, centerStep, centerCoordinate, RamZeroArray.zeroRationalArray,
    RamZeroArray.fillConstant, Lib.Fill.put, loadLeft, loadRight, storeReduced, multiplyFraction,
    RamFractionInterface.subtractFraction, RamFractionInterface.negateRight,
    RamFractionInterface.resultToRight, RamFractionInterface.resultToLeft,
    RamRounding.roundFraction, addFraction, RamArithmetic.normalizeFraction, RamArithmetic.gcdLoop,
    RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.warrs, ha.1, ha.2.1, ha.2.2]

theorem shape_no_other_writes (a : String)
    (ha : a ∉ ["ell.nextshape.s", "ell.nextshape.n", "ell.nextshape.d"]) : a ∉ updateShape.warrs := by
  simp at ha
  simp [updateShape, initializeShape, shapeLoop, shapeStep, shapeCoordinate, entryIndex, entryProduct,
    shapeDifference, roundedEntry, inflatedEntry, addDiagonal, RamZeroArray.zeroRationalArray,
    RamZeroArray.fillConstant, Lib.Fill.put, loadLeft, loadRight, storeReduced, multiplyFraction,
    RamFractionInterface.subtractFraction, RamFractionInterface.negateRight,
    RamFractionInterface.resultToRight, RamFractionInterface.resultToLeft,
    RamRounding.roundFraction, addFraction, RamArithmetic.normalizeFraction, RamArithmetic.gcdLoop,
    RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.warrs, ha.1, ha.2.1, ha.2.2]

def roundedUpdate : Com := .seq updateCenter updateShape

theorem roundedUpdate_spec (B n M D : ℕ) (u c : Fin n → ℚ) (A : Matrix (Fin n) (Fin n) ℚ)
    (gs : List ℚ) (hg : 4 < gs.length) (hM : 1 ≤ M) (hnM : n * n ≤ M)
    (hu : ∀ j, Height (u j) M) (hc : ∀ j, Height (c j) M) (hA : ∀ i j, Height (A i j) M)
    (hα : Height gs[0] M) (hβ : Height gs[1] M) (hγ : Height gs[2] M)
    (hρ : Height gs[3] M) (hδ : Height gs[4] M)
    (hD : D ≤ M) (hDpos : 0 < D) (hnB : n * n < B) (hnB' : n < B)
    (hCenterB : 2 * (centerCap M) ^ 2 + 3 < B) (hShapeB : 2 * (shapeCap M) ^ 2 + 3 < B) :
    Spec B (fun σ => Represents "ell.u" (List.ofFn u) σ ∧ Represents "ell.center" (List.ofFn c) σ ∧
        Represents "ell.shape" (flatten A) σ ∧ Represents "ell.coeff" gs σ ∧
        (σ.arrs "ell.nextcenter.s").length = n ∧ (σ.arrs "ell.nextcenter.n").length = n ∧
        (σ.arrs "ell.nextcenter.d").length = n ∧ (σ.arrs "ell.nextshape.s").length = n * n ∧
        (σ.arrs "ell.nextshape.n").length = n * n ∧ (σ.arrs "ell.nextshape.d").length = n * n ∧
        σ.vars "vec.n" = n ∧ σ.vars "grid.D" = D)
      roundedUpdate
      (fun _ τ => Represents "ell.nextcenter" (List.ofFn (centerValues u c gs[2] D)) τ ∧
        Represents "ell.nextshape" (flatten (shapeValues u A gs hg D)) τ ∧
        Represents "ell.u" (List.ofFn u) τ ∧ Represents "ell.center" (List.ofFn c) τ ∧
        Represents "ell.shape" (flatten A) τ ∧ Represents "ell.coeff" gs τ ∧
        τ.vars "vec.n" = n ∧ τ.vars "grid.D" = D)
      ((33 * n + 18 + ((180 * (centerCap M).size + 318 + 4 + 4) * n + 6)) +
        (33 * (n * n) + 26 + ((468 * (shapeCap M).size + 690 + 4 + 4) * (n * n) + 10))) := by
  rintro σ ⟨hσu, hσc, hσA, hσg, hσcs, hσcn, hσcd, hσAs, hσAn, hσAd, hσn, hσD⟩
  obtain ⟨τ, hr₁, hτnextc, hτu, hτc, hτg, hτn, hτD⟩ := updateCenter_spec B n M D u c gs
    (by omega) hM hu hc hγ hD hDpos hnB' hCenterB σ ⟨hσu, hσc, hσg, hσcs, hσcn, hσcd, hσn, hσD⟩
  have hτA : Represents "ell.shape" (flatten A) τ := represents_frame hr₁ "ell.shape" _ hσA
    (center_no_other_writes _ (by simp)) (center_no_other_writes _ (by simp)) (center_no_other_writes _ (by simp))
  have hτAs : (τ.arrs "ell.nextshape.s").length = n * n := by
    rw [hr₁.frame_arr _ (center_no_other_writes _ (by simp))]; exact hσAs
  have hτAn : (τ.arrs "ell.nextshape.n").length = n * n := by
    rw [hr₁.frame_arr _ (center_no_other_writes _ (by simp))]; exact hσAn
  have hτAd : (τ.arrs "ell.nextshape.d").length = n * n := by
    rw [hr₁.frame_arr _ (center_no_other_writes _ (by simp))]; exact hσAd
  obtain ⟨υ, hr₂, hυnextA, hυu, hυA, hυg, hυn, hυD⟩ := updateShape_spec B n M D u A gs hg hM hnM hu hA
    hα hβ hρ hδ hD hDpos hnB hnB' hShapeB τ ⟨hτu, hτA, hτg, hτAs, hτAn, hτAd, hτn, hτD⟩
  have hυnextc := represents_frame hr₂ "ell.nextcenter" _ hτnextc
    (shape_no_other_writes _ (by simp)) (shape_no_other_writes _ (by simp)) (shape_no_other_writes _ (by simp))
  have hυc := represents_frame hr₂ "ell.center" _ hτc
    (shape_no_other_writes _ (by simp)) (shape_no_other_writes _ (by simp)) (shape_no_other_writes _ (by simp))
  exact ⟨υ, hr₁.seq hr₂, hυnextc, hυnextA, hυu, hυc, hυA, hυg, hυn, hυD⟩

theorem roundedUpdate_cost_polynomial (n M : ℕ) :
    ((33 * n + 18 + ((180 * (centerCap M).size + 318 + 4 + 4) * n + 6)) +
      (33 * (n * n) + 26 + ((468 * (shapeCap M).size + 690 + 4 + 4) * (n * n) + 10))) ≤
      (720 * M.size + 1799) * n + (3744 * M.size + 6815) * (n * n) + 60 := by
  have h := Nat.add_le_add (updateCenter_cost_polynomial n M) (updateShape_cost_polynomial n M)
  convert h using 1 <;> ring

theorem roundedUpdate_eq_ellipsoid {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (a c : Fin n → ℚ) (D E : ℕ) :
    centerValues (A *ᵥ a) c ((coefficients n (a ⬝ᵥ (A *ᵥ a)) D E)[2]'(by simp [coefficients])) D =
        EllipsoidCenter.roundedCenter n A a c D ∧
      shapeValues (A *ᵥ a) A (coefficients n (a ⬝ᵥ (A *ᵥ a)) D E) (by simp [coefficients]) D =
        EllipsoidCenter.roundedStepShape n A a D (1 / (E : ℚ)) := by
  constructor
  · simpa [coefficients] using centerValues_eq_roundedCenter A a c D
  · exact shapeValues_eq_roundedStepShape A a _ (by simp [coefficients]) D (1 / (E : ℚ))
      (by simp [coefficients]) (by simp [coefficients]) (by simp [coefficients]) (by simp [coefficients])



theorem roundedUpdate_ellipsoid_spec (B n M D E : ℕ) (A : Matrix (Fin n) (Fin n) ℚ)
    (a c : Fin n → ℚ) (gs : List ℚ) (hg : 4 < gs.length) (hM : 1 ≤ M) (hnM : n * n ≤ M)
    (hu : ∀ j, Height ((A *ᵥ a) j) M) (hc : ∀ j, Height (c j) M) (hA : ∀ i j, Height (A i j) M)
    (hα : Height gs[0] M) (hβ : Height gs[1] M) (hγ : Height gs[2] M)
    (hρ : Height gs[3] M) (hδ : Height gs[4] M)
    (hD : D ≤ M) (hDpos : 0 < D) (hnB : n * n < B) (hnB' : n < B)
    (hCenterB : 2 * (centerCap M) ^ 2 + 3 < B) (hShapeB : 2 * (shapeCap M) ^ 2 + 3 < B)
    (hgs : gs = coefficients n (a ⬝ᵥ (A *ᵥ a)) D E) :
    Spec B (fun σ => Represents "ell.u" (List.ofFn (A *ᵥ a)) σ ∧ Represents "ell.center" (List.ofFn c) σ ∧
        Represents "ell.shape" (flatten A) σ ∧ Represents "ell.coeff" gs σ ∧
        (σ.arrs "ell.nextcenter.s").length = n ∧ (σ.arrs "ell.nextcenter.n").length = n ∧
        (σ.arrs "ell.nextcenter.d").length = n ∧ (σ.arrs "ell.nextshape.s").length = n * n ∧
        (σ.arrs "ell.nextshape.n").length = n * n ∧ (σ.arrs "ell.nextshape.d").length = n * n ∧
        σ.vars "vec.n" = n ∧ σ.vars "grid.D" = D)
      roundedUpdate
      (fun _ τ => Represents "ell.nextcenter" (List.ofFn (EllipsoidCenter.roundedCenter n A a c D)) τ ∧
        Represents "ell.nextshape" (flatten (EllipsoidCenter.roundedStepShape n A a D (1 / (E : ℚ)))) τ ∧
        Represents "ell.u" (List.ofFn (A *ᵥ a)) τ ∧ Represents "ell.center" (List.ofFn c) τ ∧
        Represents "ell.shape" (flatten A) τ ∧ Represents "ell.coeff" gs τ ∧
        τ.vars "vec.n" = n ∧ τ.vars "grid.D" = D)
      ((33 * n + 18 + ((180 * (centerCap M).size + 318 + 4 + 4) * n + 6)) +
        (33 * (n * n) + 26 + ((468 * (shapeCap M).size + 690 + 4 + 4) * (n * n) + 10))) := by
  have hp := roundedUpdate_spec B n M D (A *ᵥ a) c A gs hg hM hnM hu hc hA hα hβ hγ hρ hδ
    hD hDpos hnB hnB' hCenterB hShapeB
  subst gs
  have heq := roundedUpdate_eq_ellipsoid A a c D E
  exact hp.post (fun _ _ _ h => by simpa only [heq.1, heq.2] using h)

end Lax109476Proofs.RamEllipsoidUpdate

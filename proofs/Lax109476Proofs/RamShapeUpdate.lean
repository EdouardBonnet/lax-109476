import Lax109476Proofs.RamShapeCoordinate
import Lax109476Proofs.RamCenterUpdate

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamShapeUpdate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface RamFrame RationalArithmeticBounds
open RamShapeCoordinate RamZeroArray RamMatrixStorage

def shapeValues {n : ℕ} (u : Fin n → ℚ) (A : Matrix (Fin n) (Fin n) ℚ)
    (gs : List ℚ) (hg : 4 < gs.length) (D : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => gs[3] * (RationalRounding.roundDown
    (gs[0] * (A i j - gs[1] * (u i * u j))) D + if i = j then gs[4] else 0)

def entryValues {n : ℕ} (u : Fin n → ℚ) (A : Matrix (Fin n) (Fin n) ℚ)
    (gs : List ℚ) (hg : 4 < gs.length) (D : ℕ) : Fin (n * n) → ℚ :=
  fun k => shapeValues u A gs hg D k.divNat k.modNat

def ShapeInvariant {n : ℕ} (u : Fin n → ℚ) (A : Matrix (Fin n) (Fin n) ℚ)
    (gs : List ℚ) (D : ℕ) (hg : 4 < gs.length) (σ : Env) : Prop :=
  Represents "ell.u" (List.ofFn u) σ ∧ Represents "ell.shape" (flatten A) σ ∧
    Represents "ell.coeff" gs σ ∧
    Represents "ell.nextshape" (RamCenterUpdate.filled (entryValues u A gs hg D) (σ.vars "entry.k")) σ ∧
    σ.vars "entry.k" ≤ n * n ∧ σ.vars "entry.count" = n * n ∧
    σ.vars "vec.n" = n ∧ σ.vars "grid.D" = D

def shapeStep : Com := .seq shapeCoordinate (.assign "entry.k" (.add (.var "entry.k") (.lit 1)))

set_option maxRecDepth 4000 in
theorem shapeStep_spec (B n M D : ℕ) (u : Fin n → ℚ) (A : Matrix (Fin n) (Fin n) ℚ)
    (gs : List ℚ) (hg : 4 < gs.length) (hM : 1 ≤ M) (hnM : n * n ≤ M)
    (hu : ∀ j, Height (u j) M) (hA : ∀ i j, Height (A i j) M)
    (hα : Height gs[0] M) (hβ : Height gs[1] M) (hρ : Height gs[3] M) (hδ : Height gs[4] M)
    (hD : D ≤ M) (hDpos : 0 < D) (hnB : n * n < B)
    (hB : 2 * (shapeCap M) ^ 2 + 3 < B) :
    Spec B (fun σ => ShapeInvariant u A gs D hg σ ∧ σ.vars "entry.k" < n * n) shapeStep
      (fun σ τ => ShapeInvariant u A gs D hg τ ∧ τ.vars "entry.k" = σ.vars "entry.k" + 1)
      (468 * (shapeCap M).size + 690 + 4) := by
  rintro σ ⟨⟨hσu, hσA, hσg, hσnext, hσkN, hσcount, hσn, hσD⟩, hσk⟩
  let k : Fin (n * n) := ⟨σ.vars "entry.k", hσk⟩
  have hiu : k.val / n < (List.ofFn u).length := by simpa using k.divNat.isLt
  have hju : k.val % n < (List.ofFn u).length := by simpa using k.modNat.isLt
  have huk : Height (List.ofFn u)[k.val / n] M := by
    simpa [Fin.divNat] using hu k.divNat
  have hvk : Height (List.ofFn u)[k.val % n] M := by
    simpa [Fin.modNat] using hu k.modNat
  have hAk : Height (flatten A)[k.val] M := by simpa [flatten] using hA k.divNat k.modNat
  obtain ⟨τ, hr₁, hτnext, hτu, hτA, hτg⟩ := shapeCoordinate_spec B M D n k.val
    (List.ofFn u) (flatten A) gs (RamCenterUpdate.filled (entryValues u A gs hg D) k.val)
    k.isLt hnM (by simp) (by simpa using k.divNat.isLt) (by simpa using k.modNat.isLt) (by simp [flatten]) hg (by simp [RamCenterUpdate.filled])
    hM hD hDpos huk hvk hAk hα hβ hρ hδ hB
    σ ⟨hσu, hσA, hσg, hσnext, rfl, hσn, hσD⟩
  have hfields : FieldsAgree ["entry.k", "entry.count", "vec.n", "grid.D"] σ τ := by
    intro x hx
    apply hr₁.frame_var
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl
    all_goals simp [shapeCoordinate, entryProduct, shapeDifference, roundedEntry, inflatedEntry, entryIndex, addDiagonal, loadLeft, loadRight, storeReduced,
      multiplyFraction, subtractFraction, negateRight, resultToRight, resultToLeft,
      RamRounding.roundFraction, addFraction, RamArithmetic.normalizeFraction,
      RamArithmetic.gcdLoop, RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.wvars]
  have hτk : τ.vars "entry.k" = k.val := hfields _ (by simp)
  have hτcount : τ.vars "entry.count" = n * n := (hfields _ (by simp)).trans hσcount
  have hτn : τ.vars "vec.n" = n := (hfields _ (by simp)).trans hσn
  have hτD : τ.vars "grid.D" = D := (hfields _ (by simp)).trans hσD
  have h1 : 1 < B := by nlinarith
  have hkB : k.val < B := k.isLt.trans hnB
  have hk1B : k.val + 1 < B := lt_of_le_of_lt k.isLt hnB
  have hτkB : τ.vars "entry.k" < B := hτk ▸ hkB
  have hsumB : Bop.add.apply (τ.vars "entry.k") 1 < B := by simpa [Bop.apply, hτk] using hk1B
  have hr₂ : Run B (.assign "entry.k" (.add (.var "entry.k") (.lit 1))) τ
      (τ.setVar "entry.k" (k.val + 1)) 4 := by
    exact Run.assign (by simpa [Bop.apply, hτk] using
      (evalB_bin (evalB_var hτkB) (evalB_lit h1) hsumB))
  have hnext : Represents "ell.nextshape"
      (RamCenterUpdate.filled (entryValues u A gs hg D) (k.val + 1)) τ := by
    rw [← RamCenterUpdate.filled_step]
    simpa only [entryValues, shapeValues, flatten, List.getElem_ofFn, Fin.eta,
      Fin.divNat, Fin.modNat, Fin.ext_iff] using hτnext
  refine ⟨_, hr₁.seq hr₂, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Represents, arrs_setVar] using hτu
  · simpa only [Represents, arrs_setVar] using hτA
  · simpa only [Represents, arrs_setVar] using hτg
  · simpa only [Represents, arrs_setVar, vars_setVar, ite_true] using hnext
  · change k.val + 1 ≤ n * n
    exact k.isLt
  · simpa using hτcount
  · simpa using hτn
  · simpa using hτD
  · simp [k]

def shapeLoop : Com :=
  .seq (.assign "entry.count" (.mul (.var "vec.n") (.var "vec.n")))
    (.seq (.assign "entry.k" (.lit 0)) (.while (.lt (.var "entry.k") (.var "entry.count")) shapeStep))

theorem shapeLoop_spec (B n M D : ℕ) (u : Fin n → ℚ) (A : Matrix (Fin n) (Fin n) ℚ)
    (gs : List ℚ) (hg : 4 < gs.length) (hM : 1 ≤ M) (hnM : n * n ≤ M)
    (hu : ∀ j, Height (u j) M) (hA : ∀ i j, Height (A i j) M)
    (hα : Height gs[0] M) (hβ : Height gs[1] M) (hρ : Height gs[3] M) (hδ : Height gs[4] M)
    (hD : D ≤ M) (hDpos : 0 < D) (hnB : n * n < B) (hnB' : n < B)
    (hB : 2 * (shapeCap M) ^ 2 + 3 < B) :
    Spec B (fun σ => Represents "ell.u" (List.ofFn u) σ ∧ Represents "ell.shape" (flatten A) σ ∧
        Represents "ell.coeff" gs σ ∧ Represents "ell.nextshape" (List.replicate (n * n) 0) σ ∧
        σ.vars "vec.n" = n ∧ σ.vars "grid.D" = D)
      shapeLoop
      (fun _ τ => Represents "ell.nextshape" (flatten (shapeValues u A gs hg D)) τ ∧
        Represents "ell.u" (List.ofFn u) τ ∧ Represents "ell.shape" (flatten A) τ ∧
        Represents "ell.coeff" gs τ ∧ τ.vars "vec.n" = n ∧ τ.vars "grid.D" = D)
      ((468 * (shapeCap M).size + 690 + 4 + 4) * (n * n) + 10) := by
  have hlo := Spec.forRangeZero "entry.k" "entry.count" (ShapeInvariant u A gs D hg) (n * n)
    (468 * (shapeCap M).size + 690 + 4) hnB
    (fun _ h => h.2.2.2.2.1) (fun _ h => h.2.2.2.2.2.1)
    (shapeStep_spec B n M D u A gs hg hM hnM hu hA hα hβ hρ hδ hD hDpos hnB hB)
  have hloop : Spec B (fun σ => Represents "ell.u" (List.ofFn u) σ ∧ Represents "ell.shape" (flatten A) σ ∧
      Represents "ell.coeff" gs σ ∧ Represents "ell.nextshape" (List.replicate (n * n) 0) σ ∧
      σ.vars "entry.count" = n * n ∧ σ.vars "vec.n" = n ∧ σ.vars "grid.D" = D)
      (.seq (.assign "entry.k" (.lit 0)) (.while (.lt (.var "entry.k") (.var "entry.count")) shapeStep))
      (fun _ τ => Represents "ell.nextshape" (flatten (shapeValues u A gs hg D)) τ ∧
        Represents "ell.u" (List.ofFn u) τ ∧ Represents "ell.shape" (flatten A) τ ∧
        Represents "ell.coeff" gs τ ∧ τ.vars "vec.n" = n ∧ τ.vars "grid.D" = D)
      ((468 * (shapeCap M).size + 690 + 4 + 4) * (n * n) + 6) := by
    refine (hlo.pre ?_).post ?_
    · rintro σ ⟨hσu, hσA, hσg, hσnext, hσcount, hσn, hσD⟩
      simp_all [ShapeInvariant, Represents, RamCenterUpdate.filled_zero]
    · rintro σ τ _ ⟨hτ, hcounter⟩
      refine ⟨?_, hτ.1, hτ.2.1, hτ.2.2.1, hτ.2.2.2.2.2.2.1, hτ.2.2.2.2.2.2.2⟩
      change Represents "ell.nextshape" (List.ofFn (entryValues u A gs hg D)) τ
      simpa only [hcounter, RamCenterUpdate.filled_done] using hτ.2.2.2.1
  rintro σ ⟨hσu, hσA, hσg, hσnext, hσn, hσD⟩
  run_vcg [hloop]
  all_goals clear hloop hlo
  all_goals simp_all [Represents]



def initializeShape : Com :=
  .seq (.assign "shape.savedn" (.var "vec.n"))
    (.seq (.assign "vec.n" (.mul (.var "vec.n") (.var "vec.n")))
      (.seq (zeroRationalArray "ell.nextshape") (.assign "vec.n" (.var "shape.savedn"))))

theorem initializeShape_spec (B n : ℕ) (hnB : n < B) (hnnB : n * n < B) (h1 : 1 < B) :
    Spec B (fun σ => (σ.arrs "ell.nextshape.s").length = n * n ∧
        (σ.arrs "ell.nextshape.n").length = n * n ∧ (σ.arrs "ell.nextshape.d").length = n * n ∧
        σ.vars "vec.n" = n)
      initializeShape
      (fun σ τ => Represents "ell.nextshape" (List.replicate (n * n) 0) τ ∧
        τ.vars "vec.n" = n ∧ τ.vars "grid.D" = σ.vars "grid.D" ∧
        ∀ a ∉ ["ell.nextshape.s", "ell.nextshape.n", "ell.nextshape.d"], τ.arrs a = σ.arrs a)
      (33 * (n * n) + 26) := by
  have hzero := spec_with_write_frame ["shape.savedn", "grid.D"]
    (zeroRationalArray_spec B (n * n) "ell.nextshape" hnnB h1)
    (by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl
      all_goals simp [zeroRationalArray, fillConstant, Lib.Fill.put, Com.wvars])
  rintro σ ⟨hσs, hσnum, hσd, hσn⟩
  run_vcg [hzero]
  all_goals clear hzero
  all_goals simp_all [Represents, FieldsAgree]

def updateShape : Com := .seq initializeShape shapeLoop

theorem updateShape_spec (B n M D : ℕ) (u : Fin n → ℚ) (A : Matrix (Fin n) (Fin n) ℚ)
    (gs : List ℚ) (hg : 4 < gs.length) (hM : 1 ≤ M) (hnM : n * n ≤ M)
    (hu : ∀ j, Height (u j) M) (hA : ∀ i j, Height (A i j) M)
    (hα : Height gs[0] M) (hβ : Height gs[1] M) (hρ : Height gs[3] M) (hδ : Height gs[4] M)
    (hD : D ≤ M) (hDpos : 0 < D) (hnB : n * n < B) (hnB' : n < B)
    (hB : 2 * (shapeCap M) ^ 2 + 3 < B) :
    Spec B (fun σ => Represents "ell.u" (List.ofFn u) σ ∧ Represents "ell.shape" (flatten A) σ ∧
        Represents "ell.coeff" gs σ ∧ (σ.arrs "ell.nextshape.s").length = n * n ∧
        (σ.arrs "ell.nextshape.n").length = n * n ∧ (σ.arrs "ell.nextshape.d").length = n * n ∧
        σ.vars "vec.n" = n ∧ σ.vars "grid.D" = D)
      updateShape
      (fun _ τ => Represents "ell.nextshape" (flatten (shapeValues u A gs hg D)) τ ∧
        Represents "ell.u" (List.ofFn u) τ ∧ Represents "ell.shape" (flatten A) τ ∧
        Represents "ell.coeff" gs τ ∧ τ.vars "vec.n" = n ∧ τ.vars "grid.D" = D)
      (33 * (n * n) + 26 + ((468 * (shapeCap M).size + 690 + 4 + 4) * (n * n) + 10)) := by
  have h1 : 1 < B := by nlinarith
  rintro σ ⟨hσu, hσA, hσg, hσs, hσnum, hσd, hσn, hσD⟩
  obtain ⟨τ, hr₁, hτnext, hτn, hτD, hτarr⟩ := initializeShape_spec B n hnB' hnB h1
    σ ⟨hσs, hσnum, hσd, hσn⟩
  have hτu : Represents "ell.u" (List.ofFn u) τ := by
    simpa only [Represents, hτarr ("ell.u" ++ ".s") (by simp),
      hτarr ("ell.u" ++ ".n") (by simp), hτarr ("ell.u" ++ ".d") (by simp)] using hσu
  have hτA : Represents "ell.shape" (flatten A) τ := by
    simpa only [Represents, hτarr ("ell.shape" ++ ".s") (by simp),
      hτarr ("ell.shape" ++ ".n") (by simp), hτarr ("ell.shape" ++ ".d") (by simp)] using hσA
  have hτg : Represents "ell.coeff" gs τ := by
    simpa only [Represents, hτarr ("ell.coeff" ++ ".s") (by simp),
      hτarr ("ell.coeff" ++ ".n") (by simp), hτarr ("ell.coeff" ++ ".d") (by simp)] using hσg
  obtain ⟨υ, hr₂, hυ⟩ := shapeLoop_spec B n M D u A gs hg hM hnM hu hA hα hβ hρ hδ
    hD hDpos hnB hnB' hB τ ⟨hτu, hτA, hτg, hτnext, hτn, hτD.trans hσD⟩
  exact ⟨υ, hr₁.seq hr₂, hυ⟩

theorem shapeCap_size (M : ℕ) : (shapeCap M).size ≤ 8 * M.size + 13 := by
  have hb := RationalSizeBounds.size_add_one_le M
  have hp := RationalSizeBounds.size_pow_le (M + 1) 8
  have hm := RationalSizeBounds.size_mul_le 8 ((M + 1) ^ 8)
  have h8 : Nat.size 8 = 4 := by decide
  unfold shapeCap
  omega

theorem updateShape_cost_polynomial (n M : ℕ) :
    33 * (n * n) + 26 + ((468 * (shapeCap M).size + 690 + 4 + 4) * (n * n) + 10) ≤
      (3744 * M.size + 6815) * (n * n) + 36 := by
  have hm := Nat.mul_le_mul_left 468 (shapeCap_size M)
  have hn := Nat.mul_le_mul_right (n * n) (Nat.add_le_add_right hm 731)
  convert Nat.add_le_add_right hn 36 using 1 <;> ring

theorem shapeValues_eq_roundedStepShape {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (a : Fin n → ℚ) (gs : List ℚ) (hg : 4 < gs.length) (D : ℕ) (η : ℚ)
    (hα : gs[0] = (n : ℚ) ^ 2 / ((n : ℚ) ^ 2 - 1))
    (hβ : gs[1] = 2 / (((n : ℚ) + 1) * (a ⬝ᵥ (A *ᵥ a))))
    (hρ : gs[3] = (1 + η) ^ 2) (hδ : gs[4] = (n : ℚ) / D) :
    shapeValues (A *ᵥ a) A gs hg D = EllipsoidCenter.roundedStepShape n A a D η := by
  ext i j
  simp only [shapeValues, hα, hβ, hρ, hδ, EllipsoidCenter.roundedStepShape,
    EllipsoidRounding.roundedShape, EllipsoidBounds.cutShape, Matrix.smul_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]



theorem updateShape_ellipsoid_spec (B n M D : ℕ) (A : Matrix (Fin n) (Fin n) ℚ)
    (a : Fin n → ℚ) (gs : List ℚ) (hg : 4 < gs.length) (η : ℚ)
    (hM : 1 ≤ M) (hnM : n * n ≤ M) (hu : ∀ j, Height ((A *ᵥ a) j) M)
    (hA : ∀ i j, Height (A i j) M)
    (hα : Height gs[0] M) (hβ : Height gs[1] M) (hρ : Height gs[3] M) (hδ : Height gs[4] M)
    (hD : D ≤ M) (hDpos : 0 < D) (hnB : n * n < B) (hnB' : n < B)
    (hB : 2 * (shapeCap M) ^ 2 + 3 < B)
    (hαValue : gs[0] = (n : ℚ) ^ 2 / ((n : ℚ) ^ 2 - 1))
    (hβValue : gs[1] = 2 / (((n : ℚ) + 1) * (a ⬝ᵥ (A *ᵥ a))))
    (hρValue : gs[3] = (1 + η) ^ 2) (hδValue : gs[4] = (n : ℚ) / D) :
    Spec B (fun σ => Represents "ell.u" (List.ofFn (A *ᵥ a)) σ ∧ Represents "ell.shape" (flatten A) σ ∧
        Represents "ell.coeff" gs σ ∧ (σ.arrs "ell.nextshape.s").length = n * n ∧
        (σ.arrs "ell.nextshape.n").length = n * n ∧ (σ.arrs "ell.nextshape.d").length = n * n ∧
        σ.vars "vec.n" = n ∧ σ.vars "grid.D" = D)
      updateShape
      (fun _ τ => Represents "ell.nextshape" (flatten (EllipsoidCenter.roundedStepShape n A a D η)) τ ∧
        Represents "ell.u" (List.ofFn (A *ᵥ a)) τ ∧ Represents "ell.shape" (flatten A) τ ∧
        Represents "ell.coeff" gs τ ∧ τ.vars "vec.n" = n ∧ τ.vars "grid.D" = D)
      (33 * (n * n) + 26 + ((468 * (shapeCap M).size + 690 + 4 + 4) * (n * n) + 10)) := by
  have hv := shapeValues_eq_roundedStepShape A a gs hg D η hαValue hβValue hρValue hδValue
  exact (updateShape_spec B n M D (A *ᵥ a) A gs hg hM hnM hu hA hα hβ hρ hδ hD hDpos hnB hnB' hB).post
    (fun _ _ _ h => by simpa only [hv] using h)

end Lax109476Proofs.RamShapeUpdate

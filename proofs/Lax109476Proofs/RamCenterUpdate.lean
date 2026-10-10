import Lax109476Proofs.RamCenterCoordinate
import Lax109476Proofs.RamZeroArray
import Lax109476Proofs.EllipsoidCenter

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamCenterUpdate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface RamFrame RationalArithmeticBounds
open RamCenterCoordinate RamZeroArray

/-- Stored-coordinate values, with the already computed rational step factor. -/
def centerValues {n : ℕ} (u c : Fin n → ℚ) (gamma : ℚ) (D : ℕ) : Fin n → ℚ :=
  fun j => RationalRounding.roundDown (c j - u j * gamma) D

def filled {n : ℕ} (v : Fin n → ℚ) (k : ℕ) : List ℚ :=
  List.ofFn (fun j => if j.val < k then v j else 0)

theorem filled_zero {n : ℕ} (v : Fin n → ℚ) : filled v 0 = List.replicate n 0 := by simp [filled]

theorem filled_done {n : ℕ} (v : Fin n → ℚ) : filled v n = List.ofFn v := by
  unfold filled
  congr 1
  funext j
  simp [j.isLt]

theorem filled_step {n : ℕ} (v : Fin n → ℚ) (i : Fin n) :
    (filled v i.val).set i.val (v i) = filled v (i.val + 1) := by
  apply List.ext_getElem
  · simp [filled]
  · intro k hk hk'
    have hkn : k < n := by simpa [filled] using hk'
    rw [List.getElem_set]
    by_cases hki : i.val = k
    · have hfin : i = (⟨k, hkn⟩ : Fin n) := Fin.ext hki
      simp [filled, hfin]
    · have hnext : k < i.val + 1 ↔ k < i.val := by omega
      simp only [hki, ↓reduceIte, filled, List.getElem_ofFn]
      change (if k < i.val then v ⟨k, hkn⟩ else 0) = (if k < i.val + 1 then v ⟨k, hkn⟩ else 0)
      simp only [hnext]

def CenterInvariant {n : ℕ} (u c : Fin n → ℚ) (gs : List ℚ) (D : ℕ) (hg : 2 < gs.length)
    (σ : Env) : Prop :=
  Represents "ell.u" (List.ofFn u) σ ∧ Represents "ell.center" (List.ofFn c) σ ∧
    Represents "ell.coeff" gs σ ∧
    Represents "ell.nextcenter" (filled (centerValues u c gs[2] D) (σ.vars "center.i")) σ ∧
    σ.vars "center.i" ≤ n ∧ σ.vars "vec.n" = n ∧ σ.vars "grid.D" = D

def centerStep : Com := .seq centerCoordinate (.assign "center.i" (.add (.var "center.i") (.lit 1)))

theorem centerStep_spec (B n M D : ℕ) (u c : Fin n → ℚ) (gs : List ℚ)
    (hg : 2 < gs.length) (hM : 1 ≤ M) (hu : ∀ j, Height (u j) M) (hc : ∀ j, Height (c j) M)
    (hgamma : Height gs[2] M) (hD : D ≤ M) (hDpos : 0 < D)
    (hnB : n < B) (hB : 2 * (centerCap M) ^ 2 + 3 < B) :
    Spec B (fun σ => CenterInvariant u c gs D hg σ ∧ σ.vars "center.i" < n) centerStep
      (fun σ τ => CenterInvariant u c gs D hg τ ∧ τ.vars "center.i" = σ.vars "center.i" + 1)
      (180 * (centerCap M).size + 318 + 4) := by
  rintro σ ⟨⟨hσu, hσc, hσg, hσnext, hσin, hσn, hσD⟩, hσi⟩
  let i : Fin n := ⟨σ.vars "center.i", hσi⟩
  have hui : Height (List.ofFn u)[i.val] M := by simpa using hu i
  have hci : Height (List.ofFn c)[i.val] M := by simpa using hc i
  obtain ⟨τ, hr₁, hτnext, hτu, hτc, hτg⟩ := centerCoordinate_spec B M D i.val
    (List.ofFn u) (List.ofFn c) gs (filled (centerValues u c gs[2] D) i.val)
    (by simp) (by simp) hg (by simp [filled]) (hσi.trans hnB) hM hD hDpos hui hci hgamma hB
    σ ⟨hσu, hσc, hσg, hσnext, rfl, hσD⟩
  have hfields : FieldsAgree ["center.i", "vec.n", "grid.D"] σ τ := by
    intro x hx
    apply hr₁.frame_var
    simp at hx
    rcases hx with rfl | rfl | rfl
    all_goals simp [centerCoordinate, loadLeft, loadRight, storeReduced, multiplyFraction, subtractFraction,
      negateRight, resultToRight, resultToLeft, RamRounding.roundFraction, addFraction,
      RamArithmetic.normalizeFraction, RamArithmetic.gcdLoop, RamArithmetic.gcdDoubleStep,
      RamArithmetic.gcdStep, Com.wvars]
  have hτi : τ.vars "center.i" = i.val := hfields _ (by simp)
  have hτn : τ.vars "vec.n" = n := (hfields _ (by simp)).trans hσn
  have hτD : τ.vars "grid.D" = D := (hfields _ (by simp)).trans hσD
  have h1 : 1 < B := by nlinarith
  have hiB : i.val < B := hσi.trans hnB
  have hi1B : i.val + 1 < B := lt_of_le_of_lt i.isLt hnB
  have hτiB : τ.vars "center.i" < B := hτi ▸ hiB
  have hsumB : Bop.add.apply (τ.vars "center.i") 1 < B := by simpa [Bop.apply, hτi] using hi1B
  have hr₂ : Run B (.assign "center.i" (.add (.var "center.i") (.lit 1))) τ
      (τ.setVar "center.i" (i.val + 1)) 4 := by
    exact Run.assign (by simpa [Bop.apply, hτi] using
      (evalB_bin (evalB_var hτiB) (evalB_lit h1) hsumB))
  have hnext : Represents "ell.nextcenter" (filled (centerValues u c gs[2] D) (i.val + 1)) τ := by
    rw [← filled_step]
    simpa only [centerValues, List.getElem_ofFn, Fin.eta] using hτnext
  refine ⟨_, hr₁.seq hr₂, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Represents, arrs_setVar] using hτu
  · simpa only [Represents, arrs_setVar] using hτc
  · simpa only [Represents, arrs_setVar] using hτg
  · simpa only [Represents, arrs_setVar, vars_setVar, ite_true] using hnext
  · change i.val + 1 ≤ n
    exact i.isLt
  · simpa using hτn
  · simpa using hτD
  · simp [i]

def centerLoop : Com :=
  .seq (.assign "center.i" (.lit 0)) (.while (.lt (.var "center.i") (.var "vec.n")) centerStep)

def updateCenter : Com := .seq (zeroRationalArray "ell.nextcenter") centerLoop

theorem centerLoop_spec (B n M D : ℕ) (u c : Fin n → ℚ) (gs : List ℚ)
    (hg : 2 < gs.length) (hM : 1 ≤ M) (hu : ∀ j, Height (u j) M) (hc : ∀ j, Height (c j) M)
    (hgamma : Height gs[2] M) (hD : D ≤ M) (hDpos : 0 < D)
    (hnB : n < B) (hB : 2 * (centerCap M) ^ 2 + 3 < B) :
    Spec B (fun σ => Represents "ell.u" (List.ofFn u) σ ∧ Represents "ell.center" (List.ofFn c) σ ∧
        Represents "ell.coeff" gs σ ∧ Represents "ell.nextcenter" (List.replicate n 0) σ ∧
        σ.vars "vec.n" = n ∧ σ.vars "grid.D" = D)
      centerLoop
      (fun _ τ => Represents "ell.nextcenter" (List.ofFn (centerValues u c gs[2] D)) τ ∧
        Represents "ell.u" (List.ofFn u) τ ∧ Represents "ell.center" (List.ofFn c) τ ∧
        Represents "ell.coeff" gs τ ∧ τ.vars "vec.n" = n ∧ τ.vars "grid.D" = D)
      ((180 * (centerCap M).size + 318 + 4 + 4) * n + 6) := by
  have hlo := Spec.forRangeZero "center.i" "vec.n" (CenterInvariant u c gs D hg) n
    (180 * (centerCap M).size + 318 + 4) hnB
    (fun _ h => h.2.2.2.2.1) (fun _ h => h.2.2.2.2.2.1)
    (centerStep_spec B n M D u c gs hg hM hu hc hgamma hD hDpos hnB hB)
  refine (hlo.pre ?_).post ?_
  · rintro σ ⟨hσu, hσc, hσg, hσnext, hσn, hσD⟩
    simp_all [CenterInvariant, Represents, filled_zero]
  · rintro σ τ _ ⟨hτ, hcounter⟩
    refine ⟨?_, hτ.1, hτ.2.1, hτ.2.2.1, hτ.2.2.2.2.2.1, hτ.2.2.2.2.2.2⟩
    simpa only [hcounter, filled_done] using hτ.2.2.2.1

theorem updateCenter_spec (B n M D : ℕ) (u c : Fin n → ℚ) (gs : List ℚ)
    (hg : 2 < gs.length) (hM : 1 ≤ M) (hu : ∀ j, Height (u j) M) (hc : ∀ j, Height (c j) M)
    (hgamma : Height gs[2] M) (hD : D ≤ M) (hDpos : 0 < D)
    (hnB : n < B) (hB : 2 * (centerCap M) ^ 2 + 3 < B) :
    Spec B (fun σ => Represents "ell.u" (List.ofFn u) σ ∧ Represents "ell.center" (List.ofFn c) σ ∧
        Represents "ell.coeff" gs σ ∧ (σ.arrs "ell.nextcenter.s").length = n ∧
        (σ.arrs "ell.nextcenter.n").length = n ∧ (σ.arrs "ell.nextcenter.d").length = n ∧
        σ.vars "vec.n" = n ∧ σ.vars "grid.D" = D)
      updateCenter
      (fun _ τ => Represents "ell.nextcenter" (List.ofFn (centerValues u c gs[2] D)) τ ∧
        Represents "ell.u" (List.ofFn u) τ ∧ Represents "ell.center" (List.ofFn c) τ ∧
        Represents "ell.coeff" gs τ ∧ τ.vars "vec.n" = n ∧ τ.vars "grid.D" = D)
      (33 * n + 18 + ((180 * (centerCap M).size + 318 + 4 + 4) * n + 6)) := by
  have h1 : 1 < B := by nlinarith
  rintro σ ⟨hσu, hσc, hσg, hσs, hσN, hσd, hσn, hσD⟩
  obtain ⟨τ, hr₁, hτnext, hτn, hτa⟩ := zeroRationalArray_spec B n "ell.nextcenter" hnB h1
    σ ⟨hσs, hσN, hσd, hσn⟩
  have hτu : Represents "ell.u" (List.ofFn u) τ := by
    simpa only [Represents, hτa ("ell.u" ++ ".s") (by decide), hτa ("ell.u" ++ ".n") (by decide),
      hτa ("ell.u" ++ ".d") (by decide)] using hσu
  have hτc : Represents "ell.center" (List.ofFn c) τ := by
    simpa only [Represents, hτa ("ell.center" ++ ".s") (by decide), hτa ("ell.center" ++ ".n") (by decide),
      hτa ("ell.center" ++ ".d") (by decide)] using hσc
  have hτg : Represents "ell.coeff" gs τ := by
    simpa only [Represents, hτa ("ell.coeff" ++ ".s") (by decide), hτa ("ell.coeff" ++ ".n") (by decide),
      hτa ("ell.coeff" ++ ".d") (by decide)] using hσg
  have hτD : τ.vars "grid.D" = D :=
    (hr₁.frame_var "grid.D" (by simp [zeroRationalArray, fillConstant, Lib.Fill.put, Com.wvars])).trans hσD
  obtain ⟨υ, hr₂, hυ⟩ := centerLoop_spec B n M D u c gs hg hM hu hc hgamma hD hDpos hnB hB
    τ ⟨hτu, hτc, hτg, hτnext, hτn, hτD⟩
  exact ⟨υ, hr₁.seq hr₂, hυ⟩

theorem centerCap_size (M : ℕ) : (centerCap M).size ≤ 4 * M.size + 8 := by
  have hb := RationalSizeBounds.size_add_one_le M
  have hp := RationalSizeBounds.size_pow_le (M + 1) 4
  have hm := RationalSizeBounds.size_mul_le 2 ((M + 1) ^ 4)
  have ha := RationalSizeBounds.size_add_one_le (2 * (M + 1) ^ 4)
  have htwo : Nat.size 2 = 2 := by decide
  unfold centerCap
  omega

theorem updateCenter_cost_polynomial (n M : ℕ) :
    33 * n + 18 + ((180 * (centerCap M).size + 318 + 4 + 4) * n + 6) ≤
      (720 * M.size + 1799) * n + 24 := by
  have hm := Nat.mul_le_mul_left 180 (centerCap_size M)
  have hn := Nat.mul_le_mul_right n (Nat.add_le_add_right hm 359)
  convert Nat.add_le_add_right hn 24 using 1 <;> ring

theorem centerValues_eq_roundedCenter {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (a c : Fin n → ℚ) (D : ℕ) :
    centerValues (A *ᵥ a) c (1 / (((n : ℚ) + 1) * RationalRounding.sqrtUpper (a ⬝ᵥ (A *ᵥ a)) D)) D =
      EllipsoidCenter.roundedCenter n A a c D := by
  funext i
  simp only [centerValues, EllipsoidCenter.roundedCenter, EllipsoidCenter.approximateCenter,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [mul_comm]

theorem updateCenter_ellipsoid_spec (B n M D : ℕ) (A : Matrix (Fin n) (Fin n) ℚ)
    (a c : Fin n → ℚ) (gs : List ℚ) (hg : 2 < gs.length) (hM : 1 ≤ M)
    (hu : ∀ j, Height ((A *ᵥ a) j) M) (hc : ∀ j, Height (c j) M)
    (hgamma : Height gs[2] M)
    (hgeq : gs[2] = 1 / (((n : ℚ) + 1) * RationalRounding.sqrtUpper (a ⬝ᵥ (A *ᵥ a)) D))
    (hD : D ≤ M) (hDpos : 0 < D) (hnB : n < B) (hB : 2 * (centerCap M) ^ 2 + 3 < B) :
    Spec B (fun σ => Represents "ell.u" (List.ofFn (A *ᵥ a)) σ ∧ Represents "ell.center" (List.ofFn c) σ ∧
        Represents "ell.coeff" gs σ ∧ (σ.arrs "ell.nextcenter.s").length = n ∧
        (σ.arrs "ell.nextcenter.n").length = n ∧ (σ.arrs "ell.nextcenter.d").length = n ∧
        σ.vars "vec.n" = n ∧ σ.vars "grid.D" = D)
      updateCenter
      (fun _ τ => Represents "ell.nextcenter" (List.ofFn (EllipsoidCenter.roundedCenter n A a c D)) τ ∧
        Represents "ell.u" (List.ofFn (A *ᵥ a)) τ ∧ Represents "ell.center" (List.ofFn c) τ ∧
        Represents "ell.coeff" gs τ ∧ τ.vars "vec.n" = n ∧ τ.vars "grid.D" = D)
      (33 * n + 18 + ((180 * (centerCap M).size + 318 + 4 + 4) * n + 6)) := by
  apply (updateCenter_spec B n M D (A *ᵥ a) c gs hg hM hu hc hgamma hD hDpos hnB hB).post
  rintro σ τ _ ⟨hnext, hu', hc', hg', hn', hD'⟩
  refine ⟨?_, hu', hc', hg', hn', hD'⟩
  rw [hgeq, centerValues_eq_roundedCenter] at hnext
  exact hnext

end Lax109476Proofs.RamCenterUpdate

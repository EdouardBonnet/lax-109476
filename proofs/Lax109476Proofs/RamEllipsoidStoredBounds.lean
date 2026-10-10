import Lax109476Proofs.RamEllipsoidStep

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamEllipsoidStoredBounds

open RationalArithmeticBounds RamCenterCoordinate RamCenterUpdate RamShapeCoordinate RamShapeUpdate
open RamEllipsoidCoefficients RamEllipsoidWordBounds

theorem centerValues_height {n : ℕ} (M D : ℕ) (u c : Fin n → ℚ) (γ : ℚ)
    (hM : 1 ≤ M) (hD : D ≤ M) (hDpos : 0 < D)
    (hu : ∀ i, Height (u i) M) (hc : ∀ i, Height (c i) M) (hγ : Height γ M) :
    ∀ i, Height (centerValues u c γ D i) (centerCap M) := by
  intro i
  have hp : Height (u i * γ) (M ^ 2) := by simpa [pow_two] using height_mul _ _ M M (hu i) hγ
  have hd : Height (c i - u i * γ) (2 * M ^ 3) := by
    have h := height_sub _ _ M (M ^ 2) (hc i) hp
    convert h using 1
    ring
  have hr := EllipsoidArithmeticBounds.height_roundDown _ (2 * M ^ 3) D hd hDpos
  apply height_mono _ hr
  calc
    2 * M ^ 3 * D + 1 ≤ 2 * M ^ 3 * M + 1 := Nat.add_le_add_right (Nat.mul_le_mul_left _ hD) 1
    _ = 2 * M ^ 4 + 1 := by ring
    _ ≤ centerCap M := (centerCap_bounds M hM).2.2.2

set_option maxHeartbeats 500000 in
theorem shapeValues_height {n : ℕ} (M D : ℕ) (u : Fin n → ℚ)
    (A : Matrix (Fin n) (Fin n) ℚ) (gs : List ℚ) (hg : 4 < gs.length)
    (hM : 1 ≤ M) (hD : D ≤ M) (hDpos : 0 < D)
    (hu : ∀ i, Height (u i) M) (hA : ∀ i j, Height (A i j) M)
    (hα : Height gs[0] M) (hβ : Height gs[1] M) (hρ : Height gs[3] M) (hδ : Height gs[4] M) :
    ∀ i j, Height (shapeValues u A gs hg D i j) (shapeCap M) := by
  intro i j
  let p := u i * u j
  let t := gs[1] * p
  let d := A i j - t
  let r := RationalRounding.roundDown (gs[0] * d) D
  have hp : Height p (M ^ 2) := by simpa [p, pow_two] using height_mul _ _ M M (hu i) (hu j)
  have ht : Height t (M ^ 3) := by
    have h := height_mul _ _ M (M ^ 2) hβ hp
    convert h using 1
    ring
  have hd : Height d (2 * M ^ 4) := by
    have h := height_sub _ _ M (M ^ 3) (hA i j) ht
    convert h using 1
    ring
  have ha : Height (gs[0] * d) (2 * M ^ 5) := by
    have h := height_mul _ _ M (2 * M ^ 4) hα hd
    convert h using 1
    ring
  have hr : Height r (2 * M ^ 6 + 1) := by
    apply height_mono _ (EllipsoidArithmeticBounds.height_roundDown _ (2 * M ^ 5) D ha hDpos)
    calc
      2 * M ^ 5 * D + 1 ≤ 2 * M ^ 5 * M + 1 := Nat.add_le_add_right (Nat.mul_le_mul_left _ hD) 1
      _ = 2 * M ^ 6 + 1 := by ring
  have hsum : Height (r + if i = j then gs[4] else 0) (6 * M ^ 7) := by
    by_cases hij : i = j
    · simp only [if_pos hij]
      apply height_mono _ (height_add _ _ (2 * M ^ 6 + 1) M hr hδ)
      have hpM : M ≤ M ^ 7 := le_self_pow hM (by decide : (7 : ℕ) ≠ 0)
      calc
        2 * (2 * M ^ 6 + 1) * M = 4 * M ^ 7 + 2 * M := by ring
        _ ≤ 6 * M ^ 7 := by omega
    · simp only [if_neg hij, add_zero]
      apply height_mono _ hr
      have hp67 := Nat.pow_le_pow_right hM (by decide : (6 : ℕ) ≤ 7)
      have hp1 : 1 ≤ M ^ 7 := Nat.one_le_pow _ _ hM
      omega
  have hresult := height_mul _ _ M (6 * M ^ 7) hρ hsum
  apply height_mono _ hresult
  convert (shapeCap_bounds M).2.2.2.2.2.2.2 using 1
  ring



open RamEllipsoidStep RamEllipsoidForm RamMatrixVector RamDotProduct RamEllipsoidUpdate

theorem step_stored_bounds (n H M k : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ)
    (hH : 1 ≤ H) (hA : ∀ i j, Height (A i j) H) (ha : ∀ i, Height (a i) H)
    (hc : ∀ i, Height (c i) H) (hnM : n ≤ M) (hFM : formHeight n H ≤ M)
    (hDM : 2 ^ (2 * k + 3 * n + 9) ≤ M) (hEM : 2 ^ (2 * n + 4) ≤ M) :
    (∀ i, Height (EllipsoidCenter.roundedCenter n A a c (2 ^ (2 * k + 3 * n + 9)) i)
        (shapeCap (coefficientCap M))) ∧
      (∀ i j, Height (EllipsoidCenter.roundedStepShape n A a (2 ^ (2 * k + 3 * n + 9))
        (EllipsoidIteration.stepAccuracy n) i j) (shapeCap (coefficientCap M))) := by
  let D := 2 ^ (2 * k + 3 * n + 9)
  let E := 2 ^ (2 * n + 4)
  let q := a ⬝ᵥ (A *ᵥ a)
  let N := coefficientCap M
  let gs := coefficients n q D E
  have hcapM := (formHeight_ge n H hH).trans hFM
  have hHM := (cap_ge n H hH).2.trans hcapM
  have hM := hH.trans hHM
  have hMN : M ≤ N := (coefficientCap_bounds M).1
  have hN : 1 ≤ N := hM.trans hMN
  have hDpos : 0 < D := Nat.pow_pos (by decide)
  have hq : Height q M := height_mono _ (form_height n H A a hH hA ha) hFM
  have hu : ∀ i, Height ((A *ᵥ a) i) N := fun i =>
    height_mono _ (mulVec_height n H A a hH hA ha i) (hcapM.trans hMN)
  have hAc : ∀ i j, Height (A i j) N := fun i j => height_mono _ (hA i j) (hHM.trans hMN)
  have hcc : ∀ i, Height (c i) N := fun i => height_mono _ (hc i) (hHM.trans hMN)
  have hgs : ∀ v ∈ gs, Height v N := coefficients_height n M D E q hq hnM hDM hEM hDpos
  have hg : 4 < gs.length := by simp [gs, coefficients]
  have hα := hgs gs[0] (by simp [gs, coefficients])
  have hβ := hgs gs[1] (by simp [gs, coefficients])
  have hγ := hgs gs[2] (by simp [gs, coefficients])
  have hρ := hgs gs[3] (by simp [gs, coefficients])
  have hδ := hgs gs[4] (by simp [gs, coefficients])
  have hcenter := centerValues_height N D (A *ᵥ a) c gs[2] hN (hDM.trans hMN) hDpos hu hcc hγ
  have hshape := shapeValues_height N D (A *ᵥ a) A gs hg hN (hDM.trans hMN) hDpos hu hAc hα hβ hρ hδ
  have heq := roundedUpdate_eq_ellipsoid A a c D E
  have hη : (1 / (E : ℚ)) = EllipsoidIteration.stepAccuracy n := by simp [E, EllipsoidIteration.stepAccuracy]
  change (∀ i, Height (EllipsoidCenter.roundedCenter n A a c D i) (shapeCap N)) ∧
    (∀ i j, Height (EllipsoidCenter.roundedStepShape n A a D (EllipsoidIteration.stepAccuracy n) i j) (shapeCap N))
  constructor
  · intro i
    have h := height_mono _ (hcenter i) (centerCap_le_shapeCap N)
    simpa only [gs, q, heq.1] using h
  · intro i j
    simpa only [gs, q, heq.2, hη] using hshape i j

end Lax109476Proofs.RamEllipsoidStoredBounds

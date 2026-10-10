import Lax109476Proofs.RamFeasibilityScales
import Lax109476Proofs.IterationBudget

namespace Lax109476Proofs.RamFeasibilityScaleBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open IntegerCertificates NormalizedFeasibility EllipsoidSequence IterationBudget RamFeasibilityScales

theorem magnitude_bound (m n H : ℕ) (hH : 1 ≤ H) :
    magnitude m n H ≤ 30 * (ballDenominator m n H + H +
      (thresholdSteps n (ballExponent m n H) + 1) + 1) := by
  let C := coordinateCap m n H
  let G := m * C + n * m * H * C
  let D := precisionDenominator m n H
  let R := outerScale n C
  let Z := ballDenominator m n H
  let E := ballExponent m n H
  let T := thresholdSteps n E
  have hC : 1 ≤ C := by
    dsimp [C, coordinateCap]
    exact Nat.mul_pos (Nat.factorial_pos _) (pow_pos (by omega) _)
  have hD : D = 2 * (G + 1) := rfl
  have hR : R = 4 * (n + 1) * (C + 1) := rfl
  have hZ : Z = D * (n * H + 1) * R := rfl
  have hDp : 0 < D := precisionDenominator_pos _ _ _
  have hRp : 0 < R := outerScale_pos _ _
  have hnp : 0 < n * H + 1 := by omega
  have hDZ : D ≤ Z := by
    rw [hZ]
    exact (Nat.le_mul_of_pos_right _ hnp).trans (Nat.le_mul_of_pos_right _ hRp)
  have hRZ : R ≤ Z := by
    rw [hZ]
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos hDp hnp)
  have hnHZ : n * H + 1 ≤ Z := by
    rw [hZ]
    exact (Nat.le_mul_of_pos_left _ hDp).trans (Nat.le_mul_of_pos_right _ hRp)
  have hDZprod : D * (n * H + 1) ≤ Z := by rw [hZ]; exact Nat.le_mul_of_pos_right _ hRp
  have hGZ : G + 1 ≤ Z := (by rw [hD] at hDZ; omega)
  have hnmHC : n * m * H ≤ n * m * H * C := Nat.le_mul_of_pos_right _ (by omega)
  have hnmH : n * m ≤ n * m * H := Nat.le_mul_of_pos_right _ (by omega)
  have hmC : m ≤ m * C := Nat.le_mul_of_pos_right _ (by omega)
  have hEZ : E ≤ Z := RationalSizeBounds.size_le_self Z
  have hET : E * n + 1 ≤ T := by
    dsimp [T, thresholdSteps]
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hCn : C + 1 ≤ R := by rw [hR]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hnC : 4 * (n + 1) ≤ R := by rw [hR]; exact Nat.le_mul_of_pos_right _ (by omega)
  change m + n + H + C + m * C + n * m + n * m * H + n * m * H * C + G + (G + 1) +
    D + (n + 1) + (C + 1) + 4 * (n + 1) + R + n * H + (n * H + 1) +
    D * (n * H + 1) + Z + E + E * n + (E * n + 1) + T + (T + 1) + 20 ≤
      30 * (Z + H + (T + 1) + 1)
  dsimp only [G] at hGZ
  omega

def wordWidth (S : ℕ) : ℕ := 4096 * (S + 1) ^ 4

theorem magnitude_fits (m n S w : ℕ) (hdim : m + n ≤ S) (hw : wordWidth S ≤ w) :
    magnitude m n (2 ^ (2 * S)) < 2 ^ w := by
  let Q := 1024 * (S + 1) ^ 4 + 128 * (S + 1) ^ 2 + 2 * S + 16
  let Z := ballDenominator m n (2 ^ (2 * S))
  let T := thresholdSteps n (ballExponent m n (2 ^ (2 * S)))
  have hZsize := ballExponent_polynomial m n S hdim
  have hZ : Z < 2 ^ Q := (Nat.lt_size_self Z).trans_le
    (Nat.pow_le_pow_right (by decide) (by change (ballExponent m n (2 ^ (2 * S))) ≤ Q; dsimp [Q]; omega))
  have hTbound := thresholdSteps_polynomial m n S hdim
  have hTQ : T + 2 ≤ Q := by dsimp [Q, T] at *; omega
  have hT : T + 2 < 2 ^ Q := (Nat.lt_two_pow_self (n := T + 2)).trans_le
    (Nat.pow_le_pow_right (by decide) hTQ)
  have hH : 2 ^ (2 * S) < 2 ^ Q := Nat.pow_lt_pow_right (by decide) (by dsimp [Q]; omega)
  have hmag := magnitude_bound m n (2 ^ (2 * S)) (Nat.one_le_pow _ _ (by decide))
  have hlarge : magnitude m n (2 ^ (2 * S)) < 2 ^ (Q + 7) := by
    rw [pow_add]
    norm_num
    change magnitude m n (2 ^ (2 * S)) ≤ 30 * (Z + 2 ^ (2 * S) + (T + 1) + 1) at hmag
    omega
  have hsq : (S + 1) ^ 2 ≤ (S + 1) ^ 4 := by
    exact pow_le_pow_right₀ (by omega : 1 ≤ S + 1) (by decide : 2 ≤ 4)
  have hSsq : S ≤ (S + 1) ^ 2 := by nlinarith
  have hQw : Q + 7 ≤ w := by dsimp [wordWidth, Q] at hw ⊢; nlinarith
  exact hlarge.trans_le (Nat.pow_le_pow_right (by decide) hQw)

theorem prepareScales_bounded_spec (m n S w : ℕ) (hdim : m + n ≤ S) (hw : wordWidth S ≤ w) :
    Spec (2 ^ w) (fun σ => σ.vars "query.m" = m ∧ σ.vars "query.n" = n ∧
        σ.vars "cap.H" = 2 ^ (2 * S) ∧ σ.vars "cap.value" = coordinateCap m n (2 ^ (2 * S)))
      prepareScales (fun _ τ => Output m n (2 ^ (2 * S)) τ)
      (1536 * (S + 1) ^ 2 + 62) := by
  exact (prepareScales_spec (2 ^ w) m n (2 ^ (2 * S)) (magnitude_fits m n S w hdim hw)).mono
    (by have h := ballExponent_polynomial m n S hdim; omega)

end Lax109476Proofs.RamFeasibilityScaleBounds

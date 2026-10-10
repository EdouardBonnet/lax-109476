import Lax109476Proofs.RamEllipsoidCoefficients
import Lax109476Proofs.RamShapeUpdate

namespace Lax109476Proofs.RamEllipsoidWordBounds

open RamEllipsoidCoefficients RamShapeCoordinate RamCenterCoordinate

theorem coefficientCap_bounds (M : ℕ) :
    M ≤ coefficientCap M ∧ M ^ 3 + 2 ≤ coefficientCap M ∧ 4 * (M + 1) ≤ coefficientCap M := by
  have hp1 : M + 1 ≤ (M + 1) ^ 4 :=
    le_self_pow (by omega) (by decide : (4 : ℕ) ≠ 0)
  have hp3 := (Nat.pow_le_pow_left (by omega : M ≤ M + 1) 3).trans
    (Nat.pow_le_pow_right (by omega : 1 ≤ M + 1) (by decide : (3 : ℕ) ≤ 4))
  have hone : 1 ≤ (M + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  unfold coefficientCap
  omega

theorem shapeCap_linear (N : ℕ) : 8 * (N + 1) ≤ shapeCap N := by
  exact Nat.mul_le_mul_left 8 (le_self_pow (by omega) (by decide : (8 : ℕ) ≠ 0))

theorem centerCap_le_shapeCap (N : ℕ) : centerCap N ≤ shapeCap N := by
  have hp := Nat.pow_le_pow_right (by omega : 1 ≤ N + 1) (by decide : (4 : ℕ) ≤ 8)
  have hone : 1 ≤ (N + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
  unfold centerCap shapeCap
  omega

theorem rootBound_le_shapeBound (M : ℕ) :
    (2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3 ≤ 2 * (shapeCap (coefficientCap M)) ^ 2 + 3 := by
  let N := coefficientCap M
  let S := shapeCap N
  have hM3 : M ^ 3 + 2 ≤ N := (coefficientCap_bounds M).2.1
  have hS : 8 * (N + 1) ≤ S := shapeCap_linear N
  have hbase : 2 * (M ^ 3 + 2) + 1 ≤ 2 * N + 1 := by omega
  have hsq := Nat.pow_le_pow_left hbase 2
  calc
    (2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3 ≤ (2 * N + 1) ^ 2 + N + 1 := by omega
    _ ≤ 2 * S ^ 2 + 3 := by nlinarith only [hS]

theorem dimensions_le_coefficientCap (n M : ℕ) (hn : 2 ≤ n) (hnM : n * n ≤ M) :
    n + n + n * n + 1 ≤ coefficientCap M := by
  have hnp : n ≤ n * n := by
    simpa only [pow_two] using le_self_pow (by omega : 1 ≤ n) (by decide : (2 : ℕ) ≠ 0)
  have hc := (coefficientCap_bounds M).2.2
  omega

theorem unified_word_bounds (B M n : ℕ) (hn : 2 ≤ n) (hnM : n * n ≤ M)
    (hB : 2 * (shapeCap (coefficientCap M)) ^ 2 + 3 < B) :
    coefficientCap M < B ∧ M < B ∧ n ^ 2 < B ∧ n < B ∧ 5 < B ∧
      n + n + n * n + 1 < B ∧ 2 * M ^ 2 + 3 < B ∧
      (2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3 < B ∧
      2 * (centerCap (coefficientCap M)) ^ 2 + 3 < B := by
  have hN := (coefficientCap_bounds M).1
  have hNS := (shapeCap_bounds (coefficientCap M)).1
  have hSB : shapeCap (coefficientCap M) < B := by nlinarith only [hB]
  have hNB := hNS.trans_lt hSB
  have hMB := hN.trans_lt hNB
  have hnB : n < B := lt_of_le_of_lt (by nlinarith only [hn, hnM]) hMB
  have h5B : 5 < B := by
    have hlin := shapeCap_linear (coefficientCap M)
    omega
  have hdimB := (dimensions_le_coefficientCap n M hn hnM).trans_lt hNB
  have hMS := hN.trans hNS
  have hpow := Nat.pow_le_pow_left hMS 2
  have hprim : 2 * M ^ 2 + 3 < B := lt_of_le_of_lt (by omega) hB
  have hroot := (rootBound_le_shapeBound M).trans_lt hB
  have hcenter := Nat.pow_le_pow_left (centerCap_le_shapeCap (coefficientCap M)) 2
  refine ⟨hNB, hMB, ?_, hnB, h5B, hdimB, hprim, hroot, ?_⟩
  · simpa only [pow_two] using hnM.trans_lt hMB
  · exact lt_of_le_of_lt (by omega) hB

end Lax109476Proofs.RamEllipsoidWordBounds

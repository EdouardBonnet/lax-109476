import Lax109476Proofs.PointRecovery
import Lax109476Proofs.BinaryOptimizationBounds
import Lax109476Proofs.IndexedPointRecovery

open scoped BigOperators

namespace Lax109476Proofs.RecoveryArithmeticBounds

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open PointRecovery CoordinateOptimization RationalArithmeticBounds
open BinaryOptimizationBounds LexicographicMinima EncodingSize

theorem recoverPrefix_height {m n : ℕ} (P : Program ℚ m n) (B k : ℕ)
    (x : Fin n → ℚ) (h : recoverPrefix P B k = some x) :
    ∀ i, Height (x i) (B * B + 1) := by
  induction k generalizing x with
  | zero =>
    simp only [recoverPrefix, Option.some.injEq] at h
    subst x
    intro i
    exact height_mono 0 height_zero (by omega)
  | succ k ih =>
    simp only [recoverPrefix, Option.bind_eq_some_iff] at h
    obtain ⟨old, hold, hx⟩ := h
    by_cases hk : k < n
    · rw [dif_pos hk] at hx
      obtain ⟨v, hv, hx⟩ := Option.map_eq_some_iff.mp hx
      subst x
      intro i
      by_cases hi : i = (⟨k, hk⟩ : Fin n)
      · subst i
        rw [Function.update_self]
        exact minimum_height _ B v hv
      · rw [Function.update_of_ne hi]
        exact ih old hold i
    · rw [dif_neg hk] at hx
      cases hx
      exact ih x hold

theorem program_height_size {m n : ℕ} (P : Program ℚ m n) (B : ℕ)
    (hA : ∀ i j, Height (P.A i j) B) (hb : ∀ i, Height (P.b i) B)
    (hc : ∀ j, Height (P.c j) B) :
    bitSize (encodeProgram P) ≤ m + n + 2 + (m * n + m + n) * (4 + 2 * B.size) := by
  have hsA : (∑ i, ∑ j, bitSize (encodeRational (P.A i j))) ≤ m * n * (4 + 2 * B.size) := by
    calc
      _ ≤ ∑ _i : Fin m, ∑ _j : Fin n, (4 + 2 * B.size) := by
        exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => height_encoding _ B (hA i j)))
      _ = _ := by simp; ring
  have hsb := bounded_vector_size P.b B hb
  have hsc := bounded_vector_size P.c B hc
  have hm := RationalSizeBounds.size_le_self m
  have hn := RationalSizeBounds.size_le_self n
  rw [program_size]
  rw [vector_size] at hsb hsc
  nlinarith

theorem fixedPrefix_height {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ)
    (k H B : ℕ) (hH : 1 ≤ H)
    (hA : ∀ i j, Height (P.A i j) H) (hb : ∀ i, Height (P.b i) H)
    (hc : ∀ j, Height (P.c j) H) (hx : ∀ j, Height (x j) B) :
    (∀ i j, Height ((fixedPrefix P x k).A i j) (max H B)) ∧
      (∀ i, Height ((fixedPrefix P x k).b i) (max H B)) ∧
      ∀ j, Height ((fixedPrefix P x k).c j) (max H B) := by
  have h0 : Height 0 (max H B) := height_mono 0 height_zero (hH.trans (le_max_left _ _))
  have h1 : Height 1 (max H B) := height_nat 1 _ (hH.trans (le_max_left _ _))
    (hH.trans (le_max_left _ _))
  have hm1 : Height (-1) (max H B) := height_neg 1 _ h1
  refine ⟨?_, ?_, fun j => height_mono _ (hc j) (le_max_left _ _)⟩
  · intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [fixedPrefix, Fin.addCases_left] using
        height_mono (P.A i j) (hA i j) (le_max_left H B)
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      all_goals simp only [fixedPrefix, Fin.addCases_right, Fin.addCases_left]
      all_goals split_ifs <;> assumption
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [fixedPrefix, Fin.addCases_left] using
        height_mono (P.b i) (hb i) (le_max_left H B)
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      all_goals simp only [fixedPrefix, Fin.addCases_right, Fin.addCases_left]
      · split_ifs
        · exact height_mono _ (hx i) (le_max_right _ _)
        · exact h0
      · split_ifs
        · exact height_mono _ (height_neg _ _ (hx i)) (le_max_right _ _)
        · exact h0

theorem coordinateCut_height {m n : ℕ} (P : Program ℚ m n) (j : Fin n)
    (t : ℚ) (H T : ℕ) (hH : 1 ≤ H)
    (hA : ∀ i k, Height (P.A i k) H) (hb : ∀ i, Height (P.b i) H)
    (hc : ∀ k, Height (P.c k) H) (ht : Height t T) :
    (∀ i k, Height ((coordinateCut P j t).A i k) (max H T)) ∧
      (∀ i, Height ((coordinateCut P j t).b i) (max H T)) ∧
      ∀ k, Height ((coordinateCut P j t).c k) (max H T) := by
  have h0 : Height 0 (max H T) := height_mono 0 height_zero (hH.trans (le_max_left _ _))
  have h1 : Height 1 (max H T) := height_nat 1 _ (hH.trans (le_max_left _ _))
    (hH.trans (le_max_left _ _))
  refine ⟨?_, ?_, fun k => height_mono _ (hc k) (le_max_left _ _)⟩
  · intro i k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [coordinateCut, Fin.addCases_left] using
        height_mono (P.A i k) (hA i k) (le_max_left H T)
    · simp only [coordinateCut, Fin.addCases_right]
      split_ifs <;> assumption
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [coordinateCut, Fin.addCases_left] using
        height_mono (P.b i) (hb i) (le_max_left H T)
    · simpa only [coordinateCut, Fin.addCases_right] using height_mono t ht (le_max_right H T)

theorem integerPoint_height {m n : ℕ} (P : Program ℤ m n) (H : ℕ)
    (x : Fin n → ℚ) (h : IntegerPointRecovery.point P H = some x) :
    ∀ i, Height (x i) ((LexicographicBounds.coordinateCap m (n + m) H) ^ 2 + 1) := by
  obtain ⟨z, hz, he⟩ := Option.map_eq_some_iff.mp h
  subst x
  intro i
  have hx := recoverPrefix_height _ _ _ z hz (Fin.castAdd m i)
  simpa only [pow_two] using hx

theorem indexedPoint_height {κ ι : Type*} {r n : ℕ} (A : κ → ι → ℤ) (b : κ → ℤ)
    (er : κ ≃ Fin r) (ec : ι ≃ Fin n) (H : ℕ) (x : ι → ℚ)
    (h : IndexedPointRecovery.point A b er ec H = some x) :
    ∀ i, Height (x i) ((LexicographicBounds.coordinateCap r (n + r) H) ^ 2 + 1) := by
  obtain ⟨z, hz, he⟩ := Option.map_eq_some_iff.mp h
  subst x
  exact fun i => integerPoint_height _ H z hz (ec i)

end Lax109476Proofs.RecoveryArithmeticBounds

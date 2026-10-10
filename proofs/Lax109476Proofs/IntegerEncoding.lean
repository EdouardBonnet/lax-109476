import Lax109476Proofs.EncodingSize

open scoped BigOperators Matrix

namespace Lax109476Proofs.IntegerEncoding

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding
open RationalSizeBounds EncodingSize

def programDenominator {m n : ℕ} (P : Program ℚ m n) : ℕ :=
  commonDenominator (programData P)

def integerProgram {m n : ℕ} (P : Program ℚ m n) : Program ℤ m n where
  A i j := clearedNumerator (programData P) (.inl (i, j))
  b i := clearedNumerator (programData P) (.inr (.inl i))
  c j := clearedNumerator (programData P) (.inr (.inr j))

def rationalProgram {m n : ℕ} (P : Program ℤ m n) : Program ℚ m n where
  A i j := P.A i j
  b i := P.b i
  c j := P.c j

def scaledProgram {m n : ℕ} (P : Program ℚ m n) (s : ℚ) : Program ℚ m n where
  A i j := s * P.A i j
  b i := s * P.b i
  c j := s * P.c j

theorem integerProgram_eq_scaled {m n : ℕ} (P : Program ℚ m n) :
    rationalProgram (integerProgram P) = scaledProgram P (programDenominator P) := by
  unfold rationalProgram integerProgram scaledProgram
  congr 1
  · funext i j
    exact clearedNumerator_cast (programData P) (.inl (i, j))
  · funext i
    exact clearedNumerator_cast (programData P) (.inr (.inl i))
  · funext j
    exact clearedNumerator_cast (programData P) (.inr (.inr j))

theorem programDenominator_bound {m n : ℕ} (P : Program ℚ m n) :
    programDenominator P ≤ 2 ^ bitSize (encodeProgram P) :=
  (commonDenominator_bound (programData P)).trans
    (Nat.pow_le_pow_right (by decide) (denominator_size_sum P))

theorem cleared_datum_bound {m n : ℕ} (P : Program ℚ m n) (i) :
    (clearedNumerator (programData P) i).natAbs ≤
      2 ^ (2 * bitSize (encodeProgram P)) := by
  have hn : (programData P i).num.natAbs ≤ 2 ^ bitSize (encodeProgram P) :=
    (Nat.lt_size_self _).le.trans
      (Nat.pow_le_pow_right (by decide) (datum_numerator_size P i))
  calc
    _ ≤ (programData P i).num.natAbs * programDenominator P :=
      clearedNumerator_bound _ i
    _ ≤ 2 ^ bitSize (encodeProgram P) * 2 ^ bitSize (encodeProgram P) :=
      Nat.mul_le_mul hn (programDenominator_bound P)
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem integerProgram_bounds {m n : ℕ} (P : Program ℚ m n) :
    (∀ i j, ((integerProgram P).A i j).natAbs ≤ 2 ^ (2 * bitSize (encodeProgram P))) ∧
    (∀ i, ((integerProgram P).b i).natAbs ≤ 2 ^ (2 * bitSize (encodeProgram P))) ∧
    (∀ j, ((integerProgram P).c j).natAbs ≤ 2 ^ (2 * bitSize (encodeProgram P))) :=
  ⟨fun i j => cleared_datum_bound P (.inl (i, j)),
    fun i => cleared_datum_bound P (.inr (.inl i)),
    fun j => cleared_datum_bound P (.inr (.inr j))⟩

theorem row_scaled {m n : ℕ} (P : Program ℚ m n) (s : ℚ) (x : Fin n → ℚ) (i) :
    rowValue (scaledProgram P s) x i = s * rowValue P x i := by
  simp only [rowValue, scaledProgram, Finset.mul_sum, mul_assoc]

theorem column_scaled {m n : ℕ} (P : Program ℚ m n) (s : ℚ) (y : Fin m → ℚ) (j) :
    columnValue (scaledProgram P s) y j = s * columnValue P y j := by
  simp only [columnValue, scaledProgram, Finset.mul_sum, mul_assoc]

theorem primalValue_scaled {m n : ℕ} (P : Program ℚ m n) (s : ℚ) (x : Fin n → ℚ) :
    primalValue (scaledProgram P s) x = s * primalValue P x := by
  simp only [primalValue, scaledProgram, Finset.mul_sum, mul_assoc]

theorem dualValue_scaled {m n : ℕ} (P : Program ℚ m n) (s : ℚ) (y : Fin m → ℚ) :
    dualValue (scaledProgram P s) y = s * dualValue P y := by
  simp only [dualValue, scaledProgram, Finset.mul_sum, mul_assoc]

theorem primal_feasible_scaled {m n : ℕ} (P : Program ℚ m n) (s : ℚ)
    (hs : 0 < s) (x : Fin n → ℚ) :
    PrimalFeasible (scaledProgram P s) x ↔ PrimalFeasible P x := by
  simp only [PrimalFeasible, row_scaled]
  change ((∀ j, 0 ≤ x j) ∧ ∀ i, s * rowValue P x i ≤ s * P.b i) ↔ _
  simp only [mul_le_mul_iff_of_pos_left hs]

theorem dual_feasible_scaled {m n : ℕ} (P : Program ℚ m n) (s : ℚ)
    (hs : 0 < s) (y : Fin m → ℚ) :
    DualFeasible (scaledProgram P s) y ↔ DualFeasible P y := by
  simp only [DualFeasible, column_scaled]
  change ((∀ i, 0 ≤ y i) ∧ ∀ j, s * P.c j ≤ s * columnValue P y j) ↔ _
  simp only [mul_le_mul_iff_of_pos_left hs]

theorem farkas_scaled {m n : ℕ} (P : Program ℚ m n) (s : ℚ)
    (hs : 0 < s) (y : Fin m → ℚ) :
    Lax109476.FarkasCertificate.IsInfeasibilityCertificate (scaledProgram P s) y ↔
      Lax109476.FarkasCertificate.IsInfeasibilityCertificate P y := by
  simp only [Lax109476.FarkasCertificate.IsInfeasibilityCertificate,
    column_scaled, dualValue_scaled]
  constructor <;> rintro ⟨hpos, hcol, hval⟩ <;> refine ⟨hpos, ?_, ?_⟩
  · intro j
    exact (mul_le_mul_iff_of_pos_left hs).mp (by simpa using hcol j)
  · exact (mul_lt_mul_iff_of_pos_left hs).mp (by simpa using hval)
  · intro j
    simpa using (mul_le_mul_iff_of_pos_left hs).mpr (hcol j)
  · simpa using (mul_lt_mul_iff_of_pos_left hs).mpr hval

theorem recession_scaled {m n : ℕ} (P : Program ℚ m n) (s : ℚ)
    (hs : 0 < s) (d : Fin n → ℚ) :
    Lax109476.RecessionDirection.IsImprovingDirection (scaledProgram P s) d ↔
      Lax109476.RecessionDirection.IsImprovingDirection P d := by
  simp only [Lax109476.RecessionDirection.IsImprovingDirection,
    row_scaled, primalValue_scaled]
  constructor <;> rintro ⟨hpos, hrow, hval⟩ <;> refine ⟨hpos, ?_, ?_⟩
  · intro i
    exact (mul_le_mul_iff_of_pos_left hs).mp (by simpa using hrow i)
  · exact (mul_lt_mul_iff_of_pos_left hs).mp (by simpa using hval)
  · intro i
    simpa using (mul_le_mul_iff_of_pos_left hs).mpr (hrow i)
  · simpa using (mul_lt_mul_iff_of_pos_left hs).mpr hval

/-- Positive common scaling preserves every exact certificate form. -/
theorem certificate_scaled {m n : ℕ} (P : Program ℚ m n) (s : ℚ)
    (hs : 0 < s) (certificate : Certificate m n) :
    IsValidCertificate (scaledProgram P s) certificate ↔
      IsValidCertificate P certificate := by
  cases certificate with
  | optimal x y =>
    simp only [IsValidCertificate, primal_feasible_scaled P s hs,
      dual_feasible_scaled P s hs, primalValue_scaled, dualValue_scaled,
      mul_right_inj' (ne_of_gt hs)]
  | infeasible y => exact farkas_scaled P s hs y
  | unbounded x d =>
    simp only [IsValidCertificate, primal_feasible_scaled P s hs,
      recession_scaled P s hs]

end Lax109476Proofs.IntegerEncoding

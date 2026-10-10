import Lax109476Proofs.RationalSizeBounds

open scoped BigOperators

namespace Lax109476Proofs.EncodingSize

open Lax759944.BinaryWordEncoding Lax109476.RationalEncoding
open Lax109476.LinearProgram

theorem bitSize_append (x y : List ℕ) : bitSize (x ++ y) = bitSize x + bitSize y := by
  simp [bitSize, encode]

theorem bitSize_cons (n : ℕ) (x : List ℕ) :
    bitSize (n :: x) = Nat.size n + 1 + bitSize x := by
  simp [bitSize, encode, encodeNat, Nat.size_eq_bits_len]
  omega

theorem bitSize_nil : bitSize [] = 0 := rfl

theorem bitSize_flatMap {α : Type*} (x : List α) (f : α → List ℕ) :
    bitSize (x.flatMap f) = (x.map (fun a => bitSize (f a))).sum := by
  induction x with
  | nil => rfl
  | cons a x ih => simp only [List.flatMap_cons, bitSize_append,
      List.map_cons, List.sum_cons, ih]

theorem rational_size_bounds (q : ℚ) :
    3 ≤ bitSize (encodeRational q) ∧
      Nat.size q.num.natAbs + Nat.size q.den ≤ bitSize (encodeRational q) := by
  unfold encodeRational
  rw [bitSize_cons, bitSize_cons, bitSize_cons, bitSize_nil]
  omega

theorem rational_size_upper (q : ℚ) :
    bitSize (encodeRational q) ≤ 4 + Nat.size q.num.natAbs + Nat.size q.den := by
  unfold encodeRational
  rw [bitSize_cons, bitSize_cons, bitSize_cons, bitSize_nil]
  split_ifs <;> norm_num [Nat.size] <;> omega

theorem vector_size {n : ℕ} (x : Fin n → ℚ) :
    bitSize (encodeVector x) = ∑ j, bitSize (encodeRational (x j)) := by
  rw [encodeVector, bitSize_flatMap, List.map_ofFn, List.sum_ofFn]
  rfl

theorem bounded_vector_size {n : ℕ} (x : Fin n → ℚ) (B : ℕ)
    (hx : ∀ j, (x j).num.natAbs ≤ B ∧ (x j).den ≤ B) :
    bitSize (encodeVector x) ≤ n * (4 + 2 * Nat.size B) := by
  rw [vector_size]
  calc
    _ ≤ ∑ _j : Fin n, (4 + 2 * Nat.size B) := by
      apply Finset.sum_le_sum
      intro j _
      have hn := Nat.size_le_size (hx j).1
      have hd := Nat.size_le_size (hx j).2
      have hu := rational_size_upper (x j)
      omega
    _ = _ := by simp

theorem program_size {m n : ℕ} (P : Program ℚ m n) :
    bitSize (encodeProgram P) = Nat.size m + Nat.size n + 2 +
      (∑ i, ∑ j, bitSize (encodeRational (P.A i j))) +
      (∑ i, bitSize (encodeRational (P.b i))) +
      (∑ j, bitSize (encodeRational (P.c j))) := by
  have hmatrix : bitSize ((List.ofFn fun i => List.ofFn (P.A i)).flatten.flatMap
      encodeRational) = ∑ i, ∑ j, bitSize (encodeRational (P.A i j)) := by
    rw [List.flatten_eq_flatMap, List.flatMap_assoc, bitSize_flatMap,
      List.map_ofFn, List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro i _
    change bitSize ((List.ofFn (P.A i)).flatMap encodeRational) = _
    rw [bitSize_flatMap, List.map_ofFn, List.sum_ofFn]
    rfl
  unfold encodeProgram
  rw [bitSize_append, bitSize_append, bitSize_append, bitSize_cons,
    bitSize_cons, bitSize_nil, vector_size, vector_size, hmatrix]
  omega

/-- All rational data occurring in the input, indexed without duplication. -/
def programData {m n : ℕ} (P : Program ℚ m n) :
    ((Fin m × Fin n) ⊕ (Fin m ⊕ Fin n)) → ℚ :=
  Sum.elim (fun ij => P.A ij.1 ij.2) (Sum.elim P.b P.c)

theorem data_size_sum {m n : ℕ} (P : Program ℚ m n) :
    (∑ i, bitSize (encodeRational (programData P i))) ≤ bitSize (encodeProgram P) := by
  rw [program_size]
  simp only [programData, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Sum.elim_inl, Sum.elim_inr]
  omega

theorem denominator_size_sum {m n : ℕ} (P : Program ℚ m n) :
    (∑ i, Nat.size (programData P i).den) ≤ bitSize (encodeProgram P) := by
  apply le_trans _ (data_size_sum P)
  apply Finset.sum_le_sum
  intro i _
  have h := (rational_size_bounds (programData P i)).2
  omega

theorem datum_numerator_size {m n : ℕ} (P : Program ℚ m n) (i) :
    Nat.size (programData P i).num.natAbs ≤ bitSize (encodeProgram P) := by
  have h := (rational_size_bounds (programData P i)).2
  have hs := Finset.single_le_sum (fun j _ => Nat.zero_le
    (bitSize (encodeRational (programData P j)))) (Finset.mem_univ i)
  have hb := data_size_sum P
  omega

theorem dimension_bound {m n : ℕ} (P : Program ℚ m n) :
    m + n ≤ bitSize (encodeProgram P) := by
  have hb : m ≤ ∑ i, bitSize (encodeRational (P.b i)) := by
    calc
      m = ∑ _i : Fin m, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => by have h := (rational_size_bounds (P.b i)).1; omega)
  have hc : n ≤ ∑ j, bitSize (encodeRational (P.c j)) := by
    calc
      n = ∑ _j : Fin n, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j _ => by have h := (rational_size_bounds (P.c j)).1; omega)
  rw [program_size]
  omega

end Lax109476Proofs.EncodingSize

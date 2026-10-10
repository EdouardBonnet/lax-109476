import Lax109476.RationalEncoding
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace Lax109476Proofs.WordDecoding

open Lax109476.LinearProgram Lax109476.RationalEncoding

def signedNumerator (sign magnitude : ℕ) : ℤ :=
  if sign = 1 then -(magnitude : ℤ) else magnitude

def readRational : List ℕ → Option (ℚ × List ℕ)
  | sign :: magnitude :: denominator :: rest =>
    if sign ≤ 1 ∧ 0 < denominator then
      some ((signedNumerator sign magnitude : ℚ) / denominator, rest)
    else none
  | _ => none

theorem signedNumerator_encode (q : ℚ) :
    signedNumerator (if q.num < 0 then 1 else 0) q.num.natAbs = q.num := by
  unfold signedNumerator
  by_cases h : q.num < 0
  · simp [h, abs_of_neg h]
  · simp [h, abs_of_nonneg (le_of_not_gt h)]

theorem readRational_encode (q : ℚ) (rest : List ℕ) :
    readRational (encodeRational q ++ rest) = some (q, rest) := by
  have hs : (if q.num < 0 then 1 else 0 : ℕ) ≤ 1 := by split_ifs <;> omega
  simp only [encodeRational, List.cons_append, List.nil_append, readRational,
    if_pos (And.intro hs q.den_pos), signedNumerator_encode, Rat.num_div_den]

def readVector : (n : ℕ) → List ℕ → Option ((Fin n → ℚ) × List ℕ)
  | 0, xs => some (0, xs)
  | n + 1, xs => do
    let (q, rest) ← readRational xs
    let (x, tail) ← readVector n rest
    pure (Fin.cons q x, tail)

theorem encodeVector_cons (n : ℕ) (q : ℚ) (x : Fin n → ℚ) :
    encodeVector (Fin.cons q x) = encodeRational q ++ encodeVector x := by
  simp [encodeVector, List.ofFn_succ]

theorem readVector_encode (n : ℕ) (x : Fin n → ℚ) (rest : List ℕ) :
    readVector n (encodeVector x ++ rest) = some (x, rest) := by
  induction n generalizing rest with
  | zero =>
    have hx : x = 0 := by funext j; exact Fin.elim0 j
    simp [readVector, encodeVector, hx]
  | succ n ih =>
    have hx : x = Fin.cons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
    rw [hx, encodeVector_cons, List.append_assoc]
    simp [readVector, readRational_encode, ih]

def encodeRows {m n : ℕ} (A : Fin m → Fin n → ℚ) : List ℕ :=
  (List.ofFn fun i => encodeVector (A i)).flatten

def readRows (n : ℕ) : (m : ℕ) → List ℕ → Option ((Fin m → Fin n → ℚ) × List ℕ)
  | 0, xs => some (0, xs)
  | m + 1, xs => do
    let (row, rest) ← readVector n xs
    let (rows, tail) ← readRows n m rest
    pure (Fin.cons row rows, tail)

theorem encodeRows_cons {m n : ℕ} (row : Fin n → ℚ) (rows : Fin m → Fin n → ℚ) :
    encodeRows (Fin.cons row rows) = encodeVector row ++ encodeRows rows := by
  simp [encodeRows, List.ofFn_succ]

theorem readRows_encode (m n : ℕ) (A : Fin m → Fin n → ℚ) (rest : List ℕ) :
    readRows n m (encodeRows A ++ rest) = some (A, rest) := by
  induction m generalizing rest with
  | zero =>
    have hA : A = 0 := by funext j; exact Fin.elim0 j
    simp [readRows, encodeRows, hA]
  | succ m ih =>
    have hA : A = Fin.cons (A 0) (Fin.tail A) := (Fin.cons_self_tail A).symm
    rw [hA, encodeRows_cons, List.append_assoc]
    simp [readRows, readVector_encode, ih]

theorem encodeVector_length (n : ℕ) (x : Fin n → ℚ) : (encodeVector x).length = 3 * n := by
  induction n with
  | zero => simp [encodeVector]
  | succ n ih =>
    rw [← Fin.cons_self_tail x, encodeVector_cons, List.length_append]
    simp only [encodeRational, List.length_cons, List.length_nil]
    rw [ih]
    omega

theorem encodeRows_length (m n : ℕ) (A : Fin m → Fin n → ℚ) :
    (encodeRows A).length = 3 * m * n := by
  induction m with
  | zero => simp [encodeRows]
  | succ m ih =>
    rw [← Fin.cons_self_tail A, encodeRows_cons, List.length_append, encodeVector_length, ih]
    ring

theorem encodeProgram_rows {m n : ℕ} (P : Program ℚ m n) :
    encodeProgram P = m :: n :: (encodeRows P.A ++ encodeVector P.b ++ encodeVector P.c) := by
  have hrows : (List.ofFn fun i => List.ofFn (P.A i)).flatten.flatMap encodeRational =
      encodeRows P.A := by
    unfold encodeRows encodeVector
    rw [List.flatten_eq_flatMap, List.flatMap_assoc, List.flatMap_def, List.map_ofFn]
    rfl
  simp only [encodeProgram, hrows]
  rfl

structure PackedProgram where
  m : ℕ
  n : ℕ
  program : Program ℚ m n

def decode : List ℕ → Option PackedProgram
  | m :: n :: xs =>
    if m ≤ xs.length + 1 ∧ n ≤ xs.length + 1 then do
      let (A, rest) ← readRows n m xs
      let (b, rest) ← readVector m rest
      let (c, rest) ← readVector n rest
      if rest = [] then pure ⟨m, n, { A := A, b := b, c := c }⟩ else none
    else none
  | _ => none

theorem decode_encode {m n : ℕ} (P : Program ℚ m n) :
    decode (encodeProgram P) = some ⟨m, n, P⟩ := by
  rw [encodeProgram_rows]
  have hlen : (encodeRows P.A ++ encodeVector P.b ++ encodeVector P.c).length =
      3 * m * n + 3 * m + 3 * n := by
    rw [List.length_append, List.length_append, encodeRows_length,
      encodeVector_length, encodeVector_length]
  have hm : m ≤ (encodeRows P.A ++ encodeVector P.b ++ encodeVector P.c).length + 1 := by
    rw [hlen]
    omega
  have hn : n ≤ (encodeRows P.A ++ encodeVector P.b ++ encodeVector P.c).length + 1 := by
    rw [hlen]
    omega
  have hA := readRows_encode m n P.A (encodeVector P.b ++ encodeVector P.c)
  have hb := readVector_encode m P.b (encodeVector P.c)
  have hc := readVector_encode n P.c []
  simp only [List.append_nil] at hc
  simp only [List.append_assoc] at hm hn ⊢
  simp [decode, hA, hb, hc]
  simpa only [List.length_append] using And.intro hm hn

end Lax109476Proofs.WordDecoding

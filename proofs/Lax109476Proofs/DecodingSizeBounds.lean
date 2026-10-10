import Lax109476Proofs.WordDecoding
import Lax109476Proofs.DeterminantBounds
import Lax109476Proofs.EncodingSize

namespace Lax109476Proofs.DecodingSizeBounds

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding WordDecoding EncodingSize DeterminantBounds

theorem rational_reencoding_size (s a d : ℕ) (hd : 0 < d) :
    bitSize (encodeRational ((signedNumerator s a : ℚ) / d)) ≤ bitSize [s, a, d] := by
  let q : ℚ := (signedNumerator s a : ℚ) / d
  obtain ⟨hn, hden⟩ := integer_ratio_num_den_bound (signedNumerator s a) (d : ℤ)
    (by exact_mod_cast ne_of_gt hd)
  simp only [Int.cast_natCast] at hn hden
  have ha : (signedNumerator s a).natAbs = a := by
    unfold signedNumerator
    split_ifs <;> simp
  rw [ha] at hn
  simp only [Int.natAbs_natCast] at hden
  have hs : (if q.num < 0 then 1 else 0 : ℕ) ≤ s := by
    by_cases h : s = 1
    · rw [h]; split_ifs <;> omega
    · have hq : 0 ≤ q := by dsimp [q, signedNumerator]; rw [if_neg h]; positivity
      have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr hq
      simp only [if_neg (not_lt.mpr hnum)]
      omega
  have hns := Nat.size_le_size hn
  have hds := Nat.size_le_size hden
  have hss := Nat.size_le_size hs
  change q.num.natAbs.size ≤ a.size at hns
  change q.den.size ≤ d.size at hds
  change bitSize (encodeRational q) ≤ _
  simp only [encodeRational, bitSize_cons, bitSize_nil]
  omega

theorem readRational_size (xs : List ℕ) (q : ℚ) (rest : List ℕ)
    (h : readRational xs = some (q, rest)) :
    bitSize (encodeRational q) + bitSize rest ≤ bitSize xs := by
  match xs with
  | s :: a :: d :: tail =>
    simp only [readRational] at h
    split_ifs at h with hg
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hs := rational_reencoding_size s a d hg.2
      simp only [bitSize_cons, bitSize_nil] at hs ⊢
      omega
  | [] | [_] | [_, _] => simp [readRational] at h

theorem readVector_size (n : ℕ) (xs : List ℕ) (x : Fin n → ℚ) (rest : List ℕ)
    (h : readVector n xs = some (x, rest)) :
    bitSize (encodeVector x) + bitSize rest ≤ bitSize xs := by
  induction n generalizing xs rest with
  | zero =>
    simp only [readVector, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [encodeVector, bitSize_nil]
  | succ n ih =>
    obtain ⟨⟨q, mid⟩, hq, hx⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨y, tail⟩, hy, he⟩ := Option.bind_eq_some_iff.mp hx
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have h₁ := readRational_size xs q mid hq
    have h₂ := ih mid y tail hy
    rw [encodeVector_cons, bitSize_append]
    omega

theorem readRows_size (m n : ℕ) (xs : List ℕ) (A : Fin m → Fin n → ℚ) (rest : List ℕ)
    (h : readRows n m xs = some (A, rest)) :
    bitSize (encodeRows A) + bitSize rest ≤ bitSize xs := by
  induction m generalizing xs rest with
  | zero =>
    simp only [readRows, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [encodeRows, bitSize_nil]
  | succ m ih =>
    obtain ⟨⟨row, mid⟩, hrow, hx⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨rows, tail⟩, hrows, he⟩ := Option.bind_eq_some_iff.mp hx
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have h₁ := readVector_size n xs row mid hrow
    have h₂ := ih mid rows tail hrows
    rw [encodeRows_cons, bitSize_append]
    omega

/-- Rational reduction during decoding cannot increase the input's canonical
binary size, including when the supplied triples are not reduced. -/
theorem decode_size (xs : List ℕ) (packed : PackedProgram) (h : decode xs = some packed) :
    bitSize (encodeProgram packed.program) ≤ bitSize xs := by
  match xs with
  | m :: n :: input =>
    simp only [decode] at h
    split_ifs at h with hg
    · obtain ⟨⟨A, afterA⟩, hA, hx⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨b, afterB⟩, hb, hx⟩ := Option.bind_eq_some_iff.mp hx
      obtain ⟨⟨c, afterC⟩, hc, hx⟩ := Option.bind_eq_some_iff.mp hx
      split_ifs at hx with hnil
      · change afterC = [] at hnil
        subst afterC
        simp only [Option.pure_def, Option.some.injEq] at hx
        subst packed
        have hsA := readRows_size m n input A afterA hA
        have hsb := readVector_size m afterA b afterB hb
        have hsc := readVector_size n afterB c [] hc
        rw [encodeProgram_rows]
        simp only [bitSize_cons, bitSize_append, bitSize_nil] at hsc ⊢
        omega
  | [] | [_] => simp [decode] at h

end Lax109476Proofs.DecodingSizeBounds

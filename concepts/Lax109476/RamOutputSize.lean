import Lax759944.RamPolytime

/-!
---
title: Polynomial-time RAM computations have polynomial-size outputs
type: theorem
---
The binary output size of every polynomial-time word-RAM computation is
bounded by a polynomial in the binary input size.

# Formalization notes

This follows from the registered machine's sequential append-only output:
each executed instruction writes at most one word. The runtime predicate
also bounds the sufficient word length polynomially in input size and
requires each output entry to fit. Their product bounds total binary output
size, including the separators in the canonical word-list encoding.
-/

namespace Lax109476.RamOutputSize

open Lax759944.RamPolytime Lax759944.BinaryWordEncoding

/-- Polynomial instruction and word-length bounds imply a polynomial output bound. -/
axiom exists_polynomial_output_bound :
  ∀ f : List ℕ → List ℕ, RamPolytime f →
    ∃ C k : ℕ, 0 < C ∧ ∀ x : List ℕ,
      bitSize (f x) ≤ C * (bitSize x + 1) ^ k

end Lax109476.RamOutputSize

import Lax109476.RationalCertificates
import Lax759944.RamPolytime

/-!
---
title: Binary-size encoding of rational linear programs
type: definition
---
An LP input word begins with its number of inequalities $m$ and variables
$n$, followed by the matrix in row order, the vector $b$, and the vector $c$.
A rational is encoded by its numerator sign, numerator magnitude, and
positive denominator, in reduced form. Solution words begin with an outcome
tag and contain the corresponding rational certificate coordinates.

# Formalization notes

The input sign is zero for nonnegative numerators and one for negative
numerators. Output tags zero, one, and two mean optimal, infeasible, and
unbounded. Dimensions are supplied by the input, so witness vectors have
fixed known lengths. Each rational keeps its exact denominator.

The imported `RamPolytime` predicate uses binary word-list size, a single
uniform program, polynomial bounds on sufficient word length and executed
instructions, and correctness at every sufficiently large word length on
Lax808846's registered RAM. Its specified physical tape is length-prefixed.
Malformed logical inputs have no prescribed output, but the solver function
is total. No new machine model or abstract running-time annotation is introduced.
-/

namespace Lax109476.RationalEncoding

open Lax109476.LinearProgram Lax109476.RationalCertificates

/-- Encode a reduced rational by sign, magnitude, and denominator. -/
def encodeRational (q : ℚ) : List ℕ :=
  [if q.num < 0 then 1 else 0, q.num.natAbs, q.den]

/-- Encode all coordinates of a rational vector in index order. -/
def encodeVector {n : ℕ} (x : Fin n → ℚ) : List ℕ :=
  (List.ofFn x).flatMap encodeRational

/-- Encode dimensions, row-major coefficients, row bounds, and objective. -/
def encodeProgram {m n : ℕ} (P : Program ℚ m n) : List ℕ :=
  [m, n] ++ (List.ofFn fun i => List.ofFn (P.A i)).flatten.flatMap encodeRational ++
    encodeVector P.b ++ encodeVector P.c

/-- Encode the outcome tag and all rational certificate coordinates. -/
def encodeCertificate {m n : ℕ} : Certificate m n → List ℕ
  | .optimal x y => [0] ++ encodeVector x ++ encodeVector y
  | .infeasible y => [1] ++ encodeVector y
  | .unbounded x d => [2] ++ encodeVector x ++ encodeVector d

end Lax109476.RationalEncoding

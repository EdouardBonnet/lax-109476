import Lax109476.RationalEncoding

/-!
---
title: Exact polynomial-time linear programming on a word RAM
type: theorem
---
There is one polynomial-time word-RAM algorithm that solves every rational
linear program exactly. It returns either an optimal primal point and matching
dual multipliers, an infeasibility certificate, or a feasible point and an
improving recession direction certifying unboundedness.

# Formalization notes

This is the classical polynomial-time solvability theorem for rational
linear programming, with the outcomes stated through exact certificates.
The computation predicate is `Lax759944.RamPolytime.RamPolytime`, using the
registered word RAM and the input's binary size. The returned word must
equal the encoding of the same certificate whose conditions are checked.
No fixed dimension, bounded coefficient magnitude, or feasibility promise
is imposed. Empty dimensions are included.

The existence of a polynomial-time solver is the algorithmic obligation;
ellipsoid-method internals are not separate claims in this submission.
-/

namespace Lax109476.PolynomialTimeSolver

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.RamPolytime

/-- One uniform polynomial-time RAM produces exact certificates for every LP. -/
axiom exists_exact_polynomial_time_solver :
  ∃ solve : List ℕ → List ℕ, RamPolytime solve ∧
    ∀ (m n : ℕ) (P : Program ℚ m n), ∃ certificate : Certificate m n,
      solve (encodeProgram P) = encodeCertificate certificate ∧
        IsValidCertificate P certificate

end Lax109476.PolynomialTimeSolver

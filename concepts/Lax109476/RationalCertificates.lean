import Lax109476.FarkasCertificate
import Lax109476.RecessionDirection
import Mathlib.Data.Rat.Cast.Order

/-!
---
title: Exact rational solution certificates
type: definition
---
A rational linear program is a linear program with rational coefficients,
still optimized over real variables. Its outcomes have three certificate forms:

* an optimal primal point and matching dual multipliers;
* nonnegative Farkas multipliers certifying infeasibility;
* a feasible primal point and an improving recession direction certifying
  unboundedness.

Every coordinate in these certificates is rational, and all certificate
conditions can be checked by exact rational arithmetic.

# Formalization notes

The three constructors carry precisely the witnesses needed for their
claims. The predicates use the same row, column, and objective formulas
as the real program. The real interpretation casts the coefficient data
and witness coordinates exactly. No outcome or correctness proof is
assumed as part of the input.
-/

namespace Lax109476.RationalCertificates

open Lax109476.LinearProgram Lax109476.FarkasCertificate Lax109476.RecessionDirection

/-- Interpret rational coefficient data as a real linear program. -/
def toReal {m n : ℕ} (P : Program ℚ m n) : Program ℝ m n where
  A i j := P.A i j
  b i := P.b i
  c j := P.c j

/-- The exact real interpretation of a rational vector. -/
def realVector {n : ℕ} (x : Fin n → ℚ) : Fin n → ℝ := fun j => x j

/-- A rational certificate for one of the three possible LP outcomes. -/
inductive Certificate (m n : ℕ)
  /-- Primal and dual points with matching objectives. -/
  | optimal (x : Fin n → ℚ) (y : Fin m → ℚ)
  /-- Separating nonnegative multipliers for an infeasible primal system. -/
  | infeasible (y : Fin m → ℚ)
  /-- A feasible base point and an improving recession direction. -/
  | unbounded (x d : Fin n → ℚ)

/-- The exact rational inequalities and equalities validating a certificate. -/
def IsValidCertificate {m n : ℕ} (P : Program ℚ m n) : Certificate m n → Prop
  | .optimal x y => PrimalFeasible P x ∧ DualFeasible P y ∧ primalValue P x = dualValue P y
  | .infeasible y => IsInfeasibilityCertificate P y
  | .unbounded x d => PrimalFeasible P x ∧ IsImprovingDirection P d

/-- The real mathematical claim made by each certificate constructor. -/
def IsCorrectOutcome {m n : ℕ} (P : Program ℚ m n) : Certificate m n → Prop
  | .optimal x _ => IsPrimalOptimal (toReal P) (realVector x)
  | .infeasible _ => ¬ IsFeasible (toReal P)
  | .unbounded _ _ => IsFeasible (toReal P) ∧ ¬ IsBoundedAbove (toReal P)

end Lax109476.RationalCertificates

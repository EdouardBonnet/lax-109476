import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic

/-!
---
title: Linear programs and their duals
type: definition
---
A linear program in inequality form is
$$\max\{c^T x: Ax\le b,\ x\ge0\}.$$
Its dual is
$$\min\{b^T y: A^T y\ge c,\ y\ge0\}.$$
All vector inequalities are componentwise. A feasible maximization program
is bounded above if one finite real number bounds the objective of every
feasible point. A primal point is optimal if it is feasible and no feasible
point has a larger objective.

# Formalization notes

There are `n` variables and `m` inequalities, indexed by `Fin n` and `Fin m`.
The coefficient data are shared by real and rational instances. Feasibility
and objective formulas are the same in either field. Both dimensions may be
zero. No feasibility, boundedness, optimizer, or optimum value is bundled
into the input data. Theorems state the necessary hypotheses explicitly.
Equality constraints and unrestricted variables can be represented by paired
inequalities and differences of nonnegative variables.
-/

open scoped BigOperators

namespace Lax109476.LinearProgram

/-- Coefficients of a maximization program with `m` inequalities and `n`
nonnegative variables. -/
structure Program (K : Type) (m n : ℕ) where
  /-- The constraint matrix. -/
  A : Fin m → Fin n → K
  /-- The upper bounds on the constraint rows. -/
  b : Fin m → K
  /-- The coefficients of the maximized objective. -/
  c : Fin n → K

/-- The value of one constraint row at a primal point. -/
def rowValue {K : Type} [Ring K] {m n : ℕ} (P : Program K m n)
    (x : Fin n → K) (i : Fin m) : K :=
  ∑ j, P.A i j * x j

/-- One component of the transposed matrix applied to a dual point. -/
def columnValue {K : Type} [Ring K] {m n : ℕ} (P : Program K m n)
    (y : Fin m → K) (j : Fin n) : K :=
  ∑ i, P.A i j * y i

/-- The primal objective value. -/
def primalValue {K : Type} [Ring K] {m n : ℕ} (P : Program K m n)
    (x : Fin n → K) : K :=
  ∑ j, P.c j * x j

/-- The dual objective value. -/
def dualValue {K : Type} [Ring K] {m n : ℕ} (P : Program K m n)
    (y : Fin m → K) : K :=
  ∑ i, P.b i * y i

/-- A nonnegative primal point satisfies all row upper bounds. -/
def PrimalFeasible {K : Type} [Ring K] [PartialOrder K] {m n : ℕ}
    (P : Program K m n) (x : Fin n → K) : Prop :=
  (∀ j, 0 ≤ x j) ∧ ∀ i, rowValue P x i ≤ P.b i

/-- A nonnegative dual point dominates every objective coefficient. -/
def DualFeasible {K : Type} [Ring K] [PartialOrder K] {m n : ℕ}
    (P : Program K m n) (y : Fin m → K) : Prop :=
  (∀ i, 0 ≤ y i) ∧ ∀ j, P.c j ≤ columnValue P y j

/-- The real primal feasible set is nonempty. -/
def IsFeasible {m n : ℕ} (P : Program ℝ m n) : Prop :=
  ∃ x, PrimalFeasible P x

/-- A finite upper bound holds for every real primal feasible point. -/
def IsBoundedAbove {m n : ℕ} (P : Program ℝ m n) : Prop :=
  ∃ B : ℝ, ∀ x, PrimalFeasible P x → primalValue P x ≤ B

/-- A primal feasible point maximizes the objective over the feasible set. -/
def IsPrimalOptimal {K : Type} [Ring K] [PartialOrder K] {m n : ℕ}
    (P : Program K m n) (x : Fin n → K) : Prop :=
  PrimalFeasible P x ∧ ∀ z, PrimalFeasible P z → primalValue P z ≤ primalValue P x

end Lax109476.LinearProgram

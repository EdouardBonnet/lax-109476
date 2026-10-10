import Lax109476.LinearProgram

/-!
---
title: Certificates of unboundedness
type: definition
---
An improving recession direction satisfies
$$d\ge0,\qquad Ad\le0,\qquad c^T d>0.$$
Together with any primal feasible point $x$, it certifies unboundedness:
$x+td$ is feasible for every $t\ge0$ and its objective tends to infinity.

# Formalization notes

A direction alone does not certify that the primal is unbounded: the
feasible set could be empty. Certificates therefore include a feasible
base point as well as the direction.
-/

namespace Lax109476.RecessionDirection

open Lax109476.LinearProgram

/-- A nonnegative direction preserves every upper constraint and improves
the maximized objective. -/
def IsImprovingDirection {K : Type} [Ring K] [PartialOrder K] {m n : ℕ}
    (P : Program K m n) (d : Fin n → K) : Prop :=
  (∀ j, 0 ≤ d j) ∧ (∀ i, rowValue P d i ≤ 0) ∧ 0 < primalValue P d

end Lax109476.RecessionDirection

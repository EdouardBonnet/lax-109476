import Lax109476Proofs.RationalReconstruction

namespace Lax109476Proofs.ReconstructionPrefix

def acceptable (l u : ℚ) (D : ℕ) (q : ℚ) : Bool := decide (q.den ≤ D ∧ l ≤ q ∧ q ≤ u)

def scan (l u : ℚ) (D j : ℕ) : Option ℚ :=
  ((List.range j).map (RationalReconstruction.convergent u)).find? (acceptable l u D)

theorem scan_zero (l u : ℚ) (D : ℕ) : scan l u D 0 = none := by simp [scan]

theorem scan_succ (l u : ℚ) (D j : ℕ) :
    scan l u D (j + 1) = match scan l u D j with
      | some q => some q
      | none => if acceptable l u D (RationalReconstruction.convergent u j) then
          some (RationalReconstruction.convergent u j) else none := by
  simp only [scan, List.range_succ, List.map_append, List.map_singleton, List.find?_append,
    List.find?_cons, List.find?_nil]
  cases h : ((List.range j).map (RationalReconstruction.convergent u)).find? (acceptable l u D) <;> simp
  cases acceptable l u D (RationalReconstruction.convergent u j) <;> rfl

theorem scan_complete (l u : ℚ) (D : ℕ) :
    scan l u D (2 * u.den.size + 1) = RationalReconstruction.reconstruct l u D := rfl

end Lax109476Proofs.ReconstructionPrefix

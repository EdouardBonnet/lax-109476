import Lax109476Proofs.LexicographicMinima
import Lax109476Proofs.SmallFeasiblePoint

open scoped BigOperators Matrix

namespace Lax109476Proofs.LexicographicBounds

open StandardForm LexicographicSupport LexicographicMinima SmallFeasiblePoint
open Lax109476.LinearProgram Lax109476.RationalCertificates

def coordinateCap (m n H : ℕ) : ℕ := n.factorial * (m * H ^ 2 + 1) ^ n

theorem independent_support_coordinate_bound {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (z : Fin n → ℚ)
    (H : ℕ) (hA : ∀ i j, (A i j).natAbs ≤ H) (hb : ∀ i, (b i).natAbs ≤ H)
    (hz : (A.map (fun a => (a : ℚ))) *ᵥ z = fun i => (b i : ℚ))
    (hind : LinearIndepOn ℚ (A.map (fun a => (a : ℚ))).col (support z : Set (Fin n))) :
    ∀ j, (z j).num.natAbs ≤ coordinateCap m n H ∧ (z j).den ≤ coordinateCap m n H := by
  classical
  let s := support z
  let C : Matrix (Fin m) s ℤ := fun i j => A i j.1
  have hcpos : ∀ i j, (C i j).natAbs ≤ H := fun i j => hA i j.1
  have hcind : LinearIndependent ℚ (C.map (fun a => (a : ℚ))).col := hind
  have hceq : (C.map (fun a => (a : ℚ))) *ᵥ (fun j : s => z j.1) =
      fun i => (b i : ℚ) := by
    ext i
    change (∑ j : s, (A i j.1 : ℚ) * z j.1) = (b i : ℚ)
    calc
      _ = ∑ j ∈ s, (A i j : ℚ) * z j := Finset.sum_coe_sort s _
      _ = ∑ j, (A i j : ℚ) * z j := by
        apply Finset.sum_subset (Finset.subset_univ s)
        intro j _ hj
        have hzj : z j = 0 := by simpa [s, mem_support] using hj
        simp [hzj]
      _ = _ := congrFun hz i
  have hbnd := independent_integer_coordinate_bound C b (fun j : s => z j.1)
    H hcpos hb hcind hceq
  have hk : Fintype.card s ≤ n := by
    simpa using Fintype.card_le_of_injective (Subtype.val : s → Fin n) Subtype.val_injective
  have hbound : (Fintype.card s).factorial *
      (Fintype.card (Fin m) * H ^ 2) ^ Fintype.card s ≤ coordinateCap m n H := by
    unfold coordinateCap
    simp only [Fintype.card_fin]
    apply Nat.mul_le_mul (Nat.factorial_le hk)
    exact (Nat.pow_le_pow_left (Nat.le_add_right _ _) _).trans
      (Nat.pow_le_pow_right (by omega) hk)
  have hbpos : 0 < coordinateCap m n H := by unfold coordinateCap; positivity
  intro j
  by_cases hj : j ∈ s
  · exact ⟨(hbnd ⟨j, hj⟩).1.trans hbound, (hbnd ⟨j, hj⟩).2.trans hbound⟩
  · have hzj : z j = 0 := by simpa [s, mem_support] using hj
    simp only [hzj, Rat.num_zero, Rat.den_zero, Int.natAbs_zero]
    omega

/-- All successive minima have the original system's determinant bound.
Earlier recovered coordinates do not cause repeated growth of the bound. -/
theorem exists_bounded_lex_point {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (H : ℕ) (hC : ∀ i j, (C i j).natAbs ≤ H)
    (hb : ∀ i, (b i).natAbs ≤ H)
    (hf : ∃ x, Feasible (C.map (fun a => (a : ℚ))) (fun i => (b i : ℚ)) x) :
    ∃ x : Fin n → ℚ,
      Feasible (C.map (fun a => (a : ℚ))) (fun i => (b i : ℚ)) x ∧
      (∀ j, (x j).num.natAbs ≤ coordinateCap m n H ∧ (x j).den ≤ coordinateCap m n H) ∧
      ∀ i, ∀ y, PrimalFeasible
        (toReal (equationProgram (C.map (fun a => (a : ℚ))) (fun i => (b i : ℚ)))) y →
        (∀ j, j < i → y j = (x j : ℝ)) → (x i : ℝ) ≤ y i := by
  let A := C.map (fun a => (a : ℚ))
  let d := fun i => (b i : ℚ)
  obtain ⟨x₀, hx₀⟩ := hf
  have hfP : IsFeasible (toReal (equationProgram A d)) :=
    ⟨realVector x₀, (cast_standard_feasible A d x₀).mp hx₀⟩
  obtain ⟨x, hx, hlex⟩ := exists_partial_lex_minimum (equationProgram A d) hfP n le_rfl
  have hxf := (cast_standard_feasible A d x).mpr hx
  have hlexRat : LexMinimum A d x := by
    refine ⟨hxf, fun y hy i hprior => ?_⟩
    have h := hlex i i.isLt (realVector y) ((cast_standard_feasible A d y).mp hy)
      (fun j hj => by change (y j : ℝ) = (x j : ℝ); rw [hprior j hj])
    exact (Rat.cast_le (K := ℝ)).mp h
  have hind := lexMinimum_independent A d x hlexRat
  refine ⟨x, hxf, independent_support_coordinate_bound C b x H hC hb hxf.2 hind, ?_⟩
  exact fun i => hlex i i.isLt

end Lax109476Proofs.LexicographicBounds

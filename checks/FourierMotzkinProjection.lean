import Lax109476Proofs.Farkas

/-! Regression for the projected feasible set of u+t ≤ 0, -t ≤ 0.
The registered proof must preserve the particular retained value u. In
particular, u=1 must be excluded, which the former feasibility-only
specification did not require. These examples are kernel-checked proofs.
-/
namespace Checks.FourierMotzkinProjection

private def A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, -1]

private theorem extension_iff (u : ℝ) :
    (∃ t : ℝ, A.mulVec (Fin.lastCases t (fun _ : Fin 1 => u)) ≤ 0) ↔ u ≤ 0 := by
  have hfirst : ∀ t : ℝ, Fin.lastCases t (fun _ : Fin 1 => u) (0 : Fin 2) = u := by
    intro t
    change Fin.lastCases t (fun _ : Fin 1 => u) (Fin.castSucc (0 : Fin 1)) = u
    exact Fin.lastCases_castSucc _
  have hlast : ∀ t : ℝ, Fin.lastCases t (fun _ : Fin 1 => u) (1 : Fin 2) = t := by
    intro t
    change Fin.lastCases t (fun _ : Fin 1 => u) (Fin.last 1) = t
    exact Fin.lastCases_last
  constructor
  · rintro ⟨t, ht⟩
    have h0 := ht 0
    have h1 := ht 1
    norm_num [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hfirst, hlast] at h0 h1
    linarith
  · intro hu
    refine ⟨0, fun i => ?_⟩
    fin_cases i <;> simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hfirst, hlast, hu]

/-- The actual registered proof gives precisely u ≤ 0 after elimination. -/
example : ∃ κ : Type, ∃ _ : Fintype κ, ∃ M : Matrix κ (Fin 2) ℝ,
    (∀ i j, 0 ≤ M i j) ∧
    (∀ i, (M * A) i (Fin.last 1) = 0) ∧
    (∀ u : ℝ,
      (M * (A.submatrix id Fin.castSucc)).mulVec (fun _ => u) ≤ M.mulVec 0 ↔ u ≤ 0) := by
  obtain ⟨κ, inst, M, hM, hzero, hprojection⟩ :=
    Lax109476Proofs.Farkas.fourier_motzkin (Fin 2) 1 A 0
  exact ⟨κ, inst, M, hM, hzero, fun u => (hprojection _).trans (extension_iff u)⟩

/-- The zero matrix from the review fails the strengthened specification. -/
example : ¬ (∀ u : ℝ,
    ((0 : Matrix (Fin 1) (Fin 2) ℝ) * (A.submatrix id Fin.castSucc)).mulVec
        (fun _ => u) ≤ (0 : Matrix (Fin 1) (Fin 2) ℝ).mulVec 0 ↔
      ∃ t : ℝ, A.mulVec (Fin.lastCases t (fun _ : Fin 1 => u)) ≤ 0) := by
  intro h
  have hbad := (extension_iff 1).mp ((h 1).mp (by simp))
  norm_num at hbad

end Checks.FourierMotzkinProjection

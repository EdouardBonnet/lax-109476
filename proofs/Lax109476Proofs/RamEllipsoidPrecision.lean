import Lax109476Proofs.RamEllipsoidCoefficients

namespace Lax109476Proofs.RamEllipsoidPrecision

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamEllipsoidScalars RamFrame

def preparePrecision : Com := .seq epsilonDenominator precisionGrid

theorem preparePrecision_spec (B k n : ℕ)
    (hE : 2 ^ (2 * n + 4) < B) (hD : 2 ^ (2 * k + 3 * n + 9) < B) :
    Spec B (fun σ => σ.vars "vec.n" = n ∧ σ.vars "iter.k" = k) preparePrecision
      (fun σ τ => τ.vars "ell.epsden" = 2 ^ (2 * n + 4) ∧
        τ.vars "grid.D" = 2 ^ (2 * k + 3 * n + 9) ∧ τ.vars "vec.n" = n ∧
        τ.vars "iter.k" = k ∧ τ.arrs = σ.arrs) 20 := by
  have heps := spec_with_fields ["vec.n", "iter.k"] (epsilonDenominator_spec B n hE)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp [epsilonDenominator, Com.wvars])
    (by simp [epsilonDenominator, Com.warrs])
  have hgrid := spec_with_fields ["vec.n", "iter.k", "ell.epsden"] (precisionGrid_spec B k n hD)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> simp [precisionGrid, Com.wvars])
    (by simp [precisionGrid, Com.warrs])
  rintro σ ⟨hσn, hσk⟩
  run_vcg [heps, hgrid]
  all_goals clear heps hgrid
  all_goals simp_all [FieldsAgree, precisionGrid_value]

theorem precision_form_frame {B K : ℕ} {σ τ : Env} (hr : Run B preparePrecision σ τ K)
    (q : ℚ) (hσ : RamEllipsoidForm.FormOutput q σ) : RamEllipsoidForm.FormOutput q τ := by
  have hs := hr.frame_var "ell.form.s" (by simp [preparePrecision, epsilonDenominator, precisionGrid, Com.wvars])
  have hn := hr.frame_var "ell.form.n" (by simp [preparePrecision, epsilonDenominator, precisionGrid, Com.wvars])
  have hd := hr.frame_var "ell.form.d" (by simp [preparePrecision, epsilonDenominator, precisionGrid, Com.wvars])
  simpa only [RamEllipsoidForm.FormOutput, hs, hn, hd] using hσ

end Lax109476Proofs.RamEllipsoidPrecision

import Lax808846Proofs.Spec

namespace Lax109476Proofs.RamFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def FieldsAgree (fields : List String) (σ τ : Env) : Prop :=
  ∀ x ∈ fields, τ.vars x = σ.vars x

theorem fieldsAgree_trans (fields : List String) (σ τ υ : Env)
    (hστ : FieldsAgree fields σ τ) (hτυ : FieldsAgree fields τ υ) : FieldsAgree fields σ υ :=
  fun x hx => (hτυ x hx).trans (hστ x hx)

/-- Preserve the selected loop fields and all arrays around an arithmetic
phase, without expanding the phase's implementation at each call site. -/
theorem spec_with_fields {B K : ℕ} {c : Com} {P : Env → Prop} {Q : Env → Env → Prop}
    (fields : List String) (h : Spec B P c Q K)
    (hf : ∀ x ∈ fields, x ∉ c.wvars) (ha : c.warrs = []) :
    Spec B P c (fun σ τ => Q σ τ ∧ FieldsAgree fields σ τ ∧ τ.arrs = σ.arrs) K := by
  intro σ hσ
  obtain ⟨τ, hr, hτ⟩ := h σ hσ
  refine ⟨τ, hr, hτ, fun x hx => hr.frame_var x (hf x hx), ?_⟩
  funext a
  exact hr.frame_arr a (by simp [ha])

end Lax109476Proofs.RamFrame

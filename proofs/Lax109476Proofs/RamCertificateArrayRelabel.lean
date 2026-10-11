import Lax109476Proofs.RamArrayRelabel
import Lax109476Proofs.RamCertificateSource

namespace Lax109476Proofs.RamCertificateArrayRelabel

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def sourceNames : List String := ["source.A.s", "source.A.n", "source.A.d",
  "source.b.s", "source.b.n", "source.b.d", "source.c.s", "source.c.n", "source.c.d"]

def relabel (name a : String) : String := if a ∈ sourceNames then a else name ++ a

/-- A sufficiently long fixed prefix isolates workspace arrays while keeping
the immutable original coefficients shared between the certificate branches. -/
theorem relabel_injective (name : String) (hname : ∀ a ∈ sourceNames, a.length < name.length) :
    Function.Injective (relabel name) := by
  intro a b hab
  by_cases ha : a ∈ sourceNames <;> by_cases hb : b ∈ sourceNames
  · simpa [relabel, ha, hb] using hab
  · have he : a = name ++ b := by simpa [relabel, ha, hb] using hab
    have hl := congrArg String.length he
    have hh := hname a ha
    simp only [String.length_append] at hl
    omega
  · have he : name ++ a = b := by simpa [relabel, ha, hb] using hab
    have hl := congrArg String.length he
    have hh := hname b hb
    simp only [String.length_append] at hl
    omega
  · exact (String.append_right_inj name).mp (by simpa [relabel, ha, hb] using hab)

def isolated (name : String) (c : Com) : Com := RamArrayRelabel.command (relabel name) c

theorem spec_isolated {B K : ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {c : Com}
    (name : String) (hname : ∀ a ∈ sourceNames, a.length < name.length) (h : Spec B P c Q K) :
    Spec B (fun σ => P (RamArrayRelabel.view (relabel name) σ)) (isolated name c)
      (fun σ τ => Q (RamArrayRelabel.view (relabel name) σ) (RamArrayRelabel.view (relabel name) τ)) K :=
  RamArrayRelabel.spec_relabel _ (relabel_injective name hname) h

@[simp] theorem source_data_view {m n : ℕ} (P : Program ℤ m n) (name : String) (σ : Env) :
    RamCertificateSource.Data P (RamArrayRelabel.view (relabel name) σ) ↔ RamCertificateSource.Data P σ := by
  simp [RamCertificateSource.Data, RamRationalArrays.Represents, RamArrayRelabel.view, relabel, sourceNames]

@[simp] theorem command_wvars (f : String → String) (c : Com) :
    (RamArrayRelabel.command f c).wvars = c.wvars := by
  induction c <;> simp_all [RamArrayRelabel.command, Com.wvars]

@[simp] theorem command_warrs (f : String → String) (c : Com) :
    (RamArrayRelabel.command f c).warrs = c.warrs.map f := by
  induction c <;> simp_all [RamArrayRelabel.command, Com.warrs, List.map_append]

theorem source_not_written (name : String) (hname : ∀ a ∈ sourceNames, a.length < name.length)
    (c : Com) (a : String) (ha : a ∈ sourceNames) (hc : a ∉ c.warrs) :
    a ∉ (isolated name c).warrs := by
  simp only [isolated, command_warrs, List.mem_map]
  rintro ⟨b, hb, he⟩
  have haeq : relabel name a = a := by simp [relabel, ha]
  have hba : b = a := relabel_injective name hname (he.trans haeq.symm)
  exact hc (hba ▸ hb)

theorem optimal_prefix : ∀ a ∈ sourceNames, a.length < "optimal.recovery.".length := by
  intro a ha; simp [sourceNames] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem infeasible_prefix : ∀ a ∈ sourceNames, a.length < "infeasible.recovery.".length := by
  intro a ha; simp [sourceNames] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem unbounded_prefix : ∀ a ∈ sourceNames, a.length < "unbounded.recovery.".length := by
  intro a ha; simp [sourceNames] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end Lax109476Proofs.RamCertificateArrayRelabel

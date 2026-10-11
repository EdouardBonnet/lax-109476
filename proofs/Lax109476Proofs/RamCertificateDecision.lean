import Lax109476Proofs.RamFamilyQueryCopy
import Lax109476Proofs.RamFeasibilityFlags
import Lax109476Proofs.RamStoredFeasibilityBounds
import Lax109476Proofs.RamCertificateArrayRelabel
import Lax109476Proofs.RamEquationData
import Lax109476Proofs.RecoveryArithmeticBounds

namespace Lax109476Proofs.RamCertificateDecision

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RationalArithmeticBounds IntegerEncoding

def prefixedView (name : String) (σ : Env) : Env := RamArrayRelabel.view (fun a => name ++ a) σ

def prepare (source target : String) : Com := RamFamilyQueryCopy.copy
  (source ++ "system.A") (source ++ "system.b") (target ++ "lp.A") (target ++ "lp.b") (target ++ "lp.c")

def decideFeasible (source target : String) : Com := .seq (prepare source target)
  (RamArrayRelabel.prefixed target RamStoredFeasibility.decideFeasible)

def sizeBound (r s S : ℕ) : ℕ := r + s + 2 + (r * s + r + s) * (4 + 2 * (2 * S + 1))
def instructionBound (r s S : ℕ) : ℕ := 71 * (r * s + r) + 33 * s + 80 +
  RamStoredFeasibility.instructionBound (sizeBound r s S)

def Input {r s : ℕ} (F : Program ℤ r s) (source target : String) (σ : Env) : Prop :=
  RamEquationData.Data F (prefixedView source σ) ∧
    Extents (target ++ "lp.A") (r * s) σ ∧ Extents (target ++ "lp.b") r σ ∧ Extents (target ++ "lp.c") s σ ∧
    Extents (target ++ "int.A") (r * s) σ ∧ Extents (target ++ "int.b") r σ ∧ Extents (target ++ "int.c") s σ ∧
    RamFeasibilityQuery.Workspace r s (prefixedView target σ)

theorem extents_view_of_run {B k : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ k)
    (name a : String) (n : ℕ) (hσ : Extents a n (prefixedView name σ)) :
    Extents a n (prefixedView name τ) := by
  obtain ⟨_, _, hstep⟩ := hr.bigStep
  intro t ht
  change (τ.arrs (name ++ (a ++ t))).length = n
  rw [RamAdvanceState.array_length_of_bigStep hstep]
  exact hσ t ht

theorem workspace_view_of_run {B k : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ k)
    (name : String) (r s : ℕ) (hσ : RamFeasibilityQuery.Workspace r s (prefixedView name σ)) :
    RamFeasibilityQuery.Workspace r s (prefixedView name τ) := by
  obtain ⟨_, _, hstep⟩ := hr.bigStep
  have hlen := RamAdvanceState.array_length_of_bigStep hstep
  simpa only [RamFeasibilityQuery.Workspace, RamEllipsoidStep.Workspace, Extents,
    prefixedView, RamArrayRelabel.view, hlen] using hσ

theorem family_size {r s : ℕ} (F : Program ℤ r s) (S : ℕ)
    (hA : ∀ i j, (F.A i j).natAbs ≤ 2 ^ (2 * S)) (hb : ∀ i, (F.b i).natAbs ≤ 2 ^ (2 * S))
    (hc : ∀ j, F.c j = 0) : bitSize (encodeProgram (rationalProgram F)) ≤ sizeBound r s S := by
  have hH : 1 ≤ 2 ^ (2 * S) := Nat.one_le_pow _ _ (by decide)
  simpa only [sizeBound, Nat.size_pow] using RecoveryArithmeticBounds.program_height_size (rationalProgram F)
    (2 ^ (2 * S)) (fun i j => ⟨by simpa [rationalProgram] using hA i j, by simpa [rationalProgram] using hH⟩)
    (fun i => ⟨by simpa [rationalProgram] using hb i, by simpa [rationalProgram] using hH⟩)
    (fun j => by simpa [rationalProgram, hc j, Height] using hH)

theorem decide_wvars (source target : String) :
    (decideFeasible source target).wvars = (decideFeasible "" "").wvars := by
  simp [decideFeasible, prepare, RamFamilyQueryCopy.copy_wvars, RamArrayRelabel.prefixed,
    RamCertificateArrayRelabel.command_wvars, Com.wvars]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
theorem decideFeasible_spec (r s S w : ℕ) (F : Program ℤ r s) (source target : String)
    (hMB : 2 ^ (2 * S) < 2 ^ w) (hB : r * s + r + s + 4 < 2 ^ w)
    (hw : RamStoredFeasibility.wordWidth (sizeBound r s S) ≤ w)
    (hA : ∀ i j, (F.A i j).natAbs ≤ 2 ^ (2 * S)) (hb : ∀ i, (F.b i).natAbs ≤ 2 ^ (2 * S))
    (hc : ∀ j, F.c j = 0)
    (hAA : RamCopy.Disjoint (source ++ "system.A") (target ++ "lp.A"))
    (hBA : RamCopy.Disjoint (source ++ "system.b") (target ++ "lp.A"))
    (hBB : RamCopy.Disjoint (source ++ "system.b") (target ++ "lp.b"))
    (hFrameA : ∀ t ∈ RamCopy.suffixes, source ++ ("system.A" ++ t) ∉ (decideFeasible source target).warrs)
    (hFrameB : ∀ t ∈ RamCopy.suffixes, source ++ ("system.b" ++ t) ∉ (decideFeasible source target).warrs) :
    Spec (2 ^ w) (Input F source target) (decideFeasible source target)
      (fun _ τ => RamEquationData.Data F (prefixedView source τ) ∧
        RamBisectionCommit.condition.evalB (2 ^ w) τ = some (RationalFeasibilityDecision.feasible (rationalProgram F)))
      (instructionBound r s S) := by
  have hH : 1 ≤ 2 ^ (2 * S) := Nat.one_le_pow _ _ (by decide)
  have h1 : 1 < 2 ^ w := hH.trans_lt hMB
  have hsize := family_size F S hA hb hc
  have hwidth := (RamStoredFeasibilityBounds.wordWidth_monotone hsize).trans hw
  have hcopy := RamFamilyQueryCopy.copy_spec (2 ^ w) (2 ^ (2 * S)) r s (rationalProgram F)
    (source ++ "system.A") (source ++ "system.b") (target ++ "lp.A") (target ++ "lp.b") (target ++ "lp.c")
    h1 hMB hB
    (fun i j => ⟨by simpa [rationalProgram] using hA i j, by simpa [rationalProgram] using hH⟩)
    (fun i => ⟨by simpa [rationalProgram] using hb i, by simpa [rationalProgram] using hH⟩)
    (fun j => by simp [rationalProgram, hc j]) hAA hBA hBB
    (by simp [RamCopy.Disjoint, RamCopy.suffixes, List.mem_cons, List.mem_singleton, String.append_assoc])
    (by simp [RamCopy.Disjoint, RamCopy.suffixes, List.mem_cons, List.mem_singleton, String.append_assoc])
    (by simp [RamCopy.Disjoint, RamCopy.suffixes, List.mem_cons, List.mem_singleton, String.append_assoc])
  rintro σ ⟨hσData, hσlpA, hσlpb, hσlpc, hσintA, hσintb, hσintc, hσWork⟩
  have hσcopy : RamFamilyQueryCopy.Input (rationalProgram F)
      (source ++ "system.A") (source ++ "system.b") (target ++ "lp.A") (target ++ "lp.b") (target ++ "lp.c") σ := by
    rcases hσData with ⟨hσA, hσb, hσm, hσn⟩
    exact ⟨by simpa [prefixedView, RamArrayRelabel.view, Represents, String.append_assoc] using hσA,
      by simpa [prefixedView, RamArrayRelabel.view, Represents, String.append_assoc] using hσb,
      hσm, hσn, hσlpA, hσlpb, hσlpc⟩
  obtain ⟨τ, hr₁, hτcopy⟩ := hcopy σ hσcopy
  have hτP : RamStoredProgram.RepresentsProgram (rationalProgram F) (prefixedView target τ) := by
    simpa [RamFamilyQueryCopy.Output, RamStoredProgram.RepresentsProgram, prefixedView,
      RamArrayRelabel.view, Represents, String.append_assoc] using hτcopy
  have hτintA := RamAdvanceState.extents_of_run hr₁ _ _ hσintA
  have hτintb := RamAdvanceState.extents_of_run hr₁ _ _ hσintb
  have hτintc := RamAdvanceState.extents_of_run hr₁ _ _ hσintc
  have hτWork := workspace_view_of_run hr₁ target r s hσWork
  have hfeas := RamArrayRelabel.spec_prefixed target
    (RamStoredFeasibility.decideFeasible_condition_spec r s (rationalProgram F) w hwidth)
  obtain ⟨υ, hr₂, hυbool⟩ := hfeas τ ⟨hτP,
    by simpa [Extents, prefixedView, RamArrayRelabel.view, String.append_assoc] using hτintA,
    by simpa [Extents, prefixedView, RamArrayRelabel.view, String.append_assoc] using hτintb,
    by simpa [Extents, prefixedView, RamArrayRelabel.view, String.append_assoc] using hτintc, hτWork⟩
  have hr := hr₁.seq hr₂
  have hυm := (hr.frame_var "system.m" (by change "system.m" ∉ (decideFeasible source target).wvars; rw [decide_wvars]; decide)).trans hσData.2.2.1
  have hυn := (hr.frame_var "system.n" (by change "system.n" ∉ (decideFeasible source target).wvars; rw [decide_wvars]; decide)).trans hσData.2.2.2
  have hυA := RamReadBody.represents_frame (source ++ "system.A") _ hσcopy.1 hr
    (by intro t ht; change (source ++ "system.A") ++ t ∉ (decideFeasible source target).warrs; simpa [String.append_assoc] using hFrameA t (by simpa [RamCopy.suffixes] using ht))
  have hυb := RamReadBody.represents_frame (source ++ "system.b") _ hσcopy.2.1 hr
    (by intro t ht; change (source ++ "system.b") ++ t ∉ (decideFeasible source target).warrs; simpa [String.append_assoc] using hFrameB t (by simpa [RamCopy.suffixes] using ht))
  refine ⟨υ, hr.mono (Nat.add_le_add_left (RamStoredFeasibilityBounds.instructionBound_monotone hsize) _),
    ⟨?_, ?_, hυm, hυn⟩, ?_⟩
  · simpa [prefixedView, RamArrayRelabel.view, Represents, String.append_assoc] using hυA
  · simpa [prefixedView, RamArrayRelabel.view, Represents, String.append_assoc] using hυb
  · simpa [RamBisectionCommit.condition, prefixedView, RamArrayRelabel.view, Cond.evalB, Expr.evalB] using hυbool

end Lax109476Proofs.RamCertificateDecision

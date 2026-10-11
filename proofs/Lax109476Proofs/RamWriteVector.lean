import Lax109476Proofs.RamArrayResult
import Lax109476Proofs.RamReadBody
import Lax109476Proofs.RamEncoding
import Mathlib.Data.List.OfFn

namespace Lax109476Proofs.RamWriteVector

open Lax109476.RationalEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RationalArithmeticBounds

def increment : Com := .assign "output.i" (.add (.var "output.i") (.lit 1))
def step (a : String) : Com := .seq (.assign "vec.i" (.var "output.i"))
  (.seq (RamArrayResult.load a) (.seq RamEncoding.writeReducedFraction increment))

def Invariant (a : String) (xs : List ℚ) (O : List ℕ) (N : ℕ) (σ : Env) : Prop :=
  Represents a xs σ ∧ σ.vars "output.i" ≤ N ∧ σ.vars "output.count" = N ∧
    σ.out = O ++ (xs.take (σ.vars "output.i")).flatMap encodeRational

theorem step_spec (B M N : ℕ) (a : String) (xs : List ℚ) (O : List ℕ)
    (h1 : 1 < B) (hMB : M < B) (hNB : N < B) (hN : N ≤ xs.length)
    (hq : ∀ q ∈ xs, Height q M) :
    Spec B (fun σ => Invariant a xs O N σ ∧ σ.vars "output.i" < N) (step a)
      (fun σ τ => Invariant a xs O N τ ∧ τ.vars "output.i" = σ.vars "output.i" + 1) 31 := by
  rintro σ ⟨⟨hσa, hσi, hσcount, hσout⟩, hi⟩
  let i := σ.vars "output.i"
  have hil : i < xs.length := hi.trans_le hN
  have hiB : i < B := hi.trans hNB
  have hheight := hq xs[i] (List.getElem_mem hil)
  have hr₁ : Run B (.assign "vec.i" (.var "output.i")) σ (σ.setVar "vec.i" i) 2 :=
    Run.assign (evalB_var hiB)
  obtain ⟨τ, hr₂, hτq⟩ := RamArrayResult.load_spec B a xs i hil h1 hiB
    (hheight.1.trans_lt hMB) (hheight.2.trans_lt hMB) (σ.setVar "vec.i" i) ⟨hσa, by simp⟩
  obtain ⟨υ, hr₃, hυout⟩ := RamEncoding.writeReducedFraction_spec B xs[i] h1
    (hheight.1.trans_lt hMB) (hheight.2.trans_lt hMB) τ hτq
  have hυi : υ.vars "output.i" = i :=
    ((hr₁.seq (hr₂.seq hr₃)).frame_var _ (by
      change "output.i" ∉ (Com.seq (.assign "vec.i" (.var "output.i"))
        (.seq (RamArrayResult.load "") RamEncoding.writeReducedFraction)).wvars
      decide)).trans rfl
  have hsum : Bop.add.apply (υ.vars "output.i") 1 < B := by simpa [hυi] using (show i + 1 < B by dsimp only [i]; omega)
  have hr₄ : Run B increment υ (υ.setVar "output.i" (i + 1)) 4 :=
    Run.assign (by simpa only [hυi, Bop.apply_add] using (evalB_bin
      (evalB_var (B := B) (σ := υ) (x := "output.i") (hυi ▸ hiB)) (evalB_lit h1) hsum))
  let ρ := υ.setVar "output.i" (i + 1)
  have hr := hr₁.seq (hr₂.seq (hr₃.seq hr₄))
  have hτout : τ.out = σ.out := (hr₁.seq hr₂).out_eq (by
    change (Com.seq (.assign "vec.i" (.var "output.i")) (RamArrayResult.load "")).NoWrite
    decide)
  have hρout : ρ.out = O ++ (xs.take (i + 1)).flatMap encodeRational := by
    change υ.out = _
    rw [hυout, hτout, hσout, List.take_succ_eq_append_getElem hil, List.flatMap_append]
    simp [i, List.append_assoc]
  refine ⟨ρ, hr, ⟨RamReadBody.represents_frame _ _ hσa hr (by intro s hs; change _ ∉ ([] : List String); simp),
    ?_, (hr.frame_var "output.count" (by change "output.count" ∉ (step "").wvars; decide)).trans hσcount, ?_⟩, ?_⟩
  · change i + 1 ≤ N; dsimp only [i]; omega
  · simpa only [ρ, vars_setVar, ite_true] using hρout
  · simp [ρ, i]

/-- Emit a prefix of a stored rational vector in the registered canonical
encoding. Slack coordinates beyond the prefix remain internal. -/
def writePrefix (a : String) : Com := .seq (.assign "output.i" (.lit 0))
  (.while (.lt (.var "output.i") (.var "output.count")) (step a))

theorem writePrefix_spec (B M N : ℕ) (a : String) (xs : List ℚ)
    (h1 : 1 < B) (hMB : M < B) (hNB : N < B) (hN : N ≤ xs.length)
    (hq : ∀ q ∈ xs, Height q M) :
    Spec B (fun σ => Represents a xs σ ∧ σ.vars "output.count" = N) (writePrefix a)
      (fun σ τ => τ.out = σ.out ++ (xs.take N).flatMap encodeRational) (35 * N + 6) := by
  rintro σ ⟨hσa, hσcount⟩
  have hlo := Spec.forRangeZero "output.i" "output.count" (Invariant a xs σ.out N) N 31 hNB
    (fun _ h => h.2.1) (fun _ h => h.2.2.1) (step_spec B M N a xs σ.out h1 hMB hNB hN hq)
  obtain ⟨τ, hr, hτ, hcounter⟩ := hlo σ ⟨hσa, by simp, by simpa using hσcount, by simp⟩
  exact ⟨τ, hr, by simpa only [hcounter] using hτ.2.2.2⟩

theorem encodeVector_split {m n : ℕ} (z : Fin (m + n) → ℚ) :
    encodeVector z = encodeVector (fun i => z (Fin.castAdd n i)) ++ encodeVector (fun i => z (Fin.natAdd m i)) := by
  simp only [encodeVector, List.ofFn_add, List.flatMap_append]
  congr 2

end Lax109476Proofs.RamWriteVector

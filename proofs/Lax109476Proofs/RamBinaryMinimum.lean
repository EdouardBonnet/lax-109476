import Lax109476Proofs.RamBisectionLoop
import Lax109476Proofs.RamRationalReconstruction

namespace Lax109476Proofs.RamBinaryMinimum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalScalars RamScalarFrame RationalArithmeticBounds BinaryOptimization

def endpoints : Com := .seq (.assign "bisect.lo.s" (.lit 0))
  (.seq (.assign "bisect.lo.n" (.lit 0))
  (.seq (.assign "bisect.lo.d" (.lit 1))
  (.seq (.assign "bisect.hi.s" (.lit 0))
  (.seq (.assign "bisect.hi.n" (.var "minimum.bound"))
  (.seq (.assign "bisect.hi.d" (.lit 1))
    (.assign "bits.v" (.var "minimum.bound")))))))

def setLimit : Com := .assign "bisect.limit" (.add (.mul (.lit 3) (.var "bits.k")) (.lit 2))

def prepare : Com := .seq endpoints (.seq RamBitLength.bitLength setLimit)

def finish : Com := .seq (RamScalarCopy.copy "bisect.lo" "recon.lo")
  (.seq (RamScalarCopy.copy "bisect.hi" "recon.hi")
    (.seq (.assign "recon.bound" (.var "minimum.bound")) RamRationalReconstruction.reconstruct))

/-- A fixed RAM program computes a bounded rational minimum using threshold
queries, then continued-fraction reconstruction. -/
def minimum (query : Com) : Com := .seq prepare (.seq (RamBisectionLoop.loop query) finish)

theorem prepare_spec (B D : ℕ) (h3 : 3 < B) (hDB : D < B) (hKB : steps D < B) :
    Spec B (fun σ => σ.vars "minimum.bound" = D) prepare
      (fun _ τ => Value "bisect.lo" 0 τ ∧ Value "bisect.hi" D τ ∧
        τ.vars "bisect.limit" = steps D) (12 * D.size + 28) := by
  have hstart : Spec B (fun σ => σ.vars "minimum.bound" = D) endpoints
      (fun _ τ => Value "bisect.lo" 0 τ ∧ Value "bisect.hi" D τ ∧ τ.vars "bits.v" = D) 14 := by
    intro σ hσ
    run_vcg
    all_goals simp_all [Value, fractionValue]
  have hlimit : Spec B (fun σ => σ.vars "bits.k" = D.size) setLimit
      (fun _ τ => τ.vars "bisect.limit" = steps D) 6 := by
    intro σ hσ
    have hsize := RationalSizeBounds.size_le_self D
    run_vcg
    all_goals simp_all [steps]
    all_goals omega
  intro σ hσ
  obtain ⟨τ, hr₁, hτl, hτu, hτv⟩ := hstart σ hσ
  obtain ⟨υ, hr₂, _, hυk⟩ := RamBitLength.bitLength_spec B D (by omega) hDB τ hτv
  obtain ⟨ρ, hr₃, hρlimit⟩ := hlimit υ hυk
  refine ⟨ρ, (hr₁.seq (hr₂.seq hr₃)).mono (by omega), ?_, ?_, hρlimit⟩
  · exact value_frame (hr₂.seq hr₃) "bisect.lo" 0 hτl (by decide) (by decide) (by decide)
  · exact value_frame (hr₂.seq hr₃) "bisect.hi" D hτu (by decide) (by decide) (by decide)

theorem finish_spec (S N w D : ℕ) (l u : ℚ) (hu0 : 0 ≤ u)
    (hl : Height l (2 ^ S)) (hu : Height u (2 ^ S)) (hN : RamRationalReconstruction.depthBound S + 1 ≤ N)
    (hw : RamRationalReconstruction.wordWidth S ≤ w) (hDB : D < 2 ^ w) :
    Spec (2 ^ w) (fun σ => Value "bisect.lo" l σ ∧ Value "bisect.hi" u σ ∧
      σ.vars "minimum.bound" = D ∧ (σ.arrs "cf.stack").length = N) finish
      (fun _ τ => RamReconstructionRecord.Output (RationalReconstruction.reconstruct l u D) τ)
      (RamRationalReconstruction.instructionBound S + 14) := by
  have h1 : 1 < 2 ^ w := by
    have hp := Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ w by
      unfold RamRationalReconstruction.wordWidth RamConvergentBounds.wordWidth at hw; omega)
    norm_num at hp; omega
  have hHB : 2 ^ S < 2 ^ w := Nat.pow_lt_pow_right (by decide) (by
    unfold RamRationalReconstruction.wordWidth RamConvergentBounds.wordWidth
      RamConvergentBounds.exponent RamDecoder.wordWidth RamRationalReconstruction.depthBound at hw
    nlinarith)
  have hcopyl := RamScalarCopy.copy_spec (2 ^ w) "bisect.lo" "recon.lo" l h1
    (hl.1.trans_lt hHB) (hl.2.trans_lt hHB) (by simp [RamCopy.Disjoint, RamCopy.suffixes])
  have hcopyu := RamScalarCopy.copy_spec (2 ^ w) "bisect.hi" "recon.hi" u h1
    (hu.1.trans_lt hHB) (hu.2.trans_lt hHB) (by simp [RamCopy.Disjoint, RamCopy.suffixes])
  have hreconstruct := RamRationalReconstruction.reconstruct_spec S N w D l u hu0 hl hu hN hw hDB
  rintro σ ⟨hσl, hσu, hσD, hσN⟩
  obtain ⟨τ, hr₁, hτl⟩ := hcopyl σ hσl
  have hτu := value_frame hr₁ "bisect.hi" u hσu (by decide) (by decide) (by decide)
  obtain ⟨υ, hr₂, hυu⟩ := hcopyu τ hτu
  have hυl := value_frame hr₂ "recon.lo" l hτl (by decide) (by decide) (by decide)
  have hυD := ((hr₁.seq hr₂).frame_var "minimum.bound" (by decide)).trans hσD
  have hυN : (υ.arrs "cf.stack").length = N := by
    rw [(hr₁.seq hr₂).frame_arr _ (by decide)]; exact hσN
  have hr₃ : Run (2 ^ w) (.assign "recon.bound" (.var "minimum.bound")) υ (υ.setVar "recon.bound" D) 2 :=
    Run.assign (by simpa only [hυD] using (evalB_var (B := 2 ^ w) (σ := υ) (x := "minimum.bound")
      (hυD ▸ hDB)))
  obtain ⟨ρ, hr₄, hρ⟩ := hreconstruct (υ.setVar "recon.bound" D)
    ⟨value_frame hr₃ "recon.lo" l hυl (by decide) (by decide) (by decide),
      value_frame hr₃ "recon.hi" u hυu (by decide) (by decide) (by decide), by simp,
      by simpa only [arrs_setVar] using hυN⟩
  exact ⟨ρ, (hr₁.seq (hr₂.seq (hr₃.seq hr₄))).mono (by omega), hρ⟩

set_option maxHeartbeats 1000000 in
theorem minimum_spec (S N w D M queryCost : ℕ) (query : ℚ → Bool) (queryCom : Com) (Q : Env → Prop)
    (hB : 4 * M ^ 2 + 3 < 2 ^ w) (hKB : steps D < 2 ^ w)
    (hM : (D + 1) * 2 ^ steps D ≤ M) (hMS : M ≤ 2 ^ S)
    (hN : RamRationalReconstruction.depthBound S + 1 ≤ N)
    (hw : RamRationalReconstruction.wordWidth S ≤ w) (hDB : D < 2 ^ w)
    (hquery : ∀ t, Height t (4 * M ^ 2) → Spec (2 ^ w) (fun σ => Q σ ∧ Value "bisect.mid" t σ) queryCom
      (fun _ τ => Q τ ∧ RamBisectionCommit.condition.evalB (2 ^ w) τ = some (query t)) queryCost)
    (hfields : ∀ x ∈ RamBisectionLoop.fields, x ∉ queryCom.wvars)
    (hbound : "minimum.bound" ∉ queryCom.wvars)
    (hQmid : RamBisectionLoop.preserves (2 ^ w) Q RamRationalMidpoint.midpoint)
    (hQend : RamBisectionLoop.preserves (2 ^ w) Q (.seq RamBisectionCommit.commit RamBisectionLoop.increment))
    (hQinit : ∀ σ, Q σ → Q (σ.setVar "bisect.i" 0))
    (hQprepare : RamBisectionLoop.preserves (2 ^ w) Q prepare)
    (hQfinish : RamBisectionLoop.preserves (2 ^ w) Q finish) :
    Spec (2 ^ w) (fun σ => Q σ ∧ σ.vars "minimum.bound" = D ∧ (σ.arrs "cf.stack").length = N)
      (minimum queryCom) (fun _ τ => Q τ ∧ RamReconstructionRecord.Output (BinaryOptimization.minimum query D) τ)
      ((144 * M.size + 342 + queryCost) * steps D + 12 * D.size +
        RamRationalReconstruction.instructionBound S + 48) := by
  rintro σ ⟨hσQ, hσD, hσN⟩
  obtain ⟨τ, hr₁, hτl, hτu, hτlimit⟩ := prepare_spec (2 ^ w) D (by omega) hDB hKB σ hσD
  have hτQ := hQprepare hr₁ hσQ
  obtain ⟨υ, hr₂, hυQ, hυl, hυu⟩ := RamBisectionLoop.loop_spec (2 ^ w) M D (steps D) queryCost query queryCom Q
    hB hKB hM hquery hfields hQmid hQend hQinit τ ⟨hτQ, hτl, hτu, hτlimit⟩
  have hloopbound : "minimum.bound" ∉ (RamBisectionLoop.loop queryCom).wvars := by
    simp only [RamBisectionLoop.loop, RamBisectionLoop.body, Com.wvars, List.mem_append, not_or,
      List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨by decide, by decide, hbound, by decide, by decide⟩
  have hυD := (hr₂.frame_var _ hloopbound).trans ((hr₁.frame_var _ (by decide)).trans hσD)
  have hυN : (υ.arrs "cf.stack").length = N := by
    obtain ⟨_, _, hs⟩ := (hr₁.seq hr₂).bigStep
    exact (RamAdvanceState.array_length_of_bigStep hs "cf.stack").trans hσN
  obtain ⟨hl, hu⟩ := BinaryOptimizationBounds.bisect_height query D (steps D)
  have he := hM.trans hMS
  have hu0 := (BinaryOptimizationBounds.bisect_range query D (steps D)).1.trans
    (BinaryOptimizationBounds.bisect_range query D (steps D)).2.1
  obtain ⟨ρ, hr₃, hρ⟩ := finish_spec S N w D _ _ hu0
    (height_mono _ hl he) (height_mono _ hu he) hN hw hDB υ ⟨hυl, hυu, hυD, hυN⟩
  refine ⟨ρ, (hr₁.seq (hr₂.seq hr₃)).mono (by omega), hQfinish hr₃ hυQ, ?_⟩
  exact hρ

end Lax109476Proofs.RamBinaryMinimum

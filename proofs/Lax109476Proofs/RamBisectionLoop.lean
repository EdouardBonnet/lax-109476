import Lax109476Proofs.RamBisectionCommit
import Lax109476Proofs.BinaryOptimizationBounds

namespace Lax109476Proofs.RamBisectionLoop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RamRationalScalars RamScalarFrame
open BinaryOptimization RamBisectionCommit

def fields : List String := ["bisect.lo.s", "bisect.lo.n", "bisect.lo.d",
  "bisect.hi.s", "bisect.hi.n", "bisect.hi.d", "bisect.mid.s", "bisect.mid.n", "bisect.mid.d",
  "bisect.i", "bisect.limit"]

def preserves (B : ℕ) (Q : Env → Prop) (c : Com) : Prop :=
  ∀ {σ τ k}, Run B c σ τ k → Q σ → Q τ

def increment : Com := .assign "bisect.i" (.add (.var "bisect.i") (.lit 1))

def body (query : Com) : Com := .seq RamRationalMidpoint.midpoint (.seq query (.seq commit increment))

def Invariant (query : ℚ → Bool) (D K : ℕ) (Q : Env → Prop) (σ : Env) : Prop :=
  Q σ ∧ Value "bisect.lo" (bisect query 0 D (σ.vars "bisect.i")).1 σ ∧
    Value "bisect.hi" (bisect query 0 D (σ.vars "bisect.i")).2 σ ∧
    σ.vars "bisect.i" ≤ K ∧ σ.vars "bisect.limit" = K

set_option maxHeartbeats 800000 in
/-- Binary search composes with a stored threshold query. The query restores
its persistent data and leaves the search registers untouched. -/
theorem body_spec (B M D K queryCost : ℕ) (query : ℚ → Bool) (queryCom : Com) (Q : Env → Prop)
    (hB : 4 * M ^ 2 + 3 < B) (hKB : K < B) (hM : (D + 1) * 2 ^ K ≤ M)
    (hquery : ∀ t, Height t (4 * M ^ 2) → Spec B (fun σ => Q σ ∧ Value "bisect.mid" t σ) queryCom
      (fun _ τ => Q τ ∧ condition.evalB B τ = some (query t)) queryCost)
    (hfields : ∀ x ∈ fields, x ∉ queryCom.wvars)
    (hQmid : preserves B Q RamRationalMidpoint.midpoint)
    (hQend : preserves B Q (.seq commit increment)) :
    Spec B (fun σ => Invariant query D K Q σ ∧ σ.vars "bisect.i" < K) (body queryCom)
      (fun σ τ => Invariant query D K Q τ ∧ τ.vars "bisect.i" = σ.vars "bisect.i" + 1)
      (144 * M.size + 338 + queryCost) := by
  have hMB : M < B := by nlinarith
  have h1 : 1 < B := by omega
  rintro σ ⟨⟨hσQ, hσl, hσu, hσi, hσK⟩, hi⟩
  let j := σ.vars "bisect.i"
  let old := bisect query 0 D j
  let mid := (old.1 + old.2) / 2
  have hbound : (D + 1) * 2 ^ j ≤ M := (Nat.mul_le_mul_left (D + 1)
    (Nat.pow_le_pow_right (by decide) hσi)).trans hM
  obtain ⟨hl, hu⟩ := BinaryOptimizationBounds.bisect_height query D j
  have hlM := height_mono _ hl hbound
  have huM := height_mono _ hu hbound
  have hmid : Height mid (4 * M ^ 2) := by
    have h := height_div (old.1 + old.2) 2 (2 * M * M) 2
      (height_add old.1 old.2 M M hlM huM) (by norm_num [Height])
    convert h using 1 <;> ring
  obtain ⟨τ, hr₁, hτmid⟩ := RamRationalMidpoint.midpoint_spec B M old.1 old.2 hB hlM huM σ ⟨hσl, hσu⟩
  have hτQ := hQmid hr₁ hσQ
  obtain ⟨υ, hr₂, hυQ, hυanswer⟩ := hquery mid hmid τ ⟨hτQ, hτmid⟩
  have hτl := value_frame hr₁ "bisect.lo" old.1 hσl (by decide) (by decide) (by decide)
  have hτu := value_frame hr₁ "bisect.hi" old.2 hσu (by decide) (by decide) (by decide)
  have hυl := value_frame hr₂ "bisect.lo" old.1 hτl
    (hfields _ (by simp [fields])) (hfields _ (by simp [fields])) (hfields _ (by simp [fields]))
  have hυu := value_frame hr₂ "bisect.hi" old.2 hτu
    (hfields _ (by simp [fields])) (hfields _ (by simp [fields])) (hfields _ (by simp [fields]))
  have hυmid := value_frame hr₂ "bisect.mid" mid hτmid
    (hfields _ (by simp [fields])) (hfields _ (by simp [fields])) (hfields _ (by simp [fields]))
  obtain ⟨ρ, hr₃, hρl, hρu⟩ := commit_spec B old.1 old.2 mid (query mid) h1
    (hmid.1.trans_lt (by omega)) (hmid.2.trans_lt (by omega)) υ ⟨hυl, hυu, hυmid, hυanswer⟩
  have hρi : ρ.vars "bisect.i" = j :=
    (hr₃.frame_var _ (by decide)).trans ((hr₂.frame_var _ (hfields _ (by simp [fields]))).trans
      (hr₁.frame_var _ (by decide)))
  have hjB : j < B := hi.trans hKB
  have hsumB : Bop.add.apply (ρ.vars "bisect.i") 1 < B := by
    simpa [hρi] using (show j + 1 < B by dsimp only [j]; omega)
  have hr₄ : Run B increment ρ (ρ.setVar "bisect.i" (j + 1)) 4 := Run.assign (by
    simpa only [hρi, Bop.apply_add] using (evalB_bin
      (evalB_var (B := B) (σ := ρ) (x := "bisect.i") (hρi ▸ hjB)) (evalB_lit h1) hsumB))
  have hresultl := value_frame hr₄ "bisect.lo" (if query mid then old.1 else mid) hρl (by decide) (by decide) (by decide)
  have hresultu := value_frame hr₄ "bisect.hi" (if query mid then mid else old.2) hρu (by decide) (by decide) (by decide)
  have hr := hr₁.seq (hr₂.seq (hr₃.seq hr₄))
  have hlimit : (ρ.setVar "bisect.i" (j + 1)).vars "bisect.limit" = K :=
    (hr₄.frame_var _ (by decide)).trans ((hr₃.frame_var _ (by decide)).trans
      ((hr₂.frame_var _ (hfields _ (by simp [fields]))).trans ((hr₁.frame_var _ (by decide)).trans hσK)))
  refine ⟨_, hr.mono (by omega), ⟨hQend (hr₃.seq hr₄) hυQ, ?_, ?_, ?_, hlimit⟩, ?_⟩
  · change Value "bisect.lo" (bisect query 0 D (j + 1)).1 _
    simpa only [bisect, apply_ite Prod.fst, Prod.fst] using hresultl
  · change Value "bisect.hi" (bisect query 0 D (j + 1)).2 _
    simpa only [bisect, apply_ite Prod.snd, Prod.snd] using hresultu
  · change j + 1 ≤ K; omega
  · simp [j]

def loop (query : Com) : Com := .seq (.assign "bisect.i" (.lit 0))
  (.while (.lt (.var "bisect.i") (.var "bisect.limit")) (body query))

theorem loop_spec (B M D K queryCost : ℕ) (query : ℚ → Bool) (queryCom : Com) (Q : Env → Prop)
    (hB : 4 * M ^ 2 + 3 < B) (hKB : K < B) (hM : (D + 1) * 2 ^ K ≤ M)
    (hquery : ∀ t, Height t (4 * M ^ 2) → Spec B (fun σ => Q σ ∧ Value "bisect.mid" t σ) queryCom
      (fun _ τ => Q τ ∧ condition.evalB B τ = some (query t)) queryCost)
    (hfields : ∀ x ∈ fields, x ∉ queryCom.wvars)
    (hQmid : preserves B Q RamRationalMidpoint.midpoint)
    (hQend : preserves B Q (.seq commit increment))
    (hQinit : ∀ σ, Q σ → Q (σ.setVar "bisect.i" 0)) :
    Spec B (fun σ => Q σ ∧ Value "bisect.lo" 0 σ ∧ Value "bisect.hi" D σ ∧ σ.vars "bisect.limit" = K)
      (loop queryCom) (fun _ τ => Q τ ∧ Value "bisect.lo" (bisect query 0 D K).1 τ ∧
        Value "bisect.hi" (bisect query 0 D K).2 τ)
      ((144 * M.size + 342 + queryCost) * K + 6) := by
  have hlo := Spec.forRangeZero "bisect.i" "bisect.limit" (Invariant query D K Q) K
    (144 * M.size + 338 + queryCost) hKB (fun _ h => h.2.2.2.1) (fun _ h => h.2.2.2.2)
    (body_spec B M D K queryCost query queryCom Q hB hKB hM hquery hfields hQmid hQend)
  refine ((hlo.pre ?_).post ?_).mono ?_
  · rintro σ ⟨hQ, hl, hu, hK⟩
    refine ⟨?_, ?_, ?_, by simp, ?_⟩
    · exact hQinit σ hQ
    · simpa [Value, vars_setVar, bisect] using hl
    · simpa [Value, vars_setVar, bisect] using hu
    · simpa using hK
  · rintro σ τ _ ⟨hτ, hcounter⟩
    dsimp only [Invariant] at hτ
    rw [hcounter] at hτ
    exact ⟨hτ.1, hτ.2.1, hτ.2.2.1⟩
  · exact le_of_eq (by ring)

end Lax109476Proofs.RamBisectionLoop

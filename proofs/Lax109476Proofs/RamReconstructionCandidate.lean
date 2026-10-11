import Lax109476Proofs.RamScalarFrame

namespace Lax109476Proofs.RamReconstructionCandidate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RamRationalScalars RamScalarFrame

def finish : Com :=
  .ite (.lt (.var "recon.bound") (.var "rat.d")) (.assign "recon.accept" (.lit 0))
    (.ite (.eq (.var "recon.lower") (.lit 1))
      (.assign "recon.accept" (.var "cmp.le")) (.assign "recon.accept" (.lit 0)))

theorem finish_spec (B D : ℕ) (l u r : ℚ) (h1 : 1 < B) (hDB : D < B) (hrd : r.den < B) :
    Spec B (fun σ => σ.vars "recon.bound" = D ∧ σ.vars "rat.d" = r.den ∧
      σ.vars "recon.lower" = (if l ≤ r then 1 else 0) ∧ σ.vars "cmp.le" = (if r ≤ u then 1 else 0))
      finish (fun _ τ => τ.vars "recon.accept" = (if r.den ≤ D ∧ l ≤ r ∧ r ≤ u then 1 else 0)) 18 := by
  rintro σ ⟨hD, hd, hl, hu⟩
  have hlow : σ.vars "recon.lower" < B := by rw [hl]; split_ifs <;> omega
  have hupper : σ.vars "cmp.le" < B := by rw [hu]; split_ifs <;> omega
  run_vcg
  all_goals split_ifs <;> simp_all <;> omega

def check : Com := .seq (readLeft "recon.lo")
  (.seq resultToRight (.seq RamComparison.compareFraction
    (.seq (.assign "recon.lower" (.var "cmp.le"))
      (.seq resultToLeft (.seq (readRight "recon.hi")
        (.seq RamComparison.compareFraction finish))))))

theorem flag_eq (v : ℕ) (p : Prop) [Decidable p] (hv : v ≤ 1) (he : v = 1 ↔ p) :
    v = (if p then 1 else 0) := by split_ifs <;> simp_all <;> omega

set_option maxHeartbeats 800000 in
theorem check_spec (B M D : ℕ) (l u r : ℚ) (hB : 2 * M ^ 2 + 3 < B) (hDB : D < B)
    (hl : Height l M) (hu : Height u M) (hr : Height r M) :
    Spec B (fun σ => Value "recon.lo" l σ ∧ Value "recon.hi" u σ ∧ FractionOutput r σ ∧
      σ.vars "recon.bound" = D) check
      (fun _ τ => τ.vars "recon.accept" = (if r.den ≤ D ∧ l ≤ r ∧ r ≤ u then 1 else 0) ∧
        FractionOutput r τ) 124 := by
  have h1 : 1 < B := by omega
  have hMB : M < B := by nlinarith
  rintro σ ⟨hσl, hσu, hσr, hσD⟩
  obtain ⟨τ, hr₁, hτl⟩ := readLeft_spec B "recon.lo" l h1 (hl.1.trans_lt hMB)
    (hl.2.trans_lt hMB) (by simp [RamCopy.Disjoint, RamCopy.suffixes]) σ hσl
  have hτr := fraction_frame hr₁ r hσr (by decide) (by decide) (by decide)
  obtain ⟨υ, hr₂, hυr⟩ := resultToRight_spec B r h1 (hr.1.trans_lt hMB) (hr.2.trans_lt hMB) τ hτr
  have hυl := left_frame hr₂ l hτl (by decide) (by decide) (by decide)
  obtain ⟨ρ, hr₃, hρflag⟩ := compare_spec B M l r hB hl hr υ ⟨hυl, hυr⟩
  have hρlo := flag_eq (ρ.vars "cmp.le") (l ≤ r) hρflag.1 hρflag.2
  have hρloB : ρ.vars "cmp.le" < B := hρflag.1.trans_lt h1
  have hr₄ : Run B (.assign "recon.lower" (.var "cmp.le")) ρ
      (ρ.setVar "recon.lower" (ρ.vars "cmp.le")) 2 := Run.assign (evalB_var hρloB)
  let ξ := ρ.setVar "recon.lower" (ρ.vars "cmp.le")
  have hξr := fraction_frame (hr₁.seq (hr₂.seq (hr₃.seq hr₄))) r hσr (by decide) (by decide) (by decide)
  obtain ⟨ζ, hr₅, hζr⟩ := resultToLeft_spec B r h1 (hr.1.trans_lt hMB) (hr.2.trans_lt hMB) ξ hξr
  have hζu := value_frame (hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq hr₅)))) "recon.hi" u hσu
    (by decide) (by decide) (by decide)
  obtain ⟨η, hr₆, hηu⟩ := readRight_spec B "recon.hi" u h1 (hu.1.trans_lt hMB)
    (hu.2.trans_lt hMB) (by simp [RamCopy.Disjoint, RamCopy.suffixes]) ζ hζu
  have hηr := left_frame hr₆ r hζr (by decide) (by decide) (by decide)
  obtain ⟨θ, hr₇, hθflag⟩ := compare_spec B M r u hB hr hu η ⟨hηr, hηu⟩
  have hθupper := flag_eq (θ.vars "cmp.le") (r ≤ u) hθflag.1 hθflag.2
  have hrun := hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq (hr₅.seq (hr₆.seq hr₇)))))
  have hθr := fraction_frame hrun r hσr (by decide) (by decide) (by decide)
  have hθD := (hrun.frame_var "recon.bound" (by decide)).trans hσD
  have hθlower : θ.vars "recon.lower" = (if l ≤ r then 1 else 0) := by
    rw [(hr₅.seq (hr₆.seq hr₇)).frame_var "recon.lower" (by decide)]
    exact hρlo
  obtain ⟨κ, hr₈, hκ⟩ := finish_spec B D l u r h1 hDB (hr.2.trans_lt hMB) θ
    ⟨hθD, hθr.2.2.1, hθlower, hθupper⟩
  exact ⟨κ, (hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq (hr₅.seq (hr₆.seq (hr₇.seq hr₈))))))).mono (by omega), hκ,
    fraction_frame hr₈ r hθr (by decide) (by decide) (by decide)⟩

end Lax109476Proofs.RamReconstructionCandidate

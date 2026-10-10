import Lax109476Proofs.RamFractionInterface
import Lax109476Proofs.RamFrame
import Lax109476Proofs.EllipsoidArithmeticBounds

namespace Lax109476Proofs.RamCenterCoordinate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface RamFrame RationalArithmeticBounds

/-- One stored center coordinate is rounded after the exact rational update. -/
def centerCoordinate : Com :=
  .seq (.assign "vec.i" (.var "center.i"))
    (.seq (loadLeft "ell.u")
      (.seq (.assign "vec.i" (.lit 2))
        (.seq (loadRight "ell.coeff")
          (.seq multiplyFraction
            (.seq resultToRight
              (.seq (.assign "vec.i" (.var "center.i"))
                (.seq (loadLeft "ell.center")
                  (.seq subtractFraction
                    (.seq resultToLeft (.seq RamRounding.roundFraction (storeReduced "ell.nextcenter")))))))))))

def centerCap (M : ℕ) : ℕ := 2 * (M + 1) ^ 4 + 1

theorem centerCap_bounds (M : ℕ) (hM : 1 ≤ M) :
    M ≤ centerCap M ∧ M ^ 2 ≤ centerCap M ∧ 2 * M ^ 3 ≤ centerCap M ∧
      2 * M ^ 4 + 1 ≤ centerCap M := by
  have hbase : 1 ≤ M + 1 := by omega
  have h₂ := (Nat.pow_le_pow_left (by omega : M ≤ M + 1) 2).trans
    (Nat.pow_le_pow_right hbase (by omega : 2 ≤ 4))
  have h₃ := (Nat.pow_le_pow_left (by omega : M ≤ M + 1) 3).trans
    (Nat.pow_le_pow_right hbase (by omega : 3 ≤ 4))
  have h₄ := Nat.pow_le_pow_left (by omega : M ≤ M + 1) 4
  have hm := le_self_pow hM (by decide : (2 : ℕ) ≠ 0)
  unfold centerCap
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

def loopFields : List String := ["center.i", "vec.n", "grid.D", "vec.i"]

theorem arithmetic_frames (c : Com)
    (hc : c ∈ [multiplyFraction, subtractFraction, resultToRight, resultToLeft, RamRounding.roundFraction]) :
    (∀ x ∈ loopFields, x ∉ c.wvars) ∧ c.warrs = [] := by
  simp at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals constructor
  all_goals try (intro x hx; simp [loopFields] at hx; rcases hx with rfl | rfl | rfl | rfl)
  all_goals simp [multiplyFraction, subtractFraction, negateRight, resultToRight, resultToLeft,
    RamRounding.roundFraction, addFraction, RamArithmetic.normalizeFraction, RamArithmetic.gcdLoop,
    RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.wvars, Com.warrs]

theorem framed_arithmetic {B K : ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {c : Com}
    (hc : c ∈ [multiplyFraction, subtractFraction, resultToRight, resultToLeft, RamRounding.roundFraction])
    (h : Spec B P c Q K) :
    Spec B P c (fun σ τ => Q σ τ ∧ FieldsAgree loopFields σ τ ∧ τ.arrs = σ.arrs) K :=
  spec_with_fields loopFields h (arithmetic_frames c hc).1 (arithmetic_frames c hc).2

set_option maxHeartbeats 1600000 in
theorem centerCoordinate_spec (B M D i : ℕ) (us cs gs next : List ℚ)
    (hiu : i < us.length) (hic : i < cs.length) (hig : 2 < gs.length) (hin : i < next.length)
    (hiB : i < B) (hM : 1 ≤ M) (hD : D ≤ M) (hDpos : 0 < D)
    (hu : Height us[i] M) (hc : Height cs[i] M) (hg : Height gs[2] M)
    (hB : 2 * (centerCap M) ^ 2 + 3 < B) :
    Spec B (fun σ => Represents "ell.u" us σ ∧ Represents "ell.center" cs σ ∧
        Represents "ell.coeff" gs σ ∧ Represents "ell.nextcenter" next σ ∧
        σ.vars "center.i" = i ∧ σ.vars "grid.D" = D)
      centerCoordinate
      (fun _ τ => Represents "ell.nextcenter"
          (next.set i (RationalRounding.roundDown (cs[i] - us[i] * gs[2]) D)) τ ∧
        Represents "ell.u" us τ ∧ Represents "ell.center" cs τ ∧ Represents "ell.coeff" gs τ)
      (180 * (centerCap M).size + 318) := by
  have hcaps := centerCap_bounds M hM
  have hSB : centerCap M < B := by nlinarith
  have h1 : 1 < B := by nlinarith
  have h2 : 2 < B := by nlinarith
  have hmB : M < B := hcaps.1.trans_lt hSB
  have hproduct := height_mul _ _ M M hu hg
  have hdiff := height_sub _ _ M (M * M) hc hproduct
  have hdiff' : Height (cs[i] - us[i] * gs[2]) (2 * M ^ 3) := by
    convert hdiff using 1
    ring
  have hround := EllipsoidArithmeticBounds.height_roundDown (cs[i] - us[i] * gs[2]) (2 * M ^ 3) D hdiff' hDpos
  have hfinal : Height (RationalRounding.roundDown (cs[i] - us[i] * gs[2]) D) (centerCap M) := by
    have hm := Nat.mul_le_mul_left (2 * M ^ 3) hD
    apply height_mono _ hround
    exact (by nlinarith : 2 * M ^ 3 * D + 1 ≤ 2 * M ^ 4 + 1) |>.trans hcaps.2.2.2
  have hprodS : Height (us[i] * gs[2]) (centerCap M) := by
    exact height_mono _ hproduct (by simpa only [pow_two] using hcaps.2.1)
  have hdiffS := height_mono _ hdiff' hcaps.2.2.1
  have huS := height_mono _ hu hcaps.1
  have hcS := height_mono _ hc hcaps.1
  have hgS := height_mono _ hg hcaps.1
  have hloadU := spec_with_fields loopFields
    ((loadLeft_spec B "ell.u" us i hiu h1 hiB (hu.1.trans_lt hmB) (hu.2.trans_lt hmB)).post
      (fun _ τ _ h => leftValue_of_output _ τ h))
    (by intro x hx; simp [loopFields] at hx; rcases hx with rfl | rfl | rfl | rfl <;> simp [loadLeft, Com.wvars])
    (by simp [loadLeft, Com.warrs])
  have hloadG := spec_with_fields (loopFields ++ ["left.s", "left.n", "left.d"])
    ((loadRight_spec B "ell.coeff" gs 2 hig h1 h2 (hg.1.trans_lt hmB) (hg.2.trans_lt hmB)).post
      (fun _ τ _ h => rightValue_of_output _ τ h))
    (by
      intro x hx
      simp [loopFields] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [loadRight, Com.wvars])
    (by simp [loadRight, Com.warrs])
  have hmul := framed_arithmetic (by simp) (multiply_spec B (centerCap M) us[i] gs[2] hB huS hgS)
  have hright := framed_arithmetic (by simp) (resultToRight_spec B (us[i] * gs[2]) h1
    (hprodS.1.trans_lt hSB) (hprodS.2.trans_lt hSB))
  have hloadC := spec_with_fields (loopFields ++ ["right.s", "right.n", "right.d"])
    ((loadLeft_spec B "ell.center" cs i hic h1 hiB (hc.1.trans_lt hmB) (hc.2.trans_lt hmB)).post
      (fun _ τ _ h => leftValue_of_output _ τ h))
    (by
      intro x hx
      simp [loopFields] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [loadLeft, Com.wvars])
    (by simp [loadLeft, Com.warrs])
  have hsub := framed_arithmetic (by simp) (subtract_spec B (centerCap M) cs[i] (us[i] * gs[2]) hB hcS hprodS)
  have hleft := framed_arithmetic (by simp) (resultToLeft_spec B (cs[i] - us[i] * gs[2]) h1
    (hdiffS.1.trans_lt hSB) (hdiffS.2.trans_lt hSB))
  have hroundSpec := framed_arithmetic (by simp) (round_spec B (centerCap M) D
    (cs[i] - us[i] * gs[2]) hB hdiffS (hD.trans hcaps.1) hDpos)
  have hstore := spec_with_write_frame loopFields
    (storeReduced_spec B "ell.nextcenter" next (RationalRounding.roundDown (cs[i] - us[i] * gs[2]) D)
      i hin h1 hiB (hfinal.1.trans_lt hSB) (hfinal.2.trans_lt hSB))
    (by intro x hx; simp [loopFields] at hx; rcases hx with rfl | rfl | rfl | rfl <;> simp [storeReduced, Com.wvars])
  rintro σ ⟨hσu, hσc, hσg, hσnext, hσi, hσD⟩
  run_vcg [hloadU, hloadG, hmul, hright, hloadC, hsub, hleft, hroundSpec, hstore]
  all_goals clear hloadU hloadG hmul hright hloadC hsub hleft hroundSpec hstore
  all_goals simp_all [LeftValue, RightValue, FractionOutput, Represents, FieldsAgree, loopFields, storeReduced, Com.warrs]
  all_goals aesop

end Lax109476Proofs.RamCenterCoordinate

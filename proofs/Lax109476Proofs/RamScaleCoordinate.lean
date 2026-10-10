import Lax109476Proofs.RamCopy
import Lax109476Proofs.RamFractionInterface

namespace Lax109476Proofs.RamScaleCoordinate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamFractionInterface RationalArithmeticBounds RamCopy

def prepareFactor : Com := .seq (.assign "right.s" (.lit 0))
  (.seq (.assign "right.n" (.var "scale.factor")) (.assign "right.d" (.lit 1)))

theorem prepareFactor_spec (B D : ℕ) (h1 : 1 < B) (hDB : D < B) :
    Spec B (fun σ => σ.vars "scale.factor" = D) prepareFactor
      (fun _ τ => RightValue (D : ℚ) τ) 6 := by
  rintro σ hσD
  run_vcg
  all_goals simp_all [RightValue, fractionValue]

def scaleFields : List String := ["scale.i", "scale.factor", "vec.i", "vec.n"]

def scaleCoordinate (a b : String) : Com := .seq (.assign "vec.i" (.var "scale.i"))
  (.seq (loadLeft a) (.seq prepareFactor (.seq RamRational.multiplyFraction (storeReduced b))))

set_option maxHeartbeats 500000 in
theorem scaleCoordinate_spec (B M i D : ℕ) (a b : String) (xs ys : List ℚ)
    (hi : i < xs.length) (hiy : i < ys.length) (hiB : i < B) (hM : 1 ≤ M)
    (hB : 2 * M ^ 2 + 3 < B) (hq : Height xs[i] M) (hD : D ≤ M) (hab : RamCopy.Disjoint a b) :
    Spec B (fun σ => Represents a xs σ ∧ Represents b ys σ ∧
        σ.vars "scale.i" = i ∧ σ.vars "scale.factor" = D)
      (scaleCoordinate a b)
      (fun _ τ => Represents b (ys.set i (xs[i] * (D : ℚ))) τ ∧ Represents a xs τ)
      (72 * M.size + 94) := by
  have h1 : 1 < B := by nlinarith
  have hMB : M < B := by nlinarith
  have hMMB : M * M < B := by nlinarith
  have hDH : Height (D : ℚ) M := by simpa [Height] using And.intro hD hM
  have hresult := height_mul xs[i] (D : ℚ) M M hq hDH
  have hload := spec_with_fields scaleFields
    (loadLeft_spec B a xs i hi h1 hiB (hq.1.trans_lt hMB) (hq.2.trans_lt hMB))
    (by intro x hx; simp [scaleFields] at hx; rcases hx with rfl | rfl | rfl | rfl <;> simp [loadLeft, Com.wvars])
    (by simp [loadLeft, Com.warrs])
  have hfactor := spec_with_fields (scaleFields ++ ["left.s", "left.n", "left.d"])
    (prepareFactor_spec B D h1 (hD.trans_lt hMB))
    (by intro x hx; simp [scaleFields] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [prepareFactor, Com.wvars]) (by simp [prepareFactor, Com.warrs])
  have hmul := spec_with_fields scaleFields (multiply_spec B M xs[i] (D : ℚ) hB hq hDH)
    (by intro x hx; simp [scaleFields] at hx; rcases hx with rfl | rfl | rfl | rfl <;> decide) (by decide)
  have hstore := spec_with_write_frame scaleFields
    (storeReduced_spec B b ys (xs[i] * (D : ℚ)) i hiy h1 hiB
      (hresult.1.trans_lt hMMB) (hresult.2.trans_lt hMMB))
    (by intro x hx; simp [scaleFields] at hx; rcases hx with rfl | rfl | rfl | rfl <;> simp [storeReduced, Com.wvars])
  rintro σ ⟨hσa, hσb, hσi, hσD⟩
  run_vcg [hload, hfactor, hmul, hstore]
  all_goals clear hload hfactor hmul hstore
  all_goals simp_all [scaleFields, FieldsAgree, Represents, LeftOutput, RightValue,
    LeftValue, FractionOutput, canonical_fractionValue, rationalSign_le_one,
    RamCopy.Disjoint, RamCopy.suffixes, storeReduced, Com.warrs]
  all_goals aesop

end Lax109476Proofs.RamScaleCoordinate

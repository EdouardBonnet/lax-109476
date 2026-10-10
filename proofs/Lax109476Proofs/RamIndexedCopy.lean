import Lax109476Proofs.RamCopy

namespace Lax109476Proofs.RamIndexedCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds RamCopy

def fields : List String := ["vec.i", "copy.target"]

/-- Copy one canonical rational between different indices, preserving the
source. This is used when adding columns and building certificate systems. -/
def copyAt (a b : String) : Com := .seq (loadLeft a)
  (.seq leftToResult (.seq (.assign "vec.i" (.var "copy.target")) (storeReduced b)))

set_option maxHeartbeats 600000 in
theorem copyAt_spec (B M i j : ℕ) (a b : String) (xs ys : List ℚ)
    (hi : i < xs.length) (hj : j < ys.length) (hiB : i < B) (hjB : j < B)
    (h1 : 1 < B) (hMB : M < B) (hq : Height xs[i] M) (hab : RamCopy.Disjoint a b) :
    Spec B (fun σ => Represents a xs σ ∧ Represents b ys σ ∧
        σ.vars "vec.i" = i ∧ σ.vars "copy.target" = j)
      (copyAt a b)
      (fun _ τ => Represents b (ys.set j xs[i]) τ ∧ Represents a xs τ ∧
        τ.vars "vec.i" = j ∧ τ.vars "copy.target" = j) 30 := by
  have hload := spec_with_fields fields
    (loadLeft_spec B a xs i hi h1 hiB (hq.1.trans_lt hMB) (hq.2.trans_lt hMB))
    (by intro x hx; simp [fields] at hx; rcases hx with rfl | rfl <;>
      simp [loadLeft, Com.wvars]) (by simp [loadLeft, Com.warrs])
  have hresult := spec_with_fields fields
    (leftToResult_spec B xs[i] h1 (hq.1.trans_lt hMB) (hq.2.trans_lt hMB))
    (by intro x hx; simp [fields] at hx; rcases hx with rfl | rfl <;>
      simp [leftToResult, Com.wvars]) (by simp [leftToResult, Com.warrs])
  have hstore := spec_with_write_frame fields
    (storeReduced_spec B b ys xs[i] j hj h1 hjB (hq.1.trans_lt hMB) (hq.2.trans_lt hMB))
    (by intro x hx; simp [fields] at hx; rcases hx with rfl | rfl <;>
      simp [storeReduced, Com.wvars])
  rintro σ ⟨hσa, hσb, hσi, hσj⟩
  run_vcg [hload, hresult, hstore]
  all_goals clear hload hresult hstore
  all_goals simp_all [RamCopy.Disjoint, suffixes, LeftOutput, FractionOutput, Represents,
    FieldsAgree, fields, storeReduced, Com.warrs]
  all_goals aesop

end Lax109476Proofs.RamIndexedCopy

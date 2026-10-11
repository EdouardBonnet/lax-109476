import Lax109476Proofs.RamFractionInterface
import Lax109476Proofs.RamFrame
import Lax109476Proofs.RamCopy

namespace Lax109476Proofs.RamRationalScalars

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RamRationalArrays

def Value (name : String) (q : ℚ) (σ : Env) : Prop :=
  fractionValue (σ.vars (name ++ ".s")) (σ.vars (name ++ ".n")) (σ.vars (name ++ ".d")) = q ∧
    σ.vars (name ++ ".n") = q.num.natAbs ∧ σ.vars (name ++ ".d") = q.den ∧
    σ.vars (name ++ ".s") ≤ 1

def readLeft (name : String) : Com := .seq (.assign "left.s" (.var (name ++ ".s")))
  (.seq (.assign "left.n" (.var (name ++ ".n"))) (.assign "left.d" (.var (name ++ ".d"))))

def readRight (name : String) : Com := .seq (.assign "right.s" (.var (name ++ ".s")))
  (.seq (.assign "right.n" (.var (name ++ ".n"))) (.assign "right.d" (.var (name ++ ".d"))))

def save (name : String) : Com := .seq (.assign (name ++ ".s") (.var "rat.s"))
  (.seq (.assign (name ++ ".n") (.var "rat.n")) (.assign (name ++ ".d") (.var "rat.d")))

theorem readLeft_spec (B : ℕ) (name : String) (q : ℚ) (h1 : 1 < B)
    (hn : q.num.natAbs < B) (hd : q.den < B) (hname : RamCopy.Disjoint name "left") :
    Spec B (Value name q) (readLeft name) (fun _ τ => LeftValue q τ) 6 := by
  have hsn : name ++ ".n" ≠ "left.s" := hname ".n" (by simp [RamCopy.suffixes]) ".s" (by simp [RamCopy.suffixes])
  have hsd : name ++ ".d" ≠ "left.s" := hname ".d" (by simp [RamCopy.suffixes]) ".s" (by simp [RamCopy.suffixes])
  have hnd : name ++ ".d" ≠ "left.n" := hname ".d" (by simp [RamCopy.suffixes]) ".n" (by simp [RamCopy.suffixes])
  rintro σ ⟨hval, hσn, hσd, hσs⟩
  have hs := hσs.trans_lt h1
  run_vcg
  all_goals simp_all [Value, LeftValue]

theorem readRight_spec (B : ℕ) (name : String) (q : ℚ) (h1 : 1 < B)
    (hn : q.num.natAbs < B) (hd : q.den < B) (hname : RamCopy.Disjoint name "right") :
    Spec B (Value name q) (readRight name) (fun _ τ => RightValue q τ) 6 := by
  have hsn : name ++ ".n" ≠ "right.s" := hname ".n" (by simp [RamCopy.suffixes]) ".s" (by simp [RamCopy.suffixes])
  have hsd : name ++ ".d" ≠ "right.s" := hname ".d" (by simp [RamCopy.suffixes]) ".s" (by simp [RamCopy.suffixes])
  have hnd : name ++ ".d" ≠ "right.n" := hname ".d" (by simp [RamCopy.suffixes]) ".n" (by simp [RamCopy.suffixes])
  rintro σ ⟨hval, hσn, hσd, hσs⟩
  have hs := hσs.trans_lt h1
  run_vcg
  all_goals simp_all [Value, RightValue]

/-- Saving to names outside the arithmetic result registers preserves the
reduced exact value, including the permitted sign encoding of zero. -/
theorem save_spec (B : ℕ) (name : String) (q : ℚ) (h1 : 1 < B)
    (hn : q.num.natAbs < B) (hd : q.den < B)
    (hname : ∀ s ∈ [".s", ".n", ".d"], ∀ t ∈ [".s", ".n", ".d"], name ++ s ≠ "rat" ++ t) :
    Spec B (FractionOutput q) (save name) (fun _ τ => Value name q τ) 6 := by
  have hsn : name ++ ".s" ≠ "rat.n" := hname ".s" (by simp) ".n" (by simp)
  have hsd : name ++ ".s" ≠ "rat.d" := hname ".s" (by simp) ".d" (by simp)
  have hnd : name ++ ".n" ≠ "rat.d" := hname ".n" (by simp) ".d" (by simp)
  have hsn' : name ++ ".s" ≠ name ++ ".n" := by simp
  have hsd' : name ++ ".s" ≠ name ++ ".d" := by simp
  have hnd' : name ++ ".n" ≠ name ++ ".d" := by simp
  rintro σ ⟨hval, hσn, hσd, hσs⟩
  have hs := hσs.trans_lt h1
  run_vcg
  all_goals simp_all [Value, FractionOutput, Ne.symm hsn, Ne.symm hsd, Ne.symm hnd,
    Ne.symm hsn', Ne.symm hsd', Ne.symm hnd']

end Lax109476Proofs.RamRationalScalars

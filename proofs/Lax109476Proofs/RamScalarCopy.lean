import Lax109476Proofs.RamScalarFrame

namespace Lax109476Proofs.RamScalarCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RamRationalScalars

def copy (a b : String) : Com := .seq (.assign (b ++ ".s") (.var (a ++ ".s")))
  (.seq (.assign (b ++ ".n") (.var (a ++ ".n"))) (.assign (b ++ ".d") (.var (a ++ ".d"))))

theorem copy_spec (B : ℕ) (a b : String) (q : ℚ) (h1 : 1 < B)
    (hn : q.num.natAbs < B) (hd : q.den < B) (hab : RamCopy.Disjoint a b) :
    Spec B (Value a q) (copy a b) (fun _ τ => Value b q τ) 6 := by
  have hsn : a ++ ".n" ≠ b ++ ".s" := hab ".n" (by simp [RamCopy.suffixes]) ".s" (by simp [RamCopy.suffixes])
  have hsd : a ++ ".d" ≠ b ++ ".s" := hab ".d" (by simp [RamCopy.suffixes]) ".s" (by simp [RamCopy.suffixes])
  have hnd : a ++ ".d" ≠ b ++ ".n" := hab ".d" (by simp [RamCopy.suffixes]) ".n" (by simp [RamCopy.suffixes])
  have hbSN : b ++ ".s" ≠ b ++ ".n" := by simp
  have hbSD : b ++ ".s" ≠ b ++ ".d" := by simp
  have hbND : b ++ ".n" ≠ b ++ ".d" := by simp
  rintro σ ⟨hval, hσn, hσd, hσs⟩
  have hs := hσs.trans_lt h1
  run_vcg
  all_goals simp_all [Value, Ne.symm hbSN, Ne.symm hbSD, Ne.symm hbND]

end Lax109476Proofs.RamScalarCopy

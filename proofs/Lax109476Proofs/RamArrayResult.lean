import Lax109476Proofs.RamScalarCopy

namespace Lax109476Proofs.RamArrayResult

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamScalarFrame RamRationalScalars

def load (a : String) : Com := .seq (loadLeft a) RamCopy.leftToResult

theorem load_spec (B : ℕ) (a : String) (xs : List ℚ) (i : ℕ) (hi : i < xs.length)
    (h1 : 1 < B) (hiB : i < B) (hn : xs[i].num.natAbs < B) (hd : xs[i].den < B) :
    Spec B (fun σ => Represents a xs σ ∧ σ.vars "vec.i" = i) (load a)
      (fun _ τ => FractionOutput xs[i] τ) 15 := by
  intro σ hσ
  obtain ⟨τ, hr₁, hτ⟩ := loadLeft_spec B a xs i hi h1 hiB hn hd σ hσ
  obtain ⟨υ, hr₂, hυ⟩ := RamCopy.leftToResult_spec B xs[i] h1 hn hd τ hτ
  exact ⟨υ, hr₁.seq hr₂, hυ⟩

theorem copyResult_spec (B : ℕ) (a : String) (q : ℚ) (h1 : 1 < B)
    (hn : q.num.natAbs < B) (hd : q.den < B) (ha : RamCopy.Disjoint a "rat") :
    Spec B (Value a q) (RamScalarCopy.copy a "rat") (fun _ τ => FractionOutput q τ) 6 := by
  refine (RamScalarCopy.copy_spec B a "rat" q h1 hn hd ha).post ?_
  intro σ τ _ hτ
  exact hτ

end Lax109476Proofs.RamArrayResult

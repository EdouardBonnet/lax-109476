import Lax109476Proofs.RamReadBody
import Lax109476Proofs.IntegerEncoding

namespace Lax109476Proofs.RamStoredProgram

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamFrame RamReadBlock

def RepresentsProgram {m n : ℕ} (P : Program ℚ m n) (σ : Env) : Prop :=
  Represents "lp.A" (RamMatrixStorage.flatten P.A) σ ∧
    Represents "lp.b" (List.ofFn P.b) σ ∧ Represents "lp.c" (List.ofFn P.c) σ ∧
    σ.vars "lp.m" = m ∧ σ.vars "lp.n" = n ∧ σ.vars "decode.count" = m * n

theorem representsProgram_frame {m n : ℕ} (P : Program ℚ m n) (σ τ : Env)
    (h : RepresentsProgram P σ) (ha : τ.arrs = σ.arrs) (hf : FieldsAgree fields σ τ) :
    RepresentsProgram P τ := by
  rcases h with ⟨hA, hb, hc, hm, hn, hcount⟩
  exact ⟨by simpa only [Represents, ha] using hA, by simpa only [Represents, ha] using hb,
    by simpa only [Represents, ha] using hc,
    (hf _ (by simp [fields])).trans hm, (hf _ (by simp [fields])).trans hn,
    (hf _ (by simp [fields])).trans hcount⟩

end Lax109476Proofs.RamStoredProgram

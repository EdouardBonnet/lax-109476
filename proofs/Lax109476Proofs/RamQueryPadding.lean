import Lax109476Proofs.RamPadBound

namespace Lax109476Proofs.RamQueryPadding

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamFrame RationalArithmeticBounds RamEllipsoidStep RamMatrixStorage

def padQuery : Com := .seq RamPadMatrix.padMatrix (.seq RamPadBound.padBound
  (.seq (.assign "query.m" (.add (.var "source.m") (.lit 2)))
    (.seq (.assign "query.n" (.add (.var "source.n") (.lit 2)))
      (.assign "query.bits" (.add (.var "source.bits") (.lit 4))))))

def Input {m n : ℕ} (P : Program ℚ m n) (S : ℕ) (σ : Env) : Prop :=
  Represents "query.A" (RamMatrixStorage.flatten P.A) σ ∧ Represents "query.b" (List.ofFn P.b) σ ∧
    Extents "pad.A" ((m + 2) * (n + 2)) σ ∧ Extents "pad.b" (m + 2) σ ∧
    σ.vars "source.m" = m ∧ σ.vars "source.n" = n ∧ σ.vars "source.bits" = S

def Output {m n : ℕ} (P : Program ℚ m n) (S : ℕ) (τ : Env) : Prop :=
  Represents "pad.A" (RamMatrixStorage.flatten (FeasibilityPadding.pad P).A) τ ∧
    Represents "pad.b" (List.ofFn (FeasibilityPadding.pad P).b) τ ∧
    Represents "query.A" (RamMatrixStorage.flatten P.A) τ ∧ Represents "query.b" (List.ofFn P.b) τ ∧
    τ.vars "query.m" = m + 2 ∧ τ.vars "query.n" = n + 2 ∧ τ.vars "query.bits" = S + 4

set_option maxHeartbeats 800000 in
theorem padQuery_spec (B M m n S : ℕ) (P : Program ℚ m n)
    (hM : 1 ≤ M) (hMB : M < B) (hdim : (m + 2) * (n + 2) + m + n + 4 < B)
    (hSB : S + 4 < B) (hA : ∀ i j, Height (P.A i j) M) (hb : ∀ i, Height (P.b i) M) :
    Spec B (Input P S) padQuery (fun _ τ => Output P S τ)
      (111 * ((m + 2) * (n + 2)) + 77 * (m + 2) + 78) := by
  have hmatrix := spec_with_write_frame ["source.m", "source.n", "source.bits"]
    (RamPadMatrix.padMatrix_spec B M m n P hM hMB hdim hA)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> decide)
  have hbound := spec_with_write_frame ["source.m", "source.n", "source.bits"]
    (RamPadBound.padBound_spec B M m n P hM hMB (by omega) hb)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> decide)
  have hmB : m + 2 < B := by omega
  have hnB : n + 2 < B := by omega
  have hm : m < B := by omega
  have hn : n < B := by omega
  have hS : S < B := by omega
  have hmatarrs : RamPadMatrix.padMatrix.warrs =
      ["pad.A.s", "pad.A.n", "pad.A.d", "pad.A.s", "pad.A.s", "pad.A.n", "pad.A.d"] := by rfl
  have hboundarrs : RamPadBound.padBound.warrs =
      ["pad.b.s", "pad.b.n", "pad.b.d", "pad.b.s", "pad.b.s", "pad.b.n", "pad.b.d"] := by rfl
  have h2 : 2 < B := by omega
  have h4 : 4 < B := by
    have hh : 4 ≤ (m + 2) * (n + 2) := by nlinarith
    omega
  rintro σ ⟨hσA, hσb, hσpadA, hσpadb, hσm, hσn, hσbits⟩
  have hbs := hσpadb ".s" (by simp)
  have hbn := hσpadb ".n" (by simp)
  have hbd := hσpadb ".d" (by simp)
  run_vcg [hmatrix, hbound]
  all_goals clear hmatrix hbound
  all_goals simp_all [Input, Output, FieldsAgree, Represents, Extents, hmatarrs, hboundarrs]
  all_goals aesop
  all_goals omega

end Lax109476Proofs.RamQueryPadding

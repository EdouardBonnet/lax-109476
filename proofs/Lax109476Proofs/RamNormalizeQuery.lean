import Lax109476Proofs.RamNormalizedMatrix
import Lax109476Proofs.RamNormalizedBound
import Lax109476Proofs.RamSearchBounds

namespace Lax109476Proofs.RamNormalizeQuery

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamMatrixStorage RamEllipsoidStep IntegerEncoding NormalizedFeasibility

def normalizeQuery : Com := .seq RamNormalizedMatrix.normalizeMatrix
  (.seq RamNormalizedBound.normalizeBound (.seq (.assign "vec.n" (.var "query.n"))
    (.assign "row.m" (.add (.var "query.m") (.var "query.n")))))

def Input {m n : ℕ} (P : Program ℤ m n) (R D N : ℕ) (σ : Env) : Prop :=
  Represents "pad.A" (RamMatrixStorage.flatten (rationalProgram P).A) σ ∧
    Represents "pad.b" (List.ofFn (rationalProgram P).b) σ ∧
    Extents "search.rows" ((m + n) * n) σ ∧ Extents "search.rhs" (m + n) σ ∧
    Extents "ell.center" n σ ∧ Extents "ell.shape" (n * n) σ ∧ Workspace n σ ∧
    Extents "ell.normal" n σ ∧ σ.vars "query.m" = m ∧ σ.vars "query.n" = n ∧
    σ.vars "cap.R" = R ∧ σ.vars "cap.D" = D ∧ σ.vars "search.budget" = N

theorem normalizeQuery_spec (B M m n R D N : ℕ) (P : Program ℤ m n)
    (hM : 1 ≤ M) (hR : R ≤ M) (hD : 0 < D) (hDM : D ≤ M)
    (hdim : (m + n) * n + m + n + 1 < B) (hB : 2 * M ^ 2 + 3 < B)
    (hA : ∀ i j, (P.A i j).natAbs ≤ M) (hb : ∀ i, (P.b i).natAbs ≤ M) :
    Spec B (Input P R D N) normalizeQuery
      (fun _ τ => RamSearchBounds.Input (normalizedMatrix P R) (normalizedBound P (1 / (D : ℚ))) N τ)
      ((72 * M.size + 181) * ((m + n) * n) + (72 * M.size + 189) * (m + n) + 78) := by
  rintro σ ⟨hσA, hσb, hσrows, hσrhs, hσcenter, hσshape, hσworkspace, hσnormal,
    hσm, hσn, hσR, hσD, hσN⟩
  obtain ⟨τ, hr₁, hτrows, hτA, hτm, hτn, hτR⟩ :=
    RamNormalizedMatrix.normalizeMatrix_spec B M m n P R hM hR hdim hB hA σ
      ⟨hσA, hσrows, hσm, hσn, hσR⟩
  have hτb := RamEllipsoidUpdate.represents_frame hr₁ "pad.b" _ hσb (by decide) (by decide) (by decide)
  have hτrhs := RamAdvanceState.extents_of_run hr₁ "search.rhs" (m + n) hσrhs
  have hτD := (hr₁.frame_var "cap.D" (by decide)).trans hσD
  obtain ⟨υ, hr₂, hυrhs, hυb, hυm, hυn, hυD⟩ :=
    RamNormalizedBound.normalizeBound_spec B M m n P D hM hD hDM (by omega) hB hb τ
      ⟨hτb, hτrhs, hτm, hτn, hτD⟩
  have hυrows := RamEllipsoidUpdate.represents_frame hr₂ "search.rows" _ hτrows
    (by decide) (by decide) (by decide)
  have hnB : n < B := by omega
  have hmB : m < B := by omega
  have hsumB : m + n < B := by omega
  have hr₃ : Run B (.assign "vec.n" (.var "query.n")) υ (υ.setVar "vec.n" n) 2 :=
    Run.assign (by simpa only [hυn] using evalB_var (B := B) (σ := υ) (x := "query.n") (hυn ▸ hnB))
  have hr₄ : Run B (.assign "row.m" (.add (.var "query.m") (.var "query.n")))
      (υ.setVar "vec.n" n) ((υ.setVar "vec.n" n).setVar "row.m" (m + n)) 4 := by
    apply Run.assign
    simpa [hυm, hυn] using evalB_bin
      (evalB_var (B := B) (σ := υ.setVar "vec.n" n) (x := "query.m") (by simpa [hυm] using hmB))
      (evalB_var (B := B) (σ := υ.setVar "vec.n" n) (x := "query.n") (by simpa [hυn] using hnB))
      (show Bop.add.apply ((υ.setVar "vec.n" n).vars "query.m")
        ((υ.setVar "vec.n" n).vars "query.n") < B by simpa [hυm, hυn] using hsumB)
  have hr := hr₁.seq (hr₂.seq (hr₃.seq hr₄))
  have hN := (hr.frame_var "search.budget" (by decide)).trans hσN
  have hrows := rows_of_represents "search.rows" (fun i j => (normalizedMatrix P R i j : ℚ)) υ hυrows
  refine ⟨_, hr.mono (by omega), ?_, ?_,
    RamAdvanceState.extents_of_run hr "ell.center" n hσcenter,
    RamAdvanceState.extents_of_run hr "ell.shape" (n * n) hσshape,
    RamAdvanceState.workspace_of_run hr n hσworkspace,
    RamAdvanceState.extents_of_run hr "ell.normal" n hσnormal, ?_, ?_, hN⟩
  · simpa only [RamMatrixRows.MatrixRows, RamMatrixRows.Slice, arrs_setVar] using hrows
  · simpa only [Represents, arrs_setVar] using hυrhs
  · simp
  · simp

end Lax109476Proofs.RamNormalizeQuery

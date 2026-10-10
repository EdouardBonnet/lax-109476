import Lax109476Proofs.RamReadArray
import Lax109476Proofs.RamMatrixStorage

namespace Lax109476Proofs.RamReadMatrix

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamMatrixStorage WordDecoding

/-- The registered row-major encoding and the solver's flat storage have
identical ordering, including when a row or column dimension is zero. -/
theorem flatten_rows {m n : ℕ} (A : Fin m → Fin n → ℚ) :
    flatten A = (List.ofFn fun i => List.ofFn (A i)).flatten := by
  unfold flatten
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  simpa only [flatten, List.getElem_ofFn] using flatten_entry A i j

theorem encodeRows_flat {m n : ℕ} (A : Fin m → Fin n → ℚ) :
    encodeRows A = encodeVector (fun k : Fin (m * n) => A k.divNat k.modNat) := by
  change _ = (flatten A).flatMap encodeRational
  rw [flatten_rows]
  unfold encodeRows encodeVector
  simp only [List.flatten_eq_flatMap, List.flatMap_assoc]
  simp only [List.flatMap_def, List.map_ofFn, Function.comp_def, id_eq]

theorem readRows_valid_spec (B M m n : ℕ) (a : String) (A : Fin m → Fin n → ℚ)
    (rest : List ℕ) (h2 : 2 < B) (hMB : M < B) (hM : 1 ≤ M) (hmnB : m * n < B)
    (hxB : (encodeRows A ++ rest).length < B)
    (hwords : ∀ z ∈ encodeRows A ++ rest, z ≤ M) :
    Spec B (fun σ => (σ.arrs (a ++ ".s")).length = m * n ∧
        (σ.arrs (a ++ ".n")).length = m * n ∧ (σ.arrs (a ++ ".d")).length = m * n ∧
        σ.inp = encodeRows A ++ rest ∧ σ.vars "input.remaining" = (encodeRows A ++ rest).length ∧
        σ.vars "input.valid" = 1 ∧ σ.InpBounded B ∧ σ.vars "vec.n" = m * n)
      (RamReadArray.readArray a)
      (fun _ τ => Represents a (flatten A) τ ∧ τ.inp = rest ∧
        τ.vars "input.remaining" = rest.length ∧ τ.vars "input.valid" = 1 ∧
        τ.InpBounded B ∧ τ.vars "vec.n" = m * n)
      ((36 * M.size + 115) * (m * n) + 24) := by
  have hdec : readVector (m * n) (encodeRows A ++ rest) =
      some ((fun k : Fin (m * n) => A k.divNat k.modNat), rest) := by
    rw [encodeRows_flat]
    exact readVector_encode _ _ _
  exact RamReadArray.readArray_valid_spec B M (m * n) a (encodeRows A ++ rest)
    (fun k => A k.divNat k.modNat) rest h2 hMB hM hmnB hxB hwords hdec

end Lax109476Proofs.RamReadMatrix

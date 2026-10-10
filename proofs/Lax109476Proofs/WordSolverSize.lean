import Lax109476Proofs.WordSolver
import Lax109476Proofs.DecodingSizeBounds
import Lax109476Proofs.SolverOutputBounds
import Lax759944.RamPolytime

namespace Lax109476Proofs.WordSolverSize

open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax109476.RationalEncoding EncodingSize

/-- This bound applies to the implemented solver on every word list,
including noncanonical rational triples and malformed inputs. -/
theorem solve_size (xs : List ℕ) :
    bitSize (WordSolver.solve xs) ≤ 512 * (bitSize xs + 1) ^ 3 := by
  unfold WordSolver.solve
  cases he : WordDecoding.decode xs with
  | none => simp [bitSize_nil]
  | some P =>
    obtain ⟨cert, hc, _⟩ := CertificateSearch.solve_exists P.program
    simp only [hc, Option.map_some, Option.getD_some]
    have houtput := SolverOutputBounds.solve_encoding_size P.program cert hc
    have hinput := DecodingSizeBounds.decode_size xs P he
    exact houtput.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))

theorem length_le_bitSize (xs : List ℕ) : xs.length ≤ bitSize xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [List.length_cons, bitSize_cons]; omega

theorem member_size_le {xs : List ℕ} {a : ℕ} (ha : a ∈ xs) :
    a.size ≤ bitSize xs := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    rw [bitSize_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · have h := ih ha; omega

/-- Sufficient word width for the physical input and the exact returned
certificate. Execution and time bounds are separate obligations. -/
theorem input_output_fit (xs : List ℕ) :
    FitsInWords (512 * (bitSize xs + 1) ^ 3 + 1)
      ((xs.length :: xs) ++ WordSolver.solve xs) := by
  intro a ha
  have hcube : bitSize xs + 1 ≤ (bitSize xs + 1) ^ 3 :=
    le_self_pow (by omega) (by decide)
  have hL : bitSize xs ≤ 512 * (bitSize xs + 1) ^ 3 := by omega
  have hsize : a.size ≤ 512 * (bitSize xs + 1) ^ 3 := by
    rcases List.mem_append.mp ha with hi | ho
    · rcases List.mem_cons.mp hi with rfl | hi
      · exact (RationalSizeBounds.size_le_self xs.length).trans
          ((length_le_bitSize xs).trans hL)
      · exact (member_size_le hi).trans hL
    · exact (member_size_le ho).trans (solve_size xs)
  exact Nat.size_le.mp (Nat.le_succ_of_le hsize)

end Lax109476Proofs.WordSolverSize

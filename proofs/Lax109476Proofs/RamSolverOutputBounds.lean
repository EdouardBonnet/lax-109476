import Lax109476Proofs.RamSolverTotalExecution

namespace Lax109476Proofs.RamSolverOutputBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax759944.BinaryWordEncoding

theorem output_of_bigStepB {B k : ℕ} {c : Com} {σ τ : Env} (h : BigStepB B c σ τ k) :
    (∀ v ∈ σ.out, v < B) → ∀ v ∈ τ.out, v < B := by
  induction h with
  | skip => exact fun h => h
  | assign he => simpa [Env.setVar]
  | store hi he hk => simpa [Env.setArr]
  | seq _ _ ih ih' => exact fun h => ih' (ih h)
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => exact fun h => ih' (ih h)
  | while_false _ => exact fun h => h
  | read he => simpa [Env.setVar]
  | write he =>
    intro h v hv
    simp only [List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact h v hv
    · exact Expr.lt_of_evalB he

theorem output_of_run {B k : ℕ} {c : Com} {σ τ : Env} (h : Run B c σ τ k)
    (hσ : ∀ v ∈ σ.out, v < B) : ∀ v ∈ τ.out, v < B := by
  obtain ⟨k', hk', hstep⟩ := h
  exact output_of_bigStepB hstep hσ

theorem input_fits (xs : List ℕ) :
    ∀ v ∈ xs.length :: xs, v < 2 ^ RamUniformSolverBounds.wordWidth (bitSize xs) := by
  let L := bitSize xs
  let W := RamUniformSolverBounds.wordWidth L
  have hLW : L ≤ W := by
    have hC := RamDecodedProgram.canonicalBound_ge L
    dsimp only [W, RamUniformSolverBounds.wordWidth, RamFrontEndTotal.wordWidth,
      RamInitializationTotal.wordWidth, RamDecoder.wordWidth]
    omega
  intro v hv
  simp only [List.mem_cons] at hv
  rcases hv with rfl | hv
  · exact ((WordSolverSize.length_le_bitSize xs).trans hLW).trans_lt (Nat.lt_two_pow_self (n := W))
  · exact (Nat.lt_size_self v).trans_le (Nat.pow_le_pow_right (by decide)
      ((WordSolverSize.member_size_le hv).trans hLW))

end Lax109476Proofs.RamSolverOutputBounds

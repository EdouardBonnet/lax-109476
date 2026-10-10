import Lax109476Proofs.RamDecoder
import Lax109476Proofs.RamProgramSize
import Lax109476Proofs.RamProgramDenominator

open scoped BigOperators

namespace Lax109476Proofs.RamSolverInitialization

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamStoredProgram RationalArithmeticBounds EncodingSize IntegerEncoding

def initializeSolver : Com := .seq RamDecoder.decode
  (.ite (.eq (.var "input.valid") (.lit 1))
    (.seq RamProgramSize.prepareSize RamProgramDenominator.prepareDenominator) .skip)

theorem datum_height {m n : ℕ} (P : Program ℚ m n) (i) :
    Height (programData P i) (2 ^ bitSize (encodeProgram P)) := by
  have hnum := datum_numerator_size P i
  have hden : (programData P i).den.size ≤ bitSize (encodeProgram P) := by
    have hs := Finset.single_le_sum (fun j _ => Nat.zero_le (programData P j).den.size) (Finset.mem_univ i)
    have hh := denominator_size_sum P
    omega
  exact ⟨((Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) hnum)).le,
    ((Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) hden)).le⟩

theorem cells_bound {m n : ℕ} (P : Program ℚ m n) : m * n + m + n ≤ bitSize (encodeProgram P) := by
  have hlen : (encodeProgram P).length = 2 + 3 * (m * n + m + n) := by
    rw [WordDecoding.encodeProgram_rows]
    simp only [List.length_cons, List.length_append, WordDecoding.encodeRows_length,
      WordDecoding.encodeVector_length, Nat.mul_assoc]
    omega
  have hl := WordSolverSize.length_le_bitSize (encodeProgram P)
  rw [hlen] at hl
  omega

def instructionBound (L : ℕ) : ℕ := RamDecoder.instructionBound L (L + 1) +
  (36 * (L + 1) + 61) * L + 37 * L + 86

theorem initialize_valid_spec (m n : ℕ) (P : Program ℚ m n) (w : ℕ)
    (hw : RamDecoder.wordWidth (bitSize (encodeProgram P)) ≤ w) :
    Spec (2 ^ w) (RamDecoder.Input (2 ^ w) (encodeProgram P)) initializeSolver
      (fun _ τ => RepresentsProgram P τ ∧ τ.vars "input.valid" = 1 ∧
        τ.vars "input.bits" = bitSize (encodeProgram P) ∧
        τ.vars "den.value" = programDenominator P ∧ τ.inp = [] ∧ τ.InpBounded (2 ^ w))
      (instructionBound (bitSize (encodeProgram P))) := by
  let L := bitSize (encodeProgram P)
  let H := 2 ^ L
  have hHL : H < 2 ^ w := Nat.pow_lt_pow_right (by decide)
    (by dsimp only [RamDecoder.wordWidth] at hw; omega)
  have hH : 1 ≤ H := Nat.one_le_pow L 2 (by decide)
  have h8 : 8 ≤ w := by dsimp only [RamDecoder.wordWidth] at hw; omega
  have h256 : 256 ≤ 2 ^ w := by simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) h8
  have h2 : 2 < 2 ^ w := by omega
  have hLB : L < 2 ^ w := (Nat.lt_two_pow_self (n := L)).trans hHL
  have hcells := cells_bound P
  have hmB : m < 2 ^ w := (by omega : m ≤ L).trans_lt hLB
  have hnB : n < 2 ^ w := (by omega : n ≤ L).trans_lt hLB
  have hmnB : m * n < 2 ^ w := (by omega : m * n ≤ L).trans_lt hLB
  have hA : ∀ i j, Height (P.A i j) H := fun i j => datum_height P (.inl (i, j))
  have hb : ∀ i, Height (P.b i) H := fun i => datum_height P (.inr (.inl i))
  have hc : ∀ j, Height (P.c j) H := fun j => datum_height P (.inr (.inr j))
  have hDB : programDenominator P < 2 ^ w := (programDenominator_bound P).trans_lt hHL
  intro σ hσ
  obtain ⟨τ, hr₁, hτA, hτb, hτc, hτinp, hτrem, hτvalid, hτbound, hτm, hτn, hτcount⟩ :=
    RamDecoder.decode_valid_spec m n P w hw σ hσ
  have hτP : RepresentsProgram P τ := ⟨hτA, hτb, hτc, hτm, hτn, hτcount⟩
  obtain ⟨υ, hr₂, hυbits, hυP, _⟩ := RamProgramSize.prepareSize_spec (2 ^ w) H m n P
    h2 hH hHL hmB hnB hmnB hA hb hc hLB τ hτP
  obtain ⟨ξ, hr₃, hξden, hξP, _⟩ := RamProgramDenominator.prepareDenominator_spec (2 ^ w) m n P
    (by omega) hmB hnB hmnB hDB υ hυP
  have hξbits := (hr₃.frame_var "input.bits" (by decide)).trans hυbits
  have hξvalid := ((hr₂.seq hr₃).frame_var "input.valid" (by decide)).trans hτvalid
  have hξinp := ((hr₂.seq hr₃).frame_inp (by decide)).trans hτinp
  have hbcond : (Cond.eq (.var "input.valid") (.lit 1)).evalB (2 ^ w) τ = some true := by
    simpa [hτvalid] using evalB_condEq
      (evalB_var (B := 2 ^ w) (σ := τ) (x := "input.valid") (by rw [hτvalid]; omega))
      (evalB_lit (by omega : 1 < 2 ^ w))
  have hrun := hr₁.seq (Run.ite_true (d := .skip) hbcond (hr₂.seq hr₃))
  have hms : m.size ≤ L := (RationalSizeBounds.size_le_self m).trans (by omega)
  have hns : n.size ≤ L := (RationalSizeBounds.size_le_self n).trans (by omega)
  have hmul := Nat.mul_le_mul_left (36 * (L + 1) + 61) hcells
  refine ⟨ξ, hrun.mono ?_, hξP, hξvalid, hξbits, hξden, hξinp, hrun.inpBounded hσ.2.1⟩
  simp only [instructionBound, Cond.size, Expr.size, H, Nat.size_pow, L]
  dsimp only [L] at hmul hms hns
  omega

end Lax109476Proofs.RamSolverInitialization

import Lax109476Proofs.RamDecoder
import Lax109476Proofs.RamStoredProgram
import Lax109476Proofs.RecoveryArithmeticBounds

namespace Lax109476Proofs.RamDecodedProgram

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamReadArray RamReadBody RamRationalArrays RationalArithmeticBounds

def bodyProgram (xs : List ℕ) (m n : ℕ) : Program ℚ m n :=
  { A := fun i j => values xs 1 (m * n) ⟨i.val * n + j.val, RamMatrixStorage.row_index_lt i j⟩
    b := values (afterA xs m n) (flagA xs 1 m n) m
    c := values (afterB xs m n) (flagB xs 1 m n) n }

def decodedProgram (xs : List ℕ) : Program ℚ (xs.headD 0) (xs.tail.headD 0) :=
  bodyProgram (xs.drop 2) (xs.headD 0) (xs.tail.headD 0)

theorem flatten_body (xs : List ℕ) (m n : ℕ) :
    RamMatrixStorage.flatten (bodyProgram xs m n).A = List.ofFn (values xs 1 (m * n)) := by
  unfold RamMatrixStorage.flatten
  congr 1
  funext i
  change values xs 1 (m * n) ⟨(i.val / n) * n + i.val % n, _⟩ = values xs 1 (m * n) i
  congr 1
  apply Fin.ext
  simpa only [Nat.mul_comm] using Nat.div_add_mod i.val n

theorem result_program (B m n : ℕ) (xs : List ℕ) (σ : Env) (hσ : Result B xs 1 m n σ) :
    RamStoredProgram.RepresentsProgram (bodyProgram xs m n) σ ∧ σ.vars "input.valid" ≤ 1 := by
  rcases hσ with ⟨hA, hb, hc, hinp, hrem, hvalid, hbounded, hm, hn, hcount⟩
  refine ⟨⟨?_, hb, hc, hm, hn, hcount⟩, ?_⟩
  · simpa only [flatten_body] using hA
  · have hfa : flagA xs 1 m n ≤ 1 := flag_le_one xs 1 (m * n) (by decide)
    have hfb : flagB xs 1 m n ≤ 1 := flag_le_one (afterA xs m n) _ m hfa
    have hfc : flagC xs 1 m n ≤ 1 := flag_le_one (afterB xs m n) _ n hfb
    rw [hvalid]
    split_ifs <;> omega

theorem values_height (xs : List ℕ) (v n M : ℕ) (hM : 1 ≤ M)
    (hwords : ∀ z ∈ xs, z ≤ M) : ∀ i, Height (values xs v n i) M := by
  intro i
  exact safeValue_height _ _ M hM (fun z hz => hwords z (List.mem_of_mem_drop hz))

theorem body_height (xs : List ℕ) (m n M : ℕ) (hM : 1 ≤ M) (hwords : ∀ z ∈ xs, z ≤ M) :
    (∀ i j, Height ((bodyProgram xs m n).A i j) M) ∧
      (∀ i, Height ((bodyProgram xs m n).b i) M) ∧ ∀ j, Height ((bodyProgram xs m n).c j) M := by
  refine ⟨fun i j => values_height xs 1 (m * n) M hM hwords _, ?_, ?_⟩
  · exact values_height _ _ _ _ hM (fun z hz => hwords z (List.mem_of_mem_drop hz))
  · exact values_height _ _ _ _ hM (fun z hz => hwords z (List.mem_of_mem_drop (List.mem_of_mem_drop hz)))

def canonicalBound (L : ℕ) : ℕ := 2 * L + 4 + ((L + 1) ^ 2 + 2 * L + 2) * (4 + 2 * (L + 1))

theorem decoded_size (xs : List ℕ) (hheader : RamDecoder.AcceptedHeader xs) :
    bitSize (encodeProgram (decodedProgram xs)) ≤ canonicalBound (bitSize xs) := by
  let L := bitSize xs
  have hlen : xs.length ≤ L := WordSolverSize.length_le_bitSize xs
  have hm : xs.headD 0 ≤ L + 1 := by
    have hh := hheader.2.1
    simp only [List.length_drop] at hh
    omega
  have hn : xs.tail.headD 0 ≤ L + 1 := by
    have hh := hheader.2.2
    simp only [List.length_drop] at hh
    omega
  have hprod : xs.headD 0 * xs.tail.headD 0 ≤ (L + 1) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hm hn
  have hM : 1 ≤ 2 ^ L := Nat.one_le_pow _ _ (by decide)
  have hwords : ∀ z ∈ xs.drop 2, z ≤ 2 ^ L := by
    intro z hz
    exact ((Nat.lt_size_self z).trans_le
      (Nat.pow_le_pow_right (by decide) (WordSolverSize.member_size_le (List.mem_of_mem_drop hz)))).le
  obtain ⟨hA, hb, hc⟩ := body_height (xs.drop 2) (xs.headD 0) (xs.tail.headD 0) (2 ^ L) hM hwords
  have hs := RecoveryArithmeticBounds.program_height_size (decodedProgram xs) (2 ^ L) hA hb hc
  rw [Nat.size_pow] at hs
  have hrows : xs.headD 0 + xs.tail.headD 0 + 2 ≤ 2 * L + 4 := by omega
  have hcells : xs.headD 0 * xs.tail.headD 0 + xs.headD 0 + xs.tail.headD 0 ≤ (L + 1) ^ 2 + 2 * L + 2 := by omega
  exact hs.trans (Nat.add_le_add hrows (Nat.mul_le_mul_right (4 + 2 * (L + 1)) hcells))

theorem canonicalBound_ge (L : ℕ) : L ≤ canonicalBound L := by
  unfold canonicalBound
  omega

theorem output_empty_of_valid (B : ℕ) (xs : List ℕ) (σ : Env)
    (hheader : RamDecoder.AcceptedHeader xs) (hσ : RamDecoder.Output B xs σ)
    (hvalid : σ.vars "input.valid" = 1) : σ.inp = [] := by
  simp only [RamDecoder.Output, if_pos hheader] at hσ
  rcases hσ with ⟨hA, hb, hc, hinp, hrem, hflag, hbound, hm, hn, hcount⟩
  have hz : (afterC (xs.drop 2) (xs.headD 0) (xs.tail.headD 0)).length = 0 := by
    by_contra h
    simp only [if_neg h] at hflag
    omega
  exact hinp.trans (List.eq_nil_of_length_eq_zero hz)

theorem output_program (B : ℕ) (xs : List ℕ) (σ : Env) (hheader : RamDecoder.AcceptedHeader xs)
    (hσ : RamDecoder.Output B xs σ) :
    RamStoredProgram.RepresentsProgram (decodedProgram xs) σ ∧ σ.vars "input.valid" ≤ 1 := by
  simp only [RamDecoder.Output, if_pos hheader] at hσ
  exact result_program B _ _ _ σ hσ

end Lax109476Proofs.RamDecodedProgram

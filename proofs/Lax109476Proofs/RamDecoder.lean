import Lax109476Proofs.RamReadBody
import Lax109476Proofs.RamReadHeader
import Lax109476Proofs.WordSolverSize

namespace Lax109476Proofs.RamDecoder

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamInput RamReadHeader RamReadBody RamRationalArrays RamEllipsoidStep RamAdvanceState

/-- One input-independent command reads the physical prefix and LP payload.
The matrix loops run only after the payload-length dimension checks. -/
def decode : Com := .seq startInput (.seq readHeader
  (.ite (.eq (.var "input.valid") (.lit 1)) readBody .skip))

def AcceptedHeader (xs : List ℕ) : Prop := 2 ≤ xs.length ∧ ValidDimensions xs
instance (xs : List ℕ) : Decidable (AcceptedHeader xs) := by unfold AcceptedHeader; infer_instance

def Input (B : ℕ) (xs : List ℕ) (σ : Env) : Prop :=
  σ.inp = xs.length :: xs ∧ σ.InpBounded B ∧
    Extents "lp.A" (if ValidDimensions xs then xs.headD 0 * xs.tail.headD 0 else 0) σ ∧
    Extents "lp.b" (if ValidDimensions xs then xs.headD 0 else 0) σ ∧
    Extents "lp.c" (if ValidDimensions xs then xs.tail.headD 0 else 0) σ

def Output (B : ℕ) (xs : List ℕ) (σ : Env) : Prop :=
  if AcceptedHeader xs then Result B (xs.drop 2) 1 (xs.headD 0) (xs.tail.headD 0) σ
  else σ.vars "input.valid" = 0 ∧ σ.inp = xs.drop 2 ∧ σ.InpBounded B

def instructionBound (S bits : ℕ) : ℕ := (36 * bits + 115) * (S ^ 2 + 4 * S + 3) + 127

theorem decode_spec (B M : ℕ) (xs : List ℕ) (hB : (xs.length + 2) ^ 2 < B)
    (hMB : M < B) (hM : 1 ≤ M) (hwords : ∀ z ∈ xs, z ≤ M) :
    Spec B (Input B xs) decode (fun _ τ => Output B xs τ)
      (instructionBound xs.length M.size) := by
  have h4 : 4 ≤ (xs.length + 2) ^ 2 := by
    simpa using Nat.pow_le_pow_left (show 2 ≤ xs.length + 2 by omega) 2
  have h2 : 2 < B := by omega
  have hxB : xs.length < B := by nlinarith
  rintro σ ⟨hσinp, hσbound, hσA, hσb, hσc⟩
  obtain ⟨τ, hr₁, hτinp, hτrem, hτvalid, hτbound, _⟩ := startInput_spec B xs (by omega)
    σ ⟨hσinp, hσbound⟩
  obtain ⟨υ, hr₂, hυm, hυn, hυinp, hυrem, hυvalid, hυcount, hυbound⟩ :=
    readHeader_spec B M 1 xs hB hMB (by decide) hwords τ ⟨hτinp, hτrem, hτvalid, hτbound⟩
  have hflag : υ.vars "input.valid" ≤ 1 := by rw [hυvalid]; split_ifs <;> omega
  have hflagB : υ.vars "input.valid" < B := by omega
  by_cases hg : AcceptedHeader xs
  · have hd : ValidDimensions xs := hg.2
    have hmm : xs.headD 0 ≤ xs.length + 1 := hd.1.trans (by simp only [List.length_drop]; omega)
    have hnn : xs.tail.headD 0 ≤ xs.length + 1 := hd.2.trans (by simp only [List.length_drop]; omega)
    have hp := Nat.mul_le_mul hmm hnn
    have hmB : xs.headD 0 < B := by nlinarith
    have hnB : xs.tail.headD 0 < B := by nlinarith
    have hmnB : xs.headD 0 * xs.tail.headD 0 < B := by nlinarith
    have hυvalid1 : υ.vars "input.valid" = 1 := by simpa only [if_pos (show 2 ≤ xs.length ∧ ValidDimensions xs from hg)] using hυvalid
    have hυcount' : υ.vars "decode.count" = xs.headD 0 * xs.tail.headD 0 :=
      by simpa only [if_pos hd] using hυcount
    have hυA := extents_of_run (hr₁.seq hr₂) "lp.A" _ hσA
    have hυb := extents_of_run (hr₁.seq hr₂) "lp.b" _ hσb
    have hυc := extents_of_run (hr₁.seq hr₂) "lp.c" _ hσc
    simp only [if_pos hd] at hυA hυb hυc
    obtain ⟨ξ, hr₃, hξ⟩ := readBody_spec B M (xs.headD 0) (xs.tail.headD 0) 1 (xs.drop 2)
      h2 hMB hM hmB hnB hmnB (by simp only [List.length_drop]; omega) (by decide)
      (fun z hz => hwords z (List.mem_of_mem_drop hz)) υ
      ⟨hυA, hυb, hυc, hυinp, hυrem, hυvalid1, hυbound, hυm, hυn, hυcount'⟩
    have hb : (Cond.eq (.var "input.valid") (.lit 1)).evalB B υ = some true := by
      simpa [hυvalid1] using evalB_condEq
        (evalB_var (B := B) (σ := υ) (x := "input.valid") hflagB) (evalB_lit (by omega : 1 < B))
    have hcount : xs.headD 0 * xs.tail.headD 0 + xs.headD 0 + xs.tail.headD 0 ≤
        xs.length ^ 2 + 4 * xs.length + 3 := by nlinarith
    have hcost := Nat.mul_le_mul_left (36 * M.size + 115) hcount
    refine ⟨ξ, (hr₁.seq (hr₂.seq (Run.ite_true (d := .skip) hb hr₃))).mono ?_, ?_⟩
    · simp only [instructionBound, Cond.size, Expr.size]; omega
    · simpa only [Output, if_pos hg] using hξ
  · have hυzero : υ.vars "input.valid" = 0 := by simpa only [if_neg (show ¬(2 ≤ xs.length ∧ ValidDimensions xs) from hg)] using hυvalid
    have hb : (Cond.eq (.var "input.valid") (.lit 1)).evalB B υ = some false := by
      simpa [hυzero] using evalB_condEq
        (evalB_var (B := B) (σ := υ) (x := "input.valid") hflagB) (evalB_lit (by omega : 1 < B))
    exact ⟨υ, (hr₁.seq (hr₂.seq (Run.ite_false (c := readBody) hb Run.skip))).mono
      (by simp only [instructionBound, Cond.size, Expr.size]; omega),
      by simpa only [Output, if_neg hg] using And.intro hυzero (And.intro hυinp hυbound)⟩

def wordWidth (L : ℕ) : ℕ := 4 * (L + 2)

theorem decode_bounded_spec (xs : List ℕ) (w : ℕ) (hw : wordWidth (Lax759944.BinaryWordEncoding.bitSize xs) ≤ w) :
    Spec (2 ^ w) (Input (2 ^ w) xs) decode (fun _ τ => Output (2 ^ w) xs τ)
      (instructionBound (Lax759944.BinaryWordEncoding.bitSize xs)
        (Lax759944.BinaryWordEncoding.bitSize xs + 1)) := by
  let L := Lax759944.BinaryWordEncoding.bitSize xs
  have hlen : xs.length ≤ L := WordSolverSize.length_le_bitSize xs
  have hpow : L + 2 < 2 ^ (L + 2) := Nat.lt_two_pow_self
  have hsquare : (L + 2) ^ 2 < 2 ^ (2 * (L + 2)) := by
    have hh := Nat.pow_lt_pow_left hpow (by decide : 2 ≠ 0)
    simpa only [← pow_mul, Nat.mul_comm] using hh
  have hexp : 2 * (L + 2) ≤ w := by dsimp only [wordWidth] at hw; omega
  have hB : (xs.length + 2) ^ 2 < 2 ^ w :=
    ((Nat.pow_le_pow_left (by omega : xs.length + 2 ≤ L + 2) 2).trans_lt hsquare).trans_le
      (Nat.pow_le_pow_right (by decide) hexp)
  have hMB : 2 ^ L < 2 ^ w :=
    Nat.pow_lt_pow_right (by decide) (by dsimp only [wordWidth] at hw; omega)
  have hM : 1 ≤ 2 ^ L := Nat.one_le_pow L 2 (by decide)
  have hwords : ∀ z ∈ xs, z ≤ 2 ^ L := by
    intro z hz
    exact ((Nat.lt_size_self z).trans_le
      (Nat.pow_le_pow_right (by decide) (WordSolverSize.member_size_le hz))).le
  apply (decode_spec (2 ^ w) (2 ^ L) xs hB hMB hM hwords).mono
  rw [Nat.size_pow]
  have hs := Nat.pow_le_pow_left hlen 2
  have hsum : xs.length ^ 2 + 4 * xs.length + 3 ≤ L ^ 2 + 4 * L + 3 := by omega
  exact Nat.add_le_add_right (Nat.mul_le_mul_left (36 * (L + 1) + 115) hsum) 127

theorem encodedHeader_accepted (m n : ℕ) (P : Lax109476.LinearProgram.Program ℚ m n) :
    AcceptedHeader (Lax109476.RationalEncoding.encodeProgram P) := by
  rw [WordDecoding.encodeProgram_rows]
  have hlen : (WordDecoding.encodeRows P.A ++ Lax109476.RationalEncoding.encodeVector P.b ++
      Lax109476.RationalEncoding.encodeVector P.c).length = 3 * m * n + 3 * m + 3 * n := by
    rw [List.length_append, List.length_append, WordDecoding.encodeRows_length,
      WordDecoding.encodeVector_length, WordDecoding.encodeVector_length]
  simp only [AcceptedHeader, ValidDimensions, List.length_cons, List.headD_cons,
    List.tail_cons, List.drop_succ_cons, List.drop_zero]
  omega

theorem decode_valid_spec (m n : ℕ) (P : Lax109476.LinearProgram.Program ℚ m n) (w : ℕ)
    (hw : wordWidth (Lax759944.BinaryWordEncoding.bitSize
      (Lax109476.RationalEncoding.encodeProgram P)) ≤ w) :
    Spec (2 ^ w) (Input (2 ^ w) (Lax109476.RationalEncoding.encodeProgram P)) decode
      (fun _ τ => Represents "lp.A" (RamMatrixStorage.flatten P.A) τ ∧
        Represents "lp.b" (List.ofFn P.b) τ ∧ Represents "lp.c" (List.ofFn P.c) τ ∧
        τ.inp = [] ∧ τ.vars "input.remaining" = 0 ∧ τ.vars "input.valid" = 1 ∧
        τ.InpBounded (2 ^ w) ∧ τ.vars "lp.m" = m ∧ τ.vars "lp.n" = n ∧
        τ.vars "decode.count" = m * n)
      (instructionBound (Lax759944.BinaryWordEncoding.bitSize (Lax109476.RationalEncoding.encodeProgram P))
        (Lax759944.BinaryWordEncoding.bitSize (Lax109476.RationalEncoding.encodeProgram P) + 1)) := by
  have hhead := encodedHeader_accepted m n P
  apply (decode_bounded_spec (Lax109476.RationalEncoding.encodeProgram P) w hw).post
  intro σ τ hσ hτ
  simp only [Output, if_pos hhead] at hτ
  rw [WordDecoding.encodeProgram_rows] at hτ
  simp only [List.headD_cons, List.tail_cons, List.drop_succ_cons, List.drop_zero] at hτ
  exact encodedResult_correct (2 ^ w) m n P τ hτ

end Lax109476Proofs.RamDecoder

import Lax109476Proofs.RamScaleBlock
import Lax109476Proofs.RamStoredProgram
import Lax109476Proofs.RamProgramDenominator

namespace Lax109476Proofs.RamClearProgram

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamScaleArray RamScaleBlock RamRationalArrays RamFrame RamStoredProgram
open RationalArithmeticBounds IntegerEncoding RamEllipsoidStep

def IntegerRep {m n : ℕ} (P : Program ℚ m n) (σ : Env) : Prop :=
  Represents "int.A" (RamMatrixStorage.flatten (rationalProgram (integerProgram P)).A) σ ∧
    Represents "int.b" (List.ofFn (rationalProgram (integerProgram P)).b) σ ∧
    Represents "int.c" (List.ofFn (rationalProgram (integerProgram P)).c) σ

def clearProgram : Com := .seq (.assign "scale.factor" (.var "den.value"))
  (.seq (scaleBlock "lp.A" "int.A" "decode.count")
    (.seq (scaleBlock "lp.b" "int.b" "lp.m") (scaleBlock "lp.c" "int.c" "lp.n")))

set_option maxHeartbeats 800000 in
theorem clearProgram_spec (B M m n : ℕ) (P : Program ℚ m n)
    (hM : 1 ≤ M) (hmB : m < B) (hnB : n < B) (hmnB : m * n < B)
    (hB : 2 * M ^ 2 + 3 < B) (hA : ∀ i j, Height (P.A i j) M)
    (hb : ∀ i, Height (P.b i) M) (hc : ∀ j, Height (P.c j) M)
    (hD : programDenominator P ≤ M) :
    Spec B (fun σ => RepresentsProgram P σ ∧ Extents "int.A" (m * n) σ ∧
        Extents "int.b" m σ ∧ Extents "int.c" n σ ∧ σ.vars "den.value" = programDenominator P)
      clearProgram
      (fun σ τ => IntegerRep P τ ∧ RepresentsProgram P τ ∧
        τ.vars "den.value" = programDenominator P ∧ τ.vars "input.bits" = σ.vars "input.bits")
      ((72 * M.size + 135) * (m * n + m + n) + 80) := by
  let D := programDenominator P
  let Avec : Fin (m * n) → ℚ := fun k => P.A k.divNat k.modNat
  have hmat := scaleBlock_spec B M (m * n) D "lp.A" "int.A" "decode.count" Avec
    hM hmnB hB (fun k => hA k.divNat k.modNat) hD (by simp [RamCopy.Disjoint, RamCopy.suffixes])
  have hbound := scaleBlock_spec B M m D "lp.b" "int.b" "lp.m" P.b
    hM hmB hB hb hD (by simp [RamCopy.Disjoint, RamCopy.suffixes])
  have hobj := scaleBlock_spec B M n D "lp.c" "int.c" "lp.n" P.c
    hM hnB hB hc hD (by simp [RamCopy.Disjoint, RamCopy.suffixes])
  have h1 : 1 < B := by nlinarith
  have hMB : M < B := by nlinarith
  have hDB : D < B := hD.trans_lt hMB
  have hint := integerProgram_eq_scaled P
  rintro σ ⟨⟨hσA, hσb, hσc, hσm, hσn, hσcount⟩, hσintA, hσintb, hσintc, hσD⟩
  have hAs := hσintA ".s" (by simp)
  have hAn := hσintA ".n" (by simp)
  have hAd := hσintA ".d" (by simp)
  have hbs := hσintb ".s" (by simp)
  have hbn := hσintb ".n" (by simp)
  have hbd := hσintb ".d" (by simp)
  have hcs := hσintc ".s" (by simp)
  have hcn := hσintc ".n" (by simp)
  have hcd := hσintc ".d" (by simp)
  simp only [Nat.mul_add]
  run_vcg [hmat, hbound, hobj]
  all_goals clear hmat hbound hobj
  all_goals simp_all [IntegerRep, RepresentsProgram, Represents, FieldsAgree, fields,
    RamMatrixStorage.flatten, scaledProgram, Avec, D, Extents, mul_comm]
  all_goals aesop
  all_goals funext i
  all_goals change _ = _
  all_goals simp only [Function.comp_def, RamScaleArray.scaled]
  all_goals simp only [mul_comm]

end Lax109476Proofs.RamClearProgram

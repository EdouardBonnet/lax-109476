import Lax109476Proofs.RamDenominatorBlock
import Lax109476Proofs.RamStoredProgram

open scoped BigOperators

namespace Lax109476Proofs.RamProgramDenominator

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamDenominatorProduct RamDenominatorBlock RamRationalArrays RamFrame RamStoredProgram RamReadBlock
open IntegerEncoding RationalSizeBounds EncodingSize

theorem product_pos {n : ℕ} (v : Fin n → ℚ) : 0 < product v := by
  simpa only [prefix_done] using prefix_pos v n

theorem denominator_flat {m n : ℕ} (P : Program ℚ m n) :
    programDenominator P = product (fun k : Fin (m * n) => P.A k.divNat k.modNat) *
      product P.b * product P.c := by
  have hflat : product (fun k : Fin (m * n) => P.A k.divNat k.modNat) =
      ∏ i, ∏ j, (P.A i j).den := by
    unfold product
    have hm : (List.ofFn fun k : Fin (m * n) => (P.A k.divNat k.modNat).den) =
        (RamMatrixStorage.flatten P.A).map (fun q => q.den) := by
      simp only [RamMatrixStorage.flatten, List.map_ofFn]
      rfl
    rw [hm, RamReadMatrix.flatten_rows, List.map_flatten, List.map_ofFn]
    simp [List.prod_flatten, List.prod_ofFn, List.map_ofFn]
  unfold programDenominator commonDenominator programData
  simp only [Fintype.prod_sum_type, Fintype.prod_prod_type, Sum.elim_inl, Sum.elim_inr]
  rw [hflat]
  simp [product, List.prod_ofFn, Nat.mul_assoc]

def prepareDenominator : Com := .seq (.assign "den.value" (.lit 1))
  (.seq (productBlock "lp.A" "decode.count")
    (.seq (productBlock "lp.b" "lp.m") (productBlock "lp.c" "lp.n")))

set_option maxHeartbeats 600000 in
theorem prepareDenominator_spec (B m n : ℕ) (P : Program ℚ m n)
    (h1 : 1 < B) (hmB : m < B) (hnB : n < B) (hmnB : m * n < B)
    (hD : programDenominator P < B) :
    Spec B (RepresentsProgram P) prepareDenominator
      (fun σ τ => τ.vars "den.value" = programDenominator P ∧
        RepresentsProgram P τ ∧ τ.arrs = σ.arrs) (13 * (m * n + m + n) + 26) := by
  let Avec : Fin (m * n) → ℚ := fun k => P.A k.divNat k.modNat
  let DA := product Avec
  let Db := product P.b
  let Dc := product P.c
  have hflat : programDenominator P = DA * Db * Dc := denominator_flat P
  have hDA : 0 < DA := product_pos Avec
  have hDb : 0 < Db := product_pos P.b
  have hDc : 0 < Dc := product_pos P.c
  have hAB : DA < B := (Nat.le_mul_of_pos_right DA hDb).trans_lt
    ((Nat.le_mul_of_pos_right (DA * Db) hDc).trans_lt (by simpa only [hflat] using hD))
  have hAbB : DA * Db < B := (Nat.le_mul_of_pos_right (DA * Db) hDc).trans_lt
    (by simpa only [hflat] using hD)
  have hmat := productBlock_spec B 1 (m * n) "lp.A" "decode.count" Avec (by decide) hmnB
    (by simpa using hAB)
  have hbound := productBlock_spec B DA m "lp.b" "lp.m" P.b hDA hmB hAbB
  have hobj := productBlock_spec B (DA * Db) n "lp.c" "lp.n" P.c (Nat.mul_pos hDA hDb) hnB
    (by simpa only [hflat] using hD)
  rintro σ ⟨hσA, hσb, hσc, hσm, hσn, hσcount⟩
  run_vcg [hmat, hbound, hobj]
  all_goals clear hmat hbound hobj
  all_goals simp_all [RepresentsProgram, Represents, FieldsAgree, fields,
    RamMatrixStorage.flatten, Avec, DA, Db, Dc, Nat.mul_add]
  all_goals omega

end Lax109476Proofs.RamProgramDenominator

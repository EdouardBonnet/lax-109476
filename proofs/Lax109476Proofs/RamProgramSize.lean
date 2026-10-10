import Lax109476Proofs.RamSizeBlock
import Lax109476Proofs.RamStoredProgram

namespace Lax109476Proofs.RamProgramSize

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamEncodedSize RamSizeBlock RamRationalArrays RamFrame RamStoredProgram RamReadBlock
open RationalArithmeticBounds EncodingSize

theorem program_bits_flat {m n : ℕ} (P : Program ℚ m n) :
    bitSize (encodeProgram P) = m.size + n.size + 2 +
      bitSize (encodeVector (fun k : Fin (m * n) => P.A k.divNat k.modNat)) +
      bitSize (encodeVector P.b) + bitSize (encodeVector P.c) := by
  rw [WordDecoding.encodeProgram_rows, RamReadMatrix.encodeRows_flat]
  simp only [bitSize_cons, bitSize_append]
  omega

theorem countWord_wvars (x : String) : (countWord x).wvars = (countWord "").wvars := by rfl

theorem countWord_frame_spec (B a t : ℕ) (x : String) (h2 : 2 < B) (ha : a < B)
    (ht : t + a.size + 1 < B) :
    Spec B (fun σ => σ.vars x = a ∧ σ.vars "size.total" = t) (countWord x)
      (fun σ τ => τ.vars "size.total" = t + a.size + 1 ∧
        FieldsAgree fields σ τ ∧ τ.arrs = σ.arrs) (12 * a.size + 14) := by
  exact spec_with_fields fields (countWord_spec B a t x h2 ha ht)
    (by
      intro y hy
      rw [countWord_wvars]
      simp [fields] at hy
      rcases hy with rfl | rfl | rfl <;> decide) (by rfl)

def prepareSize : Com := .seq (.assign "size.total" (.lit 0))
  (.seq (countWord "lp.m") (.seq (countWord "lp.n")
    (.seq (countBlock "lp.A" "decode.count") (.seq (countBlock "lp.b" "lp.m")
      (.seq (countBlock "lp.c" "lp.n") (.assign "input.bits" (.var "size.total")))))))

set_option maxHeartbeats 800000 in
theorem prepareSize_spec (B H m n : ℕ) (P : Program ℚ m n)
    (h2 : 2 < B) (hH : 1 ≤ H) (hHB : H < B) (hmB : m < B) (hnB : n < B)
    (hmnB : m * n < B) (hA : ∀ i j, Height (P.A i j) H)
    (hb : ∀ i, Height (P.b i) H) (hc : ∀ j, Height (P.c j) H)
    (hL : bitSize (encodeProgram P) < B) :
    Spec B (RepresentsProgram P) prepareSize
      (fun σ τ => τ.vars "input.bits" = bitSize (encodeProgram P) ∧
        RepresentsProgram P τ ∧ τ.arrs = σ.arrs)
      ((36 * H.size + 61) * (m * n + m + n) + 12 * m.size + 12 * n.size + 56) := by
  let Avec : Fin (m * n) → ℚ := fun k => P.A k.divNat k.modNat
  let aBits := bitSize (encodeVector Avec)
  let bBits := bitSize (encodeVector P.b)
  let cBits := bitSize (encodeVector P.c)
  have hbits : bitSize (encodeProgram P) = m.size + n.size + 2 + aBits + bBits + cBits :=
    program_bits_flat P
  have hm := countWord_frame_spec B m 0 "lp.m" h2 hmB (by omega)
  have hn := countWord_frame_spec B n (m.size + 1) "lp.n" h2 hnB (by omega)
  have hmat := countBlock_spec B H (m * n) (m.size + n.size + 2) "lp.A" "decode.count" Avec
    h2 hH hHB hmnB (fun k => hA k.divNat k.modNat) (by omega)
  have hbound := countBlock_spec B H m (m.size + n.size + 2 + aBits) "lp.b" "lp.m" P.b
    h2 hH hHB hmB hb (by omega)
  have hobj := countBlock_spec B H n (m.size + n.size + 2 + aBits + bBits) "lp.c" "lp.n" P.c
    h2 hH hHB hnB hc (by omega)
  rintro σ ⟨hσA, hσb, hσc, hσm, hσn, hσcount⟩
  let C := 36 * H.size + 61
  have hcost : C * (m * n + m + n) = C * (m * n) + C * m + C * n := by simp only [Nat.mul_add]
  rw [hcost]
  dsimp only [C]
  run_vcg [hm, hn, hmat, hbound, hobj]
  all_goals clear hm hn hmat hbound hobj
  all_goals simp_all [RepresentsProgram, Represents, FieldsAgree, fields,
    RamMatrixStorage.flatten, Avec, aBits, bBits, cBits, Nat.mul_add]
  all_goals omega

end Lax109476Proofs.RamProgramSize

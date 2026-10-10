import Lax109476Proofs.RamCopyBlock
import Lax109476Proofs.RamPaddedFeasibility
import Lax109476Proofs.RamSolverFrontEnd

namespace Lax109476Proofs.RamFeasibilityQuery

open Lax109476.LinearProgram Lax109476.RationalEncoding Lax109476.RationalCertificates
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamMatrixStorage IntegerEncoding RationalArithmeticBounds RamCopyBlock

def copyInput : Com := .seq (copyBlock "int.A" "query.A" "decode.count")
  (.seq (copyBlock "int.b" "query.b" "lp.m")
    (.seq (.assign "source.m" (.var "lp.m"))
      (.seq (.assign "source.n" (.var "lp.n")) (.assign "source.bits" (.var "input.bits")))))

def Workspace (m n : ℕ) (σ : Env) : Prop :=
  Extents "query.A" (m * n) σ ∧ Extents "query.b" m σ ∧
    Extents "pad.A" ((m + 2) * (n + 2)) σ ∧ Extents "pad.b" (m + 2) σ ∧
    Extents "search.rows" (((m + 2) + (n + 2)) * (n + 2)) σ ∧
    Extents "search.rhs" ((m + 2) + (n + 2)) σ ∧
    Extents "ell.center" (n + 2) σ ∧ Extents "ell.shape" ((n + 2) * (n + 2)) σ ∧
    RamEllipsoidStep.Workspace (n + 2) σ ∧ Extents "ell.normal" (n + 2) σ

def Input {m n : ℕ} (P : Program ℚ m n) (σ : Env) : Prop :=
  RamClearProgram.IntegerRep P σ ∧ Workspace m n σ ∧
    σ.vars "lp.m" = m ∧ σ.vars "lp.n" = n ∧ σ.vars "decode.count" = m * n ∧
    σ.vars "input.bits" = bitSize (encodeProgram P)

set_option maxHeartbeats 800000 in
theorem copyInput_spec (m n : ℕ) (P : Program ℚ m n) (w : ℕ)
    (hw : RamDecoder.wordWidth (2 * bitSize (encodeProgram P)) ≤ w) :
    Spec (2 ^ w) (Input P) copyInput
      (fun _ τ => RamPaddedFeasibility.Input (integerProgram P) (bitSize (encodeProgram P)) τ)
      (71 * (m * n + m) + 58) := by
  let L := bitSize (encodeProgram P)
  let H := 2 ^ (2 * L)
  have hHB : H < 2 ^ w := Nat.pow_lt_pow_right (by decide)
    (by unfold RamDecoder.wordWidth at hw; omega)
  have hH : 1 ≤ H := Nat.one_le_pow _ _ (by decide)
  have hLB : L < 2 ^ w := (Nat.lt_two_pow_self (n := L)).trans
    ((Nat.pow_le_pow_right (by decide) (show L ≤ 2 * L by omega)).trans_lt hHB)
  have hcells := RamSolverInitialization.cells_bound P
  have hmB : m < 2 ^ w := (by omega : m ≤ L).trans_lt hLB
  have hnB : n < 2 ^ w := (by omega : n ≤ L).trans_lt hLB
  have hmnB : m * n < 2 ^ w := (by omega : m * n ≤ L).trans_lt hLB
  have h1 : 1 < 2 ^ w := hH.trans_lt hHB
  obtain ⟨hA, hb, hc⟩ := integerProgram_bounds P
  have hAH : ∀ k : Fin (m * n), Height ((rationalProgram (integerProgram P)).A k.divNat k.modNat) H := by
    intro k
    simpa [Height, rationalProgram, H, L] using And.intro (hA k.divNat k.modNat) hH
  have hbH : ∀ i, Height ((rationalProgram (integerProgram P)).b i) H := by
    intro i
    simpa [Height, rationalProgram, H, L] using And.intro (hb i) hH
  rintro σ ⟨⟨hσA, hσb, hσc⟩, hσW, hσm, hσn, hσcount, hσbits⟩
  rcases hσW with ⟨hσqA, hσqb, hσpA, hσpb, hσrows, hσrhs, hσcenter, hσshape, hσell, hσnormal⟩
  obtain ⟨τ, hr₁, hτqA, hτA⟩ := copyBlock_spec (2 ^ w) H (m * n) "int.A" "query.A" "decode.count"
    (fun k => (rationalProgram (integerProgram P)).A k.divNat k.modNat)
    h1 hmnB hHB hAH (by simp [RamCopy.Disjoint, RamCopy.suffixes]) σ ⟨hσA, hσqA, hσcount⟩
  have hτb : Represents "int.b" (List.ofFn (rationalProgram (integerProgram P)).b) τ :=
    RamReadBody.represents_frame _ _ hσb hr₁ (by intro s hs; simp at hs; rcases hs with rfl | rfl | rfl <;> simp [copyBlock_warrs])
  have hτm : τ.vars "lp.m" = m := (hr₁.frame_var _ (by rw [copyBlock_wvars]; decide)).trans hσm
  obtain ⟨υ, hr₂, hυqb, hυb⟩ := copyBlock_spec (2 ^ w) H m "int.b" "query.b" "lp.m"
    (rationalProgram (integerProgram P)).b h1 hmB hHB hbH
    (by simp [RamCopy.Disjoint, RamCopy.suffixes]) τ
    ⟨hτb, RamAdvanceState.extents_of_run hr₁ _ _ hσqb, hτm⟩
  have hrCopy := hr₁.seq hr₂
  have hυqA : Represents "query.A" (RamMatrixStorage.flatten (rationalProgram (integerProgram P)).A) υ :=
    RamReadBody.represents_frame _ _ hτqA hr₂ (by intro s hs; simp at hs; rcases hs with rfl | rfl | rfl <;> simp [copyBlock_warrs])
  have hυm : υ.vars "lp.m" = m := (hr₂.frame_var _ (by rw [copyBlock_wvars]; decide)).trans hτm
  have hυn : υ.vars "lp.n" = n := (hrCopy.frame_var _ (by simp [Com.wvars, copyBlock_wvars]; decide)).trans hσn
  have hυbits : υ.vars "input.bits" = L := (hrCopy.frame_var _ (by simp [Com.wvars, copyBlock_wvars]; decide)).trans hσbits
  have hmeta : Spec (2 ^ w)
      (fun ρ => ρ.vars "lp.m" = m ∧ ρ.vars "lp.n" = n ∧ ρ.vars "input.bits" = L)
      (.seq (.assign "source.m" (.var "lp.m"))
        (.seq (.assign "source.n" (.var "lp.n")) (.assign "source.bits" (.var "input.bits"))))
      (fun _ ρ => ρ.vars "source.m" = m ∧ ρ.vars "source.n" = n ∧ ρ.vars "source.bits" = L) 6 := by
    rintro ρ ⟨hρm, hρn, hρbits⟩
    run_vcg
    all_goals simp_all
  obtain ⟨ρ, hr₃, hρm, hρn, hρbits⟩ := hmeta υ ⟨hυm, hυn, hυbits⟩
  have hr := hr₁.seq (hr₂.seq hr₃)
  refine ⟨ρ, hr.mono (by omega), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · refine ⟨?_, ?_, ?_, ?_, hρm, hρn, hρbits⟩
    · exact RamReadBody.represents_frame _ _ hυqA hr₃ (by intro s hs; simp [Com.warrs])
    · exact RamReadBody.represents_frame _ _ hυqb hr₃ (by intro s hs; simp [Com.warrs])
    · exact RamAdvanceState.extents_of_run hr _ _ hσpA
    · exact RamAdvanceState.extents_of_run hr _ _ hσpb
  · exact RamAdvanceState.extents_of_run hr _ _ hσrows
  · exact RamAdvanceState.extents_of_run hr _ _ hσrhs
  · exact RamAdvanceState.extents_of_run hr _ _ hσcenter
  · exact RamAdvanceState.extents_of_run hr _ _ hσshape
  · exact RamAdvanceState.workspace_of_run hr _ hσell
  · exact RamAdvanceState.extents_of_run hr _ _ hσnormal

end Lax109476Proofs.RamFeasibilityQuery

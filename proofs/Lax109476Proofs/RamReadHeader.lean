import Lax109476Proofs.RamInput
import Lax109476Proofs.RamReadFraction
import Lax808846Proofs.Tactic

namespace Lax109476Proofs.RamReadHeader

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamInput

def rejectDimensions : Com := .seq (.assign "input.valid" (.lit 0))
  (.assign "decode.count" (.lit 0))

/-- Dimensions are tested against the actual payload length before any
matrix count is computed or array loop is entered. -/
def validateDimensions : Com := .seq
  (.assign "decode.bound" (.add (.var "input.remaining") (.lit 2)))
  (.ite (.lt (.var "lp.m") (.var "decode.bound"))
    (.ite (.lt (.var "lp.n") (.var "decode.bound"))
      (.assign "decode.count" (.mul (.var "lp.m") (.var "lp.n"))) rejectDimensions)
    rejectDimensions)

theorem validateDimensions_spec (B m n r v : ℕ) (hB : (r + 2) ^ 2 < B)
    (hm : m < B) (hn : n < B) :
    Spec B (fun σ => σ.vars "lp.m" = m ∧ σ.vars "lp.n" = n ∧
        σ.vars "input.remaining" = r ∧ σ.vars "input.valid" = v)
      validateDimensions
      (fun _ τ => τ.vars "lp.m" = m ∧ τ.vars "lp.n" = n ∧
        τ.vars "input.remaining" = r ∧
        τ.vars "input.valid" = (if m ≤ r + 1 ∧ n ≤ r + 1 then v else 0) ∧
        τ.vars "decode.count" = (if m ≤ r + 1 ∧ n ≤ r + 1 then m * n else 0)) 18 := by
  have h4 : 4 ≤ (r + 2) ^ 2 := by
    simpa using Nat.pow_le_pow_left (show 2 ≤ r + 2 by omega) 2
  have h2 : 2 < B := by omega
  have hrB : r < B := by nlinarith
  have hr2B : r + 2 < B := by nlinarith
  have hmul : m ≤ r + 1 → n ≤ r + 1 → m * n < B := by
    intro hmm hnn
    have := Nat.mul_le_mul hmm hnn
    nlinarith
  rintro σ ⟨hσm, hσn, hσr, hσv⟩
  run_vcg
  all_goals simp_all [Env.setVar]
  all_goals omega

def readHeader : Com := .seq (safeRead "lp.m")
  (.seq (safeRead "lp.n") validateDimensions)


def ValidDimensions (xs : List ℕ) : Prop :=
  xs.headD 0 ≤ (xs.drop 2).length + 1 ∧ xs.tail.headD 0 ≤ (xs.drop 2).length + 1

instance (xs : List ℕ) : Decidable (ValidDimensions xs) := by unfold ValidDimensions; infer_instance

theorem readHeader_spec (B M v : ℕ) (xs : List ℕ) (hB : (xs.length + 2) ^ 2 < B)
    (hM : M < B) (hv : v ≤ 1) (hwords : ∀ z ∈ xs, z ≤ M) :
    Spec B (fun σ => σ.inp = xs ∧ σ.vars "input.remaining" = xs.length ∧
        σ.vars "input.valid" = v ∧ σ.InpBounded B)
      readHeader
      (fun _ τ => τ.vars "lp.m" = xs.headD 0 ∧ τ.vars "lp.n" = xs.tail.headD 0 ∧
        τ.inp = xs.drop 2 ∧ τ.vars "input.remaining" = (xs.drop 2).length ∧
        τ.vars "input.valid" = (if 2 ≤ xs.length ∧ ValidDimensions xs then v else 0) ∧
        τ.vars "decode.count" = (if ValidDimensions xs then xs.headD 0 * xs.tail.headD 0 else 0) ∧
        τ.InpBounded B) 36 := by
  have h4 : 4 ≤ (xs.length + 2) ^ 2 := by
    simpa using Nat.pow_le_pow_left (show 2 ≤ xs.length + 2 by omega) 2
  have h1 : 1 < B := by omega
  have hxB : xs.length < B := by nlinarith
  rintro σ ⟨hσinp, hσrem, hσvalid, hσbound⟩
  obtain ⟨τ, hr₁, hτm, hτinp, hτrem, hτvalid⟩ := safeRead_spec B "lp.m" xs v h1 hxB hv
    (by decide) (by decide) σ ⟨hσinp, hσrem, hσvalid, hσbound⟩
  obtain ⟨υ, hr₂, hυn, hυinp, hυrem, hυvalid⟩ := safeRead_spec B "lp.n" xs.tail
    (if xs = [] then 0 else v) h1 (by simp only [List.length_tail]; omega)
    (by split_ifs <;> omega) (by decide) (by decide) τ
    ⟨hτinp, by simpa using hτrem, hτvalid, hr₁.inpBounded hσbound⟩
  have hυm := (hr₂.frame_var "lp.m" (by decide)).trans hτm
  have hυr : υ.vars "input.remaining" = (xs.drop 2).length := by
    simp only [List.length_tail, List.length_drop] at hυrem ⊢; omega
  have hυin : υ.inp = xs.drop 2 := by
    simpa only [← List.drop_one, List.drop_drop] using hυinp
  have hυv : υ.vars "input.valid" = if 2 ≤ xs.length then v else 0 := by
    cases xs with
    | nil => simpa using hυvalid
    | cons m ys => cases ys with
      | nil => simpa using hυvalid
      | cons n rest =>
        have hh : 2 ≤ (m :: n :: rest).length := by simp only [List.length_cons]; omega
        simpa [hh] using hυvalid
  have hguard : ((xs.drop 2).length + 2) ^ 2 < B :=
    (Nat.pow_le_pow_left (by simp only [List.length_drop]; omega) 2).trans_lt hB
  have hmB := (RamReadFraction.headD_le xs M hwords).trans_lt hM
  have hnB := (RamReadFraction.headD_le xs.tail M
    (fun z hz => hwords z (List.mem_of_mem_tail hz))).trans_lt hM
  obtain ⟨ξ, hr₃, hξm, hξn, hξr, hξv, hξcount⟩ := validateDimensions_spec B
    (xs.headD 0) (xs.tail.headD 0) (xs.drop 2).length (if 2 ≤ xs.length then v else 0)
    hguard hmB hnB υ ⟨hυm, hυn, hυr, hυv⟩
  have hrun := hr₁.seq (hr₂.seq hr₃)
  refine ⟨ξ, hrun, hξm, hξn, (hr₃.frame_inp (by decide)).trans hυin, hξr,
    ?_, hξcount, hrun.inpBounded hσbound⟩
  by_cases hd : ValidDimensions xs
  · have he : xs.headD 0 ≤ (xs.drop 2).length + 1 ∧ xs.tail.headD 0 ≤ (xs.drop 2).length + 1 := hd
    simpa only [if_pos he, hd, and_true] using hξv
  · have he : ¬(xs.headD 0 ≤ (xs.drop 2).length + 1 ∧ xs.tail.headD 0 ≤ (xs.drop 2).length + 1) := hd
    simpa only [if_neg he, hd, and_false, if_false] using hξv

end Lax109476Proofs.RamReadHeader

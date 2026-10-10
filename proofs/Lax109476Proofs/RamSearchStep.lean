import Lax109476Proofs.RamNormalSelection
import Lax109476Proofs.RamSeparation

open scoped Matrix BigOperators

namespace Lax109476Proofs.RamSearchStep

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamMatrixRows RamSeparation RamNormalSelection RamTrajectoryBounds
open RamEllipsoidStep RamEllipsoidBitBounds RamAdvanceState EllipsoidSearch RationalArithmeticBounds

theorem matrixRows_frame {B K : ℕ} {d : Com} {σ τ : Env} (hr : Run B d σ τ K)
    {m n : ℕ} (a : String) (A : Matrix (Fin m) (Fin n) ℚ) (hσ : MatrixRows a A σ)
    (hs : a ++ ".s" ∉ d.warrs) (hn : a ++ ".n" ∉ d.warrs) (hd : a ++ ".d" ∉ d.warrs) :
    MatrixRows a A τ := by
  intro i
  simpa only [Slice, hr.frame_arr _ hs, hr.frame_arr _ hn, hr.frame_arr _ hd] using hσ i

def advanceKeepingRows : Com := .seq (.assign "search.savedm" (.var "row.m"))
  (.seq advanceState (.assign "row.m" (.var "search.savedm")))

def cutOrFinish : Com := .ite (.lt (.var "row.first") (.var "row.m"))
  (.seq (selectNormal "search.rows") advanceKeepingRows)
  (.seq (.assign "search.found" (.lit 1)) (.assign "search.limit" (.var "iter.k")))

def searchStep : Com := .seq (separateRows "search.rows" "ell.center" "search.rhs") cutOrFinish

def cost (m n K l : ℕ) : ℕ :=
  ((rowCost n (2 ^ stateBits n K l) + 20) * m + 8) + 126 * n + 83 +
    (stepCost n (2 ^ stateBits n K l) (2 ^ magnitudeExponent n (stateBits n K l) K) +
      71 * n + 71 * (n * n) + 60) + 12

def State {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ) (k : ℕ) (σ : Env) : Prop :=
  Represents "ell.shape" (RamMatrixStorage.flatten (trajectory A b k).1) σ ∧
    Represents "ell.center" (List.ofFn (trajectory A b k).2) σ ∧ Workspace n σ ∧
    Extents "ell.normal" n σ ∧ MatrixRows "search.rows" (fun i j => (A i j : ℚ)) σ ∧
    Represents "search.rhs" (List.ofFn b) σ ∧ σ.vars "vec.n" = n ∧
    σ.vars "row.m" = m ∧ σ.vars "iter.k" = k

-- The iteration-loop proof will use this fixed body and a variant
-- `search.limit - iter.k`; success lowers the limit to the current index.

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
theorem searchStep_spec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ)
    (hn : 2 ≤ n) (K l k N w : ℕ) (hk : k < N) (hNK : N ≤ K)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ l) (hb : ∀ i, Height (b i) (2 ^ l))
    (hw : wordWidth n (stateBits n K l) K ≤ w)
    (hdims : m + n + m * n + 1 < 2 ^ w)
    (hsep : 2 * (RamDotProduct.cap n (2 ^ stateBits n K l)) ^ 2 + 3 < 2 ^ w) :
    Spec (2 ^ w) (fun σ => State A b k σ ∧ σ.vars "search.limit" = N ∧ σ.vars "search.found" = 0)
      searchStep
      (fun _ τ => if RationalSeparation.firstViolation A b (trajectory A b k).2 = none then
          State A b k τ ∧ τ.vars "search.limit" = k ∧ τ.vars "search.found" = 1
        else State A b (k + 1) τ ∧ τ.vars "search.limit" = N ∧ τ.vars "search.found" = 0)
      (cost m n K l) := by
  let H := 2 ^ stateBits n K l
  change 2 * (RamDotProduct.cap n H) ^ 2 + 3 < 2 ^ w at hsep
  have hH : 1 ≤ H := Nat.one_le_pow _ _ (by decide)
  have h1 : 1 < 2 ^ w := by omega
  have hHB : H < 2 ^ w := by
    have hh := (RamDotProduct.cap_ge n H hH).2
    have hp : RamDotProduct.cap n H ≤ (RamDotProduct.cap n H) ^ 2 :=
      le_self_pow (hH.trans hh) (by decide : (2 : ℕ) ≠ 0)
    omega
  have hinput : 2 ^ l ≤ H := Nat.pow_le_pow_right (by decide) (by unfold stateBits; omega)
  have hAH : ∀ i j, (A i j).natAbs ≤ H := fun i j => (hA i j).trans hinput
  have hbH : ∀ i, Height (b i) H := fun i => height_mono _ (hb i) hinput
  have hkK : k ≤ K := by omega
  have hstate := trajectory_heights A b hn K l k hkK
  have hs := RamFrame.spec_with_write_frame ["search.limit", "search.found", "iter.k", "row.m", "vec.n"]
    (separateRows_integer_spec (2 ^ w) m n H "search.rows" "ell.center" "search.rhs" A b
      (trajectory A b k).2 hH hAH hbH hstate.2 hdims hsep)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)
  rintro σ ⟨⟨hσA, hσc, hσwork, hσnormal, hσrows, hσrhs, hσn, hσm, hσk⟩, hσlimit, hσfound⟩
  obtain ⟨τ, hr₁, ⟨hτfirst, hτarr⟩, hτvars, _⟩ := hs σ ⟨hσrows, hσc, hσrhs, hσm, hσn⟩
  clear hs
  have hτA : Represents "ell.shape" (RamMatrixStorage.flatten (trajectory A b k).1) τ := by
    simpa only [Represents, hτarr] using hσA
  have hτc : Represents "ell.center" (List.ofFn (trajectory A b k).2) τ := by
    simpa only [Represents, hτarr] using hσc
  have hτrows : MatrixRows "search.rows" (fun i j => (A i j : ℚ)) τ := by
    simpa only [MatrixRows, Slice, hτarr] using hσrows
  have hτrhs : Represents "search.rhs" (List.ofFn b) τ := by simpa only [Represents, hτarr] using hσrhs
  have hτwork := workspace_of_run hr₁ n hσwork
  have hτnormal := extents_of_run hr₁ "ell.normal" n hσnormal
  have hτn : τ.vars "vec.n" = n := (hτvars _ (by simp)).trans hσn
  have hτm : τ.vars "row.m" = m := (hτvars _ (by simp)).trans hσm
  have hτk : τ.vars "iter.k" = k := (hτvars _ (by simp)).trans hσk
  have hτlimit : τ.vars "search.limit" = N := (hτvars _ (by simp)).trans hσlimit
  have hτfound : τ.vars "search.found" = 0 := (hτvars _ (by simp)).trans hσfound
  have hmB : m < 2 ^ w := by omega
  have hτmB : τ.vars "row.m" < 2 ^ w := by omega
  have hfirstB : τ.vars "row.first" < 2 ^ w := by
    rw [hτfirst]
    cases hf : RationalSeparation.firstViolation A b (trajectory A b k).2 with
    | none => simpa using hmB
    | some i => simpa using i.isLt.trans hmB
  cases hf : RationalSeparation.firstViolation A b (trajectory A b k).2 with
  | none =>
    have hτfirst' : τ.vars "row.first" = m := by simpa only [hf, Option.map_none, Option.getD_none] using hτfirst
    have hcond : (Cond.lt (.var "row.first") (.var "row.m")).evalB (2 ^ w) τ = some false := by
      simpa [hτfirst', hτm] using (evalB_condLt (evalB_var hfirstB) (evalB_var hτmB))
    have hkB : k < 2 ^ w := by
      have hp := (magnitude_parameters n (stateBits n K l) K).1
      have hguard := wordWidth_sufficient n (stateBits n K l) K w hw
      have hparams := RamEllipsoidWordBounds.unified_word_bounds _ _ n hn hp hguard
      have hpow : K < 2 ^ (2 * K + 3 * n + 9) := by
        have := Nat.lt_two_pow_self (n := 2 * K + 3 * n + 9)
        omega
      exact (Nat.lt_of_le_of_lt hkK hpow).trans_le
        ((magnitude_parameters n (stateBits n K l) K).2.2.1.trans hparams.2.1.le)
    have hf₁ : Run (2 ^ w) (.assign "search.found" (.lit 1)) τ (τ.setVar "search.found" 1) 2 :=
      Run.assign (evalB_lit h1)
    have hf₂ : Run (2 ^ w) (.assign "search.limit" (.var "iter.k")) (τ.setVar "search.found" 1)
        ((τ.setVar "search.found" 1).setVar "search.limit" k) 2 :=
      Run.assign (by simpa [hτk] using (evalB_var (B := 2 ^ w)
        (σ := τ.setVar "search.found" 1) (x := "iter.k") (by simpa [hτk] using hkB)))
    have hrun := hr₁.seq (Run.ite_false
      (c := .seq (selectNormal "search.rows") advanceKeepingRows) hcond (hf₁.seq hf₂))
    refine ⟨_, hrun.mono ?_, ?_⟩
    · simp only [cost, Cond.size, Expr.size, H, Nat.add_assoc, Nat.reduceAdd]
      omega
    · simp only [hf, if_pos rfl]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      all_goals simp_all [State, Represents, MatrixRows, Slice, Workspace, Extents]
  | some i =>
    have hτfirst' : τ.vars "row.first" = i.val := by simpa only [hf, Option.map_some, Option.getD_some] using hτfirst
    have hcond : (Cond.lt (.var "row.first") (.var "row.m")).evalB (2 ^ w) τ = some true := by
      simpa [hτfirst', hτm, i.isLt] using (evalB_condLt (evalB_var hfirstB) (evalB_var hτmB))
    obtain ⟨υ, hr₂, hυnormal, hυn⟩ := selectNormal_integer_spec (2 ^ w) m n H "search.rows" A b
      (trajectory A b k).2 (by omega) h1 hdims hH hHB hAH
      (by simp [RamCopy.Disjoint, RamCopy.suffixes]) τ
      ⟨hτrows, hτnormal, hτn, hτm, hτfirst⟩
    have hυA := RamEllipsoidUpdate.represents_frame hr₂ "ell.shape" _ hτA (by decide) (by decide) (by decide)
    have hυc := RamEllipsoidUpdate.represents_frame hr₂ "ell.center" _ hτc (by decide) (by decide) (by decide)
    have hυwork := workspace_of_run hr₂ n hτwork
    have hυk : υ.vars "iter.k" = k := (hr₂.frame_var _ (by decide)).trans hτk
    have hυm : υ.vars "row.m" = m := (hr₂.frame_var _ (by decide)).trans hτm
    have hsave : Run (2 ^ w) (.assign "search.savedm" (.var "row.m")) υ (υ.setVar "search.savedm" m) 2 :=
      Run.assign (by simpa [hυm] using (evalB_var (B := 2 ^ w) (σ := υ) (x := "row.m") (by omega)))
    obtain ⟨ξ, hr₃, hξc, hξA, hξwork, hξn, hξk⟩ := trajectory_advance_spec A b hn K l k w hkK hA hw
      (υ.setVar "search.savedm" m)
      ⟨by simpa only [Represents, arrs_setVar] using hυA,
        by simpa only [Represents, arrs_setVar] using hυnormal,
        by simpa only [Represents, arrs_setVar] using hυc,
        by simpa only [Workspace, Extents, arrs_setVar] using hυwork,
        by simpa using hυn, by simpa using hυk⟩
    have hξsaved : ξ.vars "search.savedm" = m := by
      simpa using (hr₃.frame_var "search.savedm" (by decide))
    have hrestore : Run (2 ^ w) (.assign "row.m" (.var "search.savedm")) ξ (ξ.setVar "row.m" m) 2 :=
      Run.assign (by simpa [hξsaved] using (evalB_var (B := 2 ^ w) (σ := ξ) (x := "search.savedm") (by omega)))
    have hadvance := hsave.seq (hr₃.seq hrestore)
    have hrun := hr₁.seq (Run.ite_true
      (d := .seq (.assign "search.found" (.lit 1)) (.assign "search.limit" (.var "iter.k")))
      hcond (hr₂.seq hadvance))
    have hξrows := matrixRows_frame hrun "search.rows" _ hσrows (by decide) (by decide) (by decide)
    have hξrhs := RamEllipsoidUpdate.represents_frame hrun "search.rhs" _ hσrhs (by decide) (by decide) (by decide)
    have hξnormal := extents_of_run hrun "ell.normal" n hσnormal
    have hξlimit : (ξ.setVar "row.m" m).vars "search.limit" = N :=
      ((hr₂.seq hadvance).frame_var _ (by decide)).trans hτlimit
    have hξfound : (ξ.setVar "row.m" m).vars "search.found" = 0 :=
      ((hr₂.seq hadvance).frame_var _ (by decide)).trans hτfound
    refine ⟨_, hrun.mono ?_, ?_⟩
    · simp only [cost, Cond.size, Expr.size, H, Nat.add_assoc, Nat.reduceAdd]
      omega
    · simp only [hf, reduceCtorEq, if_false]
      refine ⟨⟨?_, ?_, ?_, hξnormal, hξrows, hξrhs, ?_, ?_, ?_⟩, hξlimit, hξfound⟩
      all_goals simp_all [Represents, Workspace, Extents]

end Lax109476Proofs.RamSearchStep

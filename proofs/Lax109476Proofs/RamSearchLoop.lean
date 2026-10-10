import Lax109476Proofs.RamSearchStep
import Lax109476Proofs.RamInitialState

open scoped Matrix BigOperators

namespace Lax109476Proofs.RamSearchLoop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamSearchStep EllipsoidSearch

def Invariant {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ) (N : ℕ) (σ : Env) : Prop :=
  ∃ k ≤ N, State A b k σ ∧
    (∀ j < k, RationalSeparation.firstViolation A b (trajectory A b j).2 ≠ none) ∧
    ((σ.vars "search.found" = 0 ∧ σ.vars "search.limit" = N) ∨
      (σ.vars "search.found" = 1 ∧ σ.vars "search.limit" = k ∧
        k < N ∧ RationalSeparation.firstViolation A b (trajectory A b k).2 = none))

def searchLoop : Com := .while (.lt (.var "iter.k") (.var "search.limit")) searchStep

theorem body_spec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ)
    (hn : 2 ≤ n) (N l w : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ l)
    (hb : ∀ i, RationalArithmeticBounds.Height (b i) (2 ^ l))
    (hw : RamEllipsoidBitBounds.wordWidth n (RamTrajectoryBounds.stateBits n N l) N ≤ w)
    (hdims : m + n + m * n + 1 < 2 ^ w)
    (hsep : 2 * (RamDotProduct.cap n (2 ^ RamTrajectoryBounds.stateBits n N l)) ^ 2 + 3 < 2 ^ w) :
    Spec (2 ^ w) (fun σ => Invariant A b N σ ∧
        (Cond.lt (.var "iter.k") (.var "search.limit")).evalB (2 ^ w) σ = some true)
      searchStep
      (fun σ τ => Invariant A b N τ ∧
        τ.vars "search.limit" - τ.vars "iter.k" < σ.vars "search.limit" - σ.vars "iter.k")
      (cost m n N l) := by
  rintro σ ⟨⟨k, hkN, hσstate, hprior, hstatus⟩, hcond⟩
  have hσk : σ.vars "iter.k" = k := hσstate.2.2.2.2.2.2.2.2
  have hlt := lt_of_condLt_true hcond
  have hσfound : σ.vars "search.found" = 0 := by
    rcases hstatus with h | h
    · exact h.1
    · omega
  have hσlimit : σ.vars "search.limit" = N := by
    rcases hstatus with h | h
    · exact h.2
    · omega
  have hk : k < N := by omega
  obtain ⟨τ, hr, hτ⟩ := searchStep_spec A b hn N l k N w hk le_rfl hA hb hw hdims hsep
    σ ⟨hσstate, hσlimit, hσfound⟩
  by_cases hf : RationalSeparation.firstViolation A b (trajectory A b k).2 = none
  · simp only [if_pos hf] at hτ
    have hτk : τ.vars "iter.k" = k := hτ.1.2.2.2.2.2.2.2.2
    refine ⟨τ, hr, ⟨k, hkN, hτ.1, hprior, Or.inr ⟨hτ.2.2, hτ.2.1, hk, hf⟩⟩, ?_⟩
    omega
  · simp only [if_neg hf] at hτ
    have hτk : τ.vars "iter.k" = k + 1 := hτ.1.2.2.2.2.2.2.2.2
    refine ⟨τ, hr, ⟨k + 1, by omega, hτ.1, ?_, Or.inl ⟨hτ.2.2, hτ.2.1⟩⟩, ?_⟩
    · intro j hj
      by_cases hjk : j < k
      · exact hprior j hjk
      · have heq : j = k := by omega
        exact heq ▸ hf
    · omega

theorem searchLoop_spec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ)
    (hn : 2 ≤ n) (N l w : ℕ) (hNB : N < 2 ^ w)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ l)
    (hb : ∀ i, RationalArithmeticBounds.Height (b i) (2 ^ l))
    (hw : RamEllipsoidBitBounds.wordWidth n (RamTrajectoryBounds.stateBits n N l) N ≤ w)
    (hdims : m + n + m * n + 1 < 2 ^ w)
    (hsep : 2 * (RamDotProduct.cap n (2 ^ RamTrajectoryBounds.stateBits n N l)) ^ 2 + 3 < 2 ^ w) :
    Spec (2 ^ w) (fun σ => State A b 0 σ ∧ σ.vars "search.limit" = N ∧ σ.vars "search.found" = 0)
      searchLoop
      (fun _ τ => Invariant A b N τ ∧
        (Cond.lt (.var "iter.k") (.var "search.limit")).evalB (2 ^ w) τ = some false)
      ((cost m n N l + 4) * N + 4) := by
  apply Spec.while_count (Invariant A b N)
    (fun σ => σ.vars "search.limit" - σ.vars "iter.k") (cost m n N l)
  · rintro σ ⟨k, hkN, hstate, hprior, hstatus⟩
    have hσk : σ.vars "iter.k" = k := hstate.2.2.2.2.2.2.2.2
    have hkB : σ.vars "iter.k" < 2 ^ w := by omega
    have hlimitB : σ.vars "search.limit" < 2 ^ w := by rcases hstatus with h | h <;> omega
    exact evalB_condLt_vars hkB hlimitB
  · exact body_spec A b hn N l w hA hb hw hdims hsep
  · rintro σ ⟨hstate, hlimit, hfound⟩
    exact ⟨0, Nat.zero_le N, hstate, by intro j hj; omega, Or.inl ⟨hfound, hlimit⟩⟩
  · rintro σ ⟨hstate, hlimit, hfound⟩
    have hσk : σ.vars "iter.k" = 0 := hstate.2.2.2.2.2.2.2.2
    simp only [Cond.size, Expr.size, hlimit, hσk, Nat.sub_zero]
    rw [show 1 + (1 + 1 + 1) + cost m n N l = cost m n N l + 4 by omega]

theorem invariant_outcome {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ)
    (N B : ℕ) (σ : Env) (hI : Invariant A b N σ)
    (hfalse : (Cond.lt (.var "iter.k") (.var "search.limit")).evalB B σ = some false) :
    findFirst (fun j => decide (RationalSeparation.firstViolation A b (trajectory A b j).2 = none)) 0 N =
      if σ.vars "search.found" = 1 then some (σ.vars "iter.k") else none := by
  obtain ⟨k, hkN, hstate, hprior, hstatus⟩ := hI
  have hσk : σ.vars "iter.k" = k := hstate.2.2.2.2.2.2.2.2
  have hle := le_of_condLt_false hfalse
  rcases hstatus with ⟨hf, hlimit⟩ | ⟨hf, hlimit, hk, hsuccess⟩
  · have heq : k = N := by omega
    simp only [hf, Nat.zero_ne_one, if_false, findFirst_eq_find, List.find?_eq_none]
    intro j hj
    have hjN : j < N := by simpa using hj
    simpa only [decide_eq_true_eq] using hprior j (by omega)
  · simp only [hf, if_pos rfl, hσk, findFirst_eq_find]
    apply List.find?_range'_eq_some.mpr
    refine ⟨by simp [hsuccess], by simpa using hk, ?_⟩
    intro j _ hj
    simp [hprior j hj]

def search : Com := .seq (.assign "search.limit" (.var "search.budget"))
  (.seq (.assign "search.found" (.lit 0)) (.seq RamInitialState.initialState searchLoop))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
theorem search_spec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ)
    (hn : 2 ≤ n) (N l w : ℕ) (hNB : N < 2 ^ w)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ l)
    (hb : ∀ i, RationalArithmeticBounds.Height (b i) (2 ^ l))
    (hw : RamEllipsoidBitBounds.wordWidth n (RamTrajectoryBounds.stateBits n N l) N ≤ w)
    (hdims : m + n + m * n + 1 < 2 ^ w)
    (hsep : 2 * (RamDotProduct.cap n (2 ^ RamTrajectoryBounds.stateBits n N l)) ^ 2 + 3 < 2 ^ w) :
    Spec (2 ^ w) (fun σ => RamMatrixRows.MatrixRows "search.rows" (fun i j => (A i j : ℚ)) σ ∧
        RamRationalArrays.Represents "search.rhs" (List.ofFn b) σ ∧
        RamEllipsoidStep.Extents "ell.center" n σ ∧ RamEllipsoidStep.Extents "ell.shape" (n * n) σ ∧
        RamEllipsoidStep.Workspace n σ ∧ RamEllipsoidStep.Extents "ell.normal" n σ ∧
        σ.vars "vec.n" = n ∧ σ.vars "row.m" = m ∧ σ.vars "search.budget" = N)
      search
      (fun _ τ => Invariant A b N τ ∧
        findFirst (fun j => decide (RationalSeparation.firstViolation A b (trajectory A b j).2 = none)) 0 N =
          if τ.vars "search.found" = 1 then some (τ.vars "iter.k") else none)
      (33 * n + 76 * (n * n) + (cost m n N l + 4) * N + 64) := by
  have h1 : 1 < 2 ^ w := by omega
  have hnB : n < 2 ^ w := by omega
  have hparams := RamEllipsoidBitBounds.magnitude_parameters n (RamTrajectoryBounds.stateBits n N l) N
  have hguard := RamEllipsoidBitBounds.wordWidth_sufficient n (RamTrajectoryBounds.stateBits n N l) N w hw
  have hbds := RamEllipsoidWordBounds.unified_word_bounds _ _ n hn hparams.1 hguard
  have hnnB : n * n < 2 ^ w := by simpa only [pow_two] using hbds.2.2.1
  rintro σ ⟨hσrows, hσrhs, hσc, hσA, hσwork, hσnormal, hσn, hσm, hσbudget⟩
  have hr₁ : Run (2 ^ w) (.assign "search.limit" (.var "search.budget")) σ
      (σ.setVar "search.limit" N) 2 :=
    Run.assign (by simpa [hσbudget] using (evalB_var (B := 2 ^ w) (σ := σ) (x := "search.budget") (by omega)))
  have hr₂ : Run (2 ^ w) (.assign "search.found" (.lit 0)) (σ.setVar "search.limit" N)
      ((σ.setVar "search.limit" N).setVar "search.found" 0) 2 := Run.assign (evalB_lit (by omega))
  obtain ⟨τ, hr₃, hτc, hτA, hτwork, hτn, hτk⟩ := RamInitialState.initialState_spec (2 ^ w) n hnB hnnB h1
    ((σ.setVar "search.limit" N).setVar "search.found" 0)
    ⟨by simpa only [RamEllipsoidStep.Extents, arrs_setVar] using hσc,
      by simpa only [RamEllipsoidStep.Extents, arrs_setVar] using hσA,
      by simpa only [RamEllipsoidStep.Workspace, RamEllipsoidStep.Extents, arrs_setVar] using hσwork,
      by simpa using hσn⟩
  have hinit := hr₁.seq (hr₂.seq hr₃)
  have hτrows := matrixRows_frame hinit "search.rows" _ hσrows (by decide) (by decide) (by decide)
  have hτrhs := RamEllipsoidUpdate.represents_frame hinit "search.rhs" _ hσrhs (by decide) (by decide) (by decide)
  have hτnormal := RamAdvanceState.extents_of_run hinit "ell.normal" n hσnormal
  have hτm : τ.vars "row.m" = m := (hinit.frame_var _ (by decide)).trans hσm
  have hτlimit : τ.vars "search.limit" = N := by simpa using (hr₃.frame_var "search.limit" (by decide))
  have hτfound : τ.vars "search.found" = 0 := by simpa using (hr₃.frame_var "search.found" (by decide))
  have hτstate : State A b 0 τ := ⟨hτA, hτc, hτwork, hτnormal, hτrows, hτrhs, hτn, hτm, hτk⟩
  obtain ⟨υ, hr₄, hυI, hυfalse⟩ := searchLoop_spec A b hn N l w hNB hA hb hw hdims hsep
    τ ⟨hτstate, hτlimit, hτfound⟩
  refine ⟨υ, (hr₁.seq (hr₂.seq (hr₃.seq hr₄))).mono ?_, hυI, invariant_outcome A b N _ υ hυI hυfalse⟩
  omega

end Lax109476Proofs.RamSearchLoop

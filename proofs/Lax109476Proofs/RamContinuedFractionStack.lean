import Lax109476Proofs.ContinuedFractionBounds

namespace Lax109476Proofs.RamContinuedFractionStack

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RationalReconstruction
open RamContinuedFractionStep ContinuedFractionBounds

def Stack (q : ℚ) (j : ℕ) (σ : Env) : Prop :=
  ∀ i < j, (σ.arrs "cf.stack").getD i 0 = (Int.floor (tail^[i] q)).toNat

def forwardStep : Com := .seq RamContinuedFractionStep.step
  (.seq (.store "cf.stack" (.var "cf.i") (.var "cf.a"))
    (.seq resultToLeft (.assign "cf.i" (.add (.var "cf.i") (.lit 1)))))

def Invariant (q : ℚ) (N K : ℕ) (σ : Env) : Prop :=
  Stack q (σ.vars "cf.i") σ ∧ (σ.arrs "cf.stack").length = N ∧
    LeftValue (tail^[σ.vars "cf.i"] q) σ ∧ σ.vars "cf.i" ≤ K ∧ σ.vars "cf.limit" = K

set_option maxHeartbeats 800000 in
theorem forwardStep_spec (B M N K : ℕ) (q : ℚ) (hq : 0 ≤ q) (hh : Height q M)
    (h1 : 1 < B) (hMB : M < B) (hKB : K < B) (hKN : K ≤ N) :
    Spec B (fun σ => Invariant q N K σ ∧ σ.vars "cf.i" < K) forwardStep
      (fun σ τ => Invariant q N K τ ∧ τ.vars "cf.i" = σ.vars "cf.i" + 1)
      (36 * M.size + 109) := by
  rintro σ ⟨⟨hσstack, hσlen, hσleft, hσi, hσK⟩, hi⟩
  let j := σ.vars "cf.i"
  let r := tail^[j] q
  have hr := iterated_tail_height q M j hq hh
  obtain ⟨τ, hr₁, hτa, hτtail⟩ := step_nonnegative_spec B M r hr.1 h1 hMB hr.2 σ hσleft
  have hτi : τ.vars "cf.i" = j := hr₁.frame_var _ (by decide)
  have hτlen : (τ.arrs "cf.stack").length = N := by
    rw [hr₁.frame_arr "cf.stack" (by decide)]
    exact hσlen
  have hτaB : τ.vars "cf.a" < B := by
    rw [hτa, floor_toNat r hr.1]
    exact ((Nat.div_le_self _ _).trans hr.2.1).trans_lt hMB
  have hjiB : j < B := hi.trans hKB
  have hjN : j < N := hi.trans_le hKN
  have hr₂ : Run B (.store "cf.stack" (.var "cf.i") (.var "cf.a")) τ
      (τ.setArr "cf.stack" j (Int.floor r).toNat) 3 := by
    apply Run.store
    · simpa only [hτi] using evalB_var (B := B) (σ := τ) (x := "cf.i") (hτi ▸ hjiB)
    · simpa only [hτa] using evalB_var (B := B) (σ := τ) (x := "cf.a") hτaB
    · rw [hτlen]; exact hi.trans_le hKN
  let υ := τ.setArr "cf.stack" j (Int.floor r).toNat
  have hυtail : FractionOutput (tail r) υ := hτtail
  have htHeight := tail_height r M hr.1 hr.2
  obtain ⟨ρ, hr₃, hρleft⟩ := resultToLeft_spec B (tail r) h1
    (htHeight.1.trans_lt hMB) (htHeight.2.trans_lt hMB) υ hυtail
  have hρi : ρ.vars "cf.i" = j := (hr₃.frame_var _ (by decide)).trans hτi
  have hsumB : Bop.add.apply (ρ.vars "cf.i") 1 < B := by simpa [hρi] using lt_of_le_of_lt hi hKB
  have hr₄ : Run B (.assign "cf.i" (.add (.var "cf.i") (.lit 1))) ρ (ρ.setVar "cf.i" (j + 1)) 4 :=
    Run.assign (by simpa only [hρi, Bop.apply_add] using (evalB_bin
      (evalB_var (B := B) (σ := ρ) (x := "cf.i") (hρi ▸ hjiB)) (evalB_lit h1) hsumB))
  have hstack : Stack q (j + 1) (ρ.setVar "cf.i" (j + 1)) := by
    intro i hii
    change (ρ.arrs "cf.stack").getD i 0 = _
    rw [hr₃.frame_arr "cf.stack" (by decide)]
    change ((τ.arrs "cf.stack").set j (Int.floor r).toNat).getD i 0 = _
    by_cases hij : i = j
    · subst i
      simp [List.getD_eq_getElem?_getD, List.getElem?_set, hτlen, hjN, r]
    · have hiold : i < j := by omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_set, Ne.symm hij, ↓reduceIte]
      rw [hr₁.frame_arr "cf.stack" (by decide)]
      simpa only [List.getD_eq_getElem?_getD] using hσstack i hiold
  have hlen : ((ρ.setVar "cf.i" (j + 1)).arrs "cf.stack").length = N := by
    rw [arrs_setVar, hr₃.frame_arr "cf.stack" (by decide)]
    simp only [υ, Env.setArr, ite_true, List.length_set, hτlen]
  have hleft : LeftValue (tail^[j + 1] q) (ρ.setVar "cf.i" (j + 1)) := by
    simpa [LeftValue, vars_setVar, Function.iterate_succ_apply', r] using hρleft
  have hlimit : (ρ.setVar "cf.i" (j + 1)).vars "cf.limit" = K :=
    ((hr₁.seq (hr₂.seq (hr₃.seq hr₄))).frame_var _ (by decide)).trans hσK
  refine ⟨_, hr₁.seq (hr₂.seq (hr₃.seq hr₄)), ⟨hstack, hlen, ?_, ?_, hlimit⟩, ?_⟩
  · simpa only [vars_setVar, ite_true] using hleft
  · change j + 1 ≤ K; exact hi
  · simp [j]

def forward : Com := .seq (.assign "cf.i" (.lit 0))
  (.while (.lt (.var "cf.i") (.var "cf.limit")) forwardStep)

theorem forward_spec (B M N K : ℕ) (q : ℚ) (hq : 0 ≤ q) (hh : Height q M)
    (h1 : 1 < B) (hMB : M < B) (hKB : K < B) (hKN : K ≤ N) :
    Spec B (fun σ => (σ.arrs "cf.stack").length = N ∧ LeftValue q σ ∧ σ.vars "cf.limit" = K)
      forward (fun _ τ => Stack q K τ ∧ (τ.arrs "cf.stack").length = N ∧
        LeftValue (tail^[K] q) τ ∧ τ.vars "cf.i" = K)
      ((36 * M.size + 113) * K + 6) := by
  have hlo := Spec.forRangeZero "cf.i" "cf.limit" (Invariant q N K) K (36 * M.size + 109) hKB
    (fun _ h => h.2.2.2.1) (fun _ h => h.2.2.2.2)
    (forwardStep_spec B M N K q hq hh h1 hMB hKB hKN)
  refine (hlo.pre ?_).post ?_
  · rintro σ ⟨hlen, hleft, hK⟩
    exact ⟨by intro i hi; simp at hi, hlen, hleft, by simp, hK⟩
  · rintro σ τ _ ⟨hτ, hcounter⟩
    simpa only [hcounter] using And.intro hτ.1 (And.intro hτ.2.1 (And.intro hτ.2.2.1 hcounter))

end Lax109476Proofs.RamContinuedFractionStack

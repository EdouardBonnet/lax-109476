import Lax109476Proofs.RamContinuedFractionStack
import Lax109476Proofs.ContinuedFractionFold

namespace Lax109476Proofs.RamContinuedFractionFoldStep

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RationalReconstruction
open RamContinuedFractionStack ContinuedFractionBounds ContinuedFractionFold

def restoreFloor : Com := .seq (.assign "left.s" (.lit 0))
  (.seq (.assign "left.n" (.get "cf.stack" (.var "cf.back"))) (.assign "left.d" (.lit 1)))

 theorem restoreFloor_spec (B N i a : ℕ) (hi : i < N) (hiB : i < B) (h1 : 1 < B) (haB : a < B) :
    Spec B (fun σ => (σ.arrs "cf.stack").length = N ∧
        (σ.arrs "cf.stack").getD i 0 = a ∧ σ.vars "cf.back" = i)
      restoreFloor (fun _ τ => LeftValue (a : ℚ) τ) 7 := by
  rintro σ ⟨hσlen, hσa, hσi⟩
  have hil : i < (σ.arrs "cf.stack").length := hσlen ▸ hi
  run_vcg
  all_goals simp_all [LeftValue, fractionValue]

 def foldStep : Com := .seq
  (.assign "cf.back" (.sub (.sub (.var "cf.limit") (.var "cf.done")) (.lit 1)))
  (.seq resultToLeft (.seq invertFraction (.seq resultToRight
    (.seq restoreFloor (.seq addFraction (.assign "cf.done" (.add (.var "cf.done") (.lit 1))))))))

 def Invariant (q : ℚ) (N K : ℕ) (σ : Env) : Prop :=
  Stack q K σ ∧ (σ.arrs "cf.stack").length = N ∧ σ.vars "cf.done" ≤ K ∧
    σ.vars "cf.limit" = K ∧ FractionOutput (ContinuedFractionFold.fold q K (σ.vars "cf.done")) σ

set_option maxHeartbeats 800000 in
theorem foldStep_spec (B M N K : ℕ) (q : ℚ) (hq : 0 ≤ q) (hh : Height q M)
    (hKB : K < B) (hKN : K ≤ N) (hB : 2 * ((2 * M) ^ (K + 1)) ^ 2 + 3 < B) :
    Spec B (fun σ => Invariant q N K σ ∧ σ.vars "cf.done" < K) foldStep
      (fun σ τ => Invariant q N K τ ∧ τ.vars "cf.done" = σ.vars "cf.done" + 1)
      (108 * ((2 * M) ^ (K + 1)).size + 204) := by
  let R := (2 * M) ^ (K + 1)
  have hM : 1 ≤ M := le_trans q.den_pos hh.2
  have hR : 1 ≤ R := Nat.one_le_pow _ _ (by omega)
  have hMR : M ≤ R := (by omega : M ≤ 2 * M).trans
    (le_self_pow (by omega : 1 ≤ 2 * M) (by omega : K + 1 ≠ 0))
  have hRB : R < B := by dsimp only [R] at *; nlinarith
  have h1 : 1 < B := by nlinarith
  rintro σ ⟨⟨hσstack, hσlen, hσdone, hσK, hσresult⟩, ht⟩
  let t := σ.vars "cf.done"
  let j := K - (t + 1)
  let r := ContinuedFractionFold.fold q K t
  let a := (Int.floor (tail^[j] q)).toNat
  have hj : j < K := by dsimp [j, t]; omega
  have hjN : j < N := hj.trans_le hKN
  have htB : t < B := ht.trans hKB
  have hjB : j < B := hj.trans hKB
  have htHeight := fold_height q M K t hq hh hσdone
  have hrHeight : Height r R := htHeight
  have hInv := height_inv r R hrHeight
  have htail := iterated_tail_height q M j hq hh
  have haM : a ≤ M := by
    dsimp only [a]
    rw [RamContinuedFractionStep.floor_toNat _ htail.1]
    exact (Nat.div_le_self _ _).trans htail.2.1
  have haR : Height (a : ℚ) R := height_nat _ _ (haM.trans hMR) hR
  have hindex : Spec B (fun υ => υ.vars "cf.limit" = K ∧ υ.vars "cf.done" = t)
      (.assign "cf.back" (.sub (.sub (.var "cf.limit") (.var "cf.done")) (.lit 1)))
      (fun _ υ => υ.vars "cf.back" = j) 6 := by
    rintro υ ⟨hυK, hυt⟩
    have hsubB : K - t < B := (Nat.sub_le _ _).trans_lt hKB
    run_vcg
    all_goals simp_all [j]
    all_goals omega
  obtain ⟨τ, hr₁, hτj⟩ := hindex σ ⟨hσK, rfl⟩
  have hτresult : FractionOutput r τ := by
    simpa only [FractionOutput, hr₁.frame_var "rat.s" (by decide),
      hr₁.frame_var "rat.n" (by decide), hr₁.frame_var "rat.d" (by decide)] using hσresult
  obtain ⟨υ, hr₂, hυleft⟩ := resultToLeft_spec B r h1
    (hrHeight.1.trans_lt hRB) (hrHeight.2.trans_lt hRB) τ hτresult
  obtain ⟨ρ, hr₃, hρresult⟩ := invert_spec B R r h1 hRB hrHeight υ hυleft
  obtain ⟨χ, hr₄, hχright⟩ := resultToRight_spec B r⁻¹ h1
    (hInv.1.trans_lt hRB) (hInv.2.trans_lt hRB) ρ hρresult
  have hrArithmetic := hr₁.seq (hr₂.seq (hr₃.seq hr₄))
  have hχlen : (χ.arrs "cf.stack").length = N := by
    rw [hrArithmetic.frame_arr "cf.stack" (by decide)]
    exact hσlen
  have hχj : χ.vars "cf.back" = j :=
    ((hr₂.seq (hr₃.seq hr₄)).frame_var _ (by decide)).trans hτj
  have hχa : (χ.arrs "cf.stack").getD j 0 = a := by
    rw [hrArithmetic.frame_arr "cf.stack" (by decide)]
    exact hσstack j hj
  obtain ⟨ψ, hr₅, hψleft⟩ := restoreFloor_spec B N j a hjN hjB h1 ((haM.trans hMR).trans_lt hRB)
    χ ⟨hχlen, hχa, hχj⟩
  have hψright : RightValue r⁻¹ ψ := by
    simpa only [RightValue, hr₅.frame_var "right.s" (by decide),
      hr₅.frame_var "right.n" (by decide), hr₅.frame_var "right.d" (by decide)] using hχright
  obtain ⟨ω, hr₆, hωresult⟩ := add_spec B R (a : ℚ) r⁻¹ hB haR hInv ψ ⟨hψleft, hψright⟩
  have hrBefore := hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq (hr₅.seq hr₆))))
  have hωt : ω.vars "cf.done" = t := hrBefore.frame_var _ (by decide)
  have hsumB : Bop.add.apply (ω.vars "cf.done") 1 < B := by simpa [hωt] using lt_of_le_of_lt ht hKB
  have hr₇ : Run B (.assign "cf.done" (.add (.var "cf.done") (.lit 1))) ω (ω.setVar "cf.done" (t + 1)) 4 :=
    Run.assign (by simpa only [hωt, Bop.apply_add] using (evalB_bin
      (evalB_var (B := B) (σ := ω) (x := "cf.done") (hωt ▸ htB)) (evalB_lit h1) hsumB))
  have hfloor : (a : ℚ) = (Int.floor (tail^[j] q) : ℚ) := by
    dsimp only [a]
    exact_mod_cast Int.toNat_of_nonneg (Int.floor_nonneg.mpr htail.1)
  have hnext : FractionOutput (ContinuedFractionFold.fold q K (t + 1)) ω := by
    simpa only [ContinuedFractionFold.fold, ← hfloor, j, r] using hωresult
  have hr := hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq (hr₅.seq (hr₆.seq hr₇)))))
  refine ⟨_, hr.mono (by dsimp only [R]; omega), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i hi
    rw [hr.frame_arr "cf.stack" (by decide)]
    exact hσstack i hi
  · rw [hr.frame_arr "cf.stack" (by decide)]
    exact hσlen
  · change t + 1 ≤ K; exact ht
  · exact (hr.frame_var _ (by decide)).trans hσK
  · simpa [FractionOutput, vars_setVar] using hnext
  · simp [t]

end Lax109476Proofs.RamContinuedFractionFoldStep

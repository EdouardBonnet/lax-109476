import Lax109476Proofs.RamPrimitiveBounds
import Lax109476Proofs.RamRationalArrays

namespace Lax109476Proofs.RamFractionInterface

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamPrimitiveBounds RamRationalArrays RamRounding RationalArithmeticBounds

def LeftValue (q : ℚ) (σ : Env) : Prop :=
  fractionValue (σ.vars "left.s") (σ.vars "left.n") (σ.vars "left.d") = q ∧
    σ.vars "left.n" = q.num.natAbs ∧ σ.vars "left.d" = q.den ∧ σ.vars "left.s" ≤ 1

def RightValue (q : ℚ) (σ : Env) : Prop :=
  fractionValue (σ.vars "right.s") (σ.vars "right.n") (σ.vars "right.d") = q ∧
    σ.vars "right.n" = q.num.natAbs ∧ σ.vars "right.d" = q.den ∧ σ.vars "right.s" ≤ 1

theorem leftValue_of_output (q : ℚ) (σ : Env) (h : LeftOutput q σ) : LeftValue q σ := by
  rcases h with ⟨hs, hn, hd⟩
  exact ⟨by rw [hs, hn, hd]; exact canonical_fractionValue q, hn, hd, hs ▸ rationalSign_le_one q⟩

theorem rightValue_of_output (q : ℚ) (σ : Env) (h : RightOutput q σ) : RightValue q σ := by
  rcases h with ⟨hs, hn, hd⟩
  exact ⟨by rw [hs, hn, hd]; exact canonical_fractionValue q, hn, hd, hs ▸ rationalSign_le_one q⟩

theorem multiply_spec (B M : ℕ) (q r : ℚ) (hB : 2 * M ^ 2 + 3 < B)
    (hq : Height q M) (hr : Height r M) :
    Spec B (fun σ => LeftValue q σ ∧ RightValue r σ) multiplyFraction
      (fun _ τ => FractionOutput (q * r) τ) (72 * M.size + 64) := by
  rintro σ ⟨⟨hqval, hqn, hqd, hqs⟩, ⟨hrval, hrn, hrd, hrs⟩⟩
  rw [hqn, hqd] at hqval
  rw [hrn, hrd] at hrval
  obtain ⟨τ, hrun, hτ⟩ := multiplyFraction_uniform_spec B M (σ.vars "left.s") q.num.natAbs q.den
    (σ.vars "right.s") r.num.natAbs r.den hB hqs hrs hq.1 hq.2 hr.1 hr.2 q.den_pos r.den_pos
    σ ⟨rfl, hqn, hqd, rfl, hrn, hrd⟩
  exact ⟨τ, hrun, by simpa only [hqval, hrval] using hτ⟩

theorem add_spec (B M : ℕ) (q r : ℚ) (hB : 2 * M ^ 2 + 3 < B)
    (hq : Height q M) (hr : Height r M) :
    Spec B (fun σ => LeftValue q σ ∧ RightValue r σ) addFraction
      (fun _ τ => FractionOutput (q + r) τ) (72 * M.size + 96) := by
  rintro σ ⟨⟨hqval, hqn, hqd, hqs⟩, ⟨hrval, hrn, hrd, hrs⟩⟩
  rw [hqn, hqd] at hqval
  rw [hrn, hrd] at hrval
  obtain ⟨τ, hrun, hτ⟩ := addFraction_uniform_spec B M (σ.vars "left.s") q.num.natAbs q.den
    (σ.vars "right.s") r.num.natAbs r.den hB hqs hrs hq.1 hq.2 hr.1 hr.2 q.den_pos r.den_pos
    σ ⟨rfl, hqn, hqd, rfl, hrn, hrd⟩
  exact ⟨τ, hrun, by simpa only [hqval, hrval] using hτ⟩

theorem round_spec (B M D : ℕ) (q : ℚ) (hB : 2 * M ^ 2 + 3 < B)
    (hq : Height q M) (hD : D ≤ M) (hDpos : 0 < D) :
    Spec B (fun σ => LeftValue q σ ∧ σ.vars "grid.D" = D) roundFraction
      (fun _ τ => FractionOutput (RationalRounding.roundDown q D) τ) (36 * M.size + 96) := by
  rintro σ ⟨⟨hqval, hqn, hqd, hqs⟩, hσD⟩
  rw [hqn, hqd] at hqval
  obtain ⟨τ, hrun, hτ⟩ := roundFraction_uniform_spec B M (σ.vars "left.s") q.num.natAbs q.den D
    hB hqs hq.1 hq.2 hD q.den_pos hDpos σ ⟨rfl, hqn, hqd, hσD⟩
  exact ⟨τ, hrun, by simpa only [hqval] using hτ⟩

def resultToLeft : Com :=
  .seq (.assign "left.s" (.var "rat.s"))
    (.seq (.assign "left.n" (.var "rat.n")) (.assign "left.d" (.var "rat.d")))

def resultToRight : Com :=
  .seq (.assign "right.s" (.var "rat.s"))
    (.seq (.assign "right.n" (.var "rat.n")) (.assign "right.d" (.var "rat.d")))

theorem resultToLeft_spec (B : ℕ) (q : ℚ) (h1 : 1 < B)
    (hn : q.num.natAbs < B) (hd : q.den < B) :
    Spec B (FractionOutput q) resultToLeft (fun _ τ => LeftValue q τ) 6 := by
  rintro σ ⟨hqval, hqn, hqd, hqs⟩
  have hsB := hqs.trans_lt h1
  run_vcg
  all_goals simp_all [LeftValue]

theorem resultToRight_spec (B : ℕ) (q : ℚ) (h1 : 1 < B)
    (hn : q.num.natAbs < B) (hd : q.den < B) :
    Spec B (FractionOutput q) resultToRight (fun _ τ => RightValue q τ) 6 := by
  rintro σ ⟨hqval, hqn, hqd, hqs⟩
  have hsB := hqs.trans_lt h1
  run_vcg
  all_goals simp_all [RightValue]

theorem invert_spec (B M : ℕ) (q : ℚ) (h1 : 1 < B) (hMB : M < B) (hq : Height q M) :
    Spec B (LeftValue q) invertFraction (fun _ τ => FractionOutput q⁻¹ τ) (36 * M.size + 40) := by
  rintro σ ⟨hqval, hqn, hqd, hqs⟩
  rw [hqn, hqd] at hqval
  obtain ⟨τ, hrun, hτ⟩ := invertFraction_spec B (σ.vars "left.s") q.num.natAbs q.den h1 hqs
    (hq.1.trans_lt hMB) (hq.2.trans_lt hMB) σ ⟨rfl, hqn, hqd⟩
  refine ⟨τ, hrun.mono ?_, ?_⟩
  · have hs := Nat.size_le_size hq.1; omega
  · simpa only [hqval] using hτ

theorem fractionValue_flip (s n d : ℕ) (hs : s ≤ 1) :
    fractionValue (1 - s) n d = -fractionValue s n d := by
  interval_cases s <;> simp [fractionValue, neg_div]

def resultToRightNegated : Com :=
  .seq (.assign "right.s" (.sub (.lit 1) (.var "rat.s")))
    (.seq (.assign "right.n" (.var "rat.n")) (.assign "right.d" (.var "rat.d")))

theorem resultToRightNegated_spec (B : ℕ) (q : ℚ) (h1 : 1 < B)
    (hn : q.num.natAbs < B) (hd : q.den < B) :
    Spec B (FractionOutput q) resultToRightNegated (fun _ τ => RightValue (-q) τ) 8 := by
  rintro σ ⟨hqval, hqn, hqd, hqs⟩
  have hsB := hqs.trans_lt h1
  have hflip := fractionValue_flip (σ.vars "rat.s") (σ.vars "rat.n") (σ.vars "rat.d") hqs
  rw [hqval] at hflip
  run_vcg
  all_goals simp_all [RightValue]

def negateRight : Com := .assign "right.s" (.sub (.lit 1) (.var "right.s"))

theorem negateRight_spec (B : ℕ) (q : ℚ) (h1 : 1 < B) :
    Spec B (RightValue q) negateRight (fun _ τ => RightValue (-q) τ) 4 := by
  rintro σ ⟨hqval, hqn, hqd, hqs⟩
  have hsB := hqs.trans_lt h1
  have hflip := fractionValue_flip (σ.vars "right.s") (σ.vars "right.n") (σ.vars "right.d") hqs
  rw [hqval] at hflip
  run_vcg
  all_goals simp_all [RightValue]

def subtractFraction : Com := .seq negateRight addFraction

theorem subtract_spec (B M : ℕ) (q r : ℚ) (hB : 2 * M ^ 2 + 3 < B)
    (hq : Height q M) (hr : Height r M) :
    Spec B (fun σ => LeftValue q σ ∧ RightValue r σ) subtractFraction
      (fun _ τ => FractionOutput (q - r) τ) (72 * M.size + 100) := by
  have h1 : 1 < B := by nlinarith
  rintro σ ⟨hσq, hσr⟩
  obtain ⟨τ, hr₁, hτr⟩ := negateRight_spec B r h1 σ hσr
  have hτq : LeftValue q τ := by
    simpa only [LeftValue, hr₁.frame_var "left.s" (by simp [negateRight, Com.wvars]),
      hr₁.frame_var "left.n" (by simp [negateRight, Com.wvars]),
      hr₁.frame_var "left.d" (by simp [negateRight, Com.wvars])] using hσq
  obtain ⟨υ, hr₂, hυ⟩ := add_spec B M q (-r) hB hq (height_neg _ _ hr) τ ⟨hτq, hτr⟩
  exact ⟨υ, (hr₁.seq hr₂).mono (by omega), by simpa only [sub_eq_add_neg] using hυ⟩

theorem compare_spec (B M : ℕ) (q r : ℚ) (hB : 2 * M ^ 2 + 3 < B)
    (hq : Height q M) (hr : Height r M) :
    Spec B (fun σ => LeftValue q σ ∧ RightValue r σ) RamComparison.compareFraction
      (fun _ τ => τ.vars "cmp.le" ≤ 1 ∧ (τ.vars "cmp.le" = 1 ↔ q ≤ r)) 40 := by
  rintro σ ⟨⟨hqval, hqn, hqd, hqs⟩, ⟨hrval, hrn, hrd, hrs⟩⟩
  rw [hqn, hqd] at hqval
  rw [hrn, hrd] at hrval
  obtain ⟨τ, hrun, hτ⟩ := RamComparison.compareFraction_spec B M (σ.vars "left.s") q.num.natAbs q.den
    (σ.vars "right.s") r.num.natAbs r.den hB hqs hrs hq.1 hq.2 hr.1 hr.2 q.den_pos r.den_pos
    σ ⟨rfl, hqn, hqd, rfl, hrn, hrd⟩
  exact ⟨τ, hrun, by simpa only [hqval, hrval] using hτ⟩

theorem upperRoot_spec (B M D : ℕ) (q : ℚ)
    (hB : (2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3 < B)
    (hq : Height q M) (hD : D ≤ M) (hDpos : 0 < D) :
    Spec B (fun σ => LeftValue q σ ∧ σ.vars "grid.D" = D) upperRootFraction
      (fun _ τ => FractionOutput (RationalRounding.sqrtUpper q D) τ) (114 * M.size + 180) := by
  rintro σ ⟨⟨hqval, hqn, hqd, hqs⟩, hσD⟩
  rw [hqn, hqd] at hqval
  obtain ⟨τ, hrun, hτ⟩ := upperRootFraction_uniform_spec B M (σ.vars "left.s") q.num.natAbs q.den D
    hB hqs hq.1 hq.2 hD q.den_pos hDpos σ ⟨rfl, hqn, hqd, hσD⟩
  exact ⟨τ, hrun, by simpa only [hqval] using hτ⟩

end Lax109476Proofs.RamFractionInterface

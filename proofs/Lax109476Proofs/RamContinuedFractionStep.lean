import Lax109476Proofs.RamFrame
import Lax109476Proofs.RamFractionInterface
import Lax109476Proofs.RationalReconstruction

namespace Lax109476Proofs.RamContinuedFractionStep

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamArithmetic RamFractionInterface RationalReconstruction

theorem nonnegative_tail (n d : ℕ) (hd : 0 < d) :
    tail (fractionValue 0 n d) = fractionValue 0 d (n % d) := by
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  have hsum : (d : ℚ) * (n / d : ℕ) + (n % d : ℕ) = n := by exact_mod_cast Nat.div_add_mod n d
  have hfrac : Int.fract ((n : ℚ) / d) = ((n % d : ℕ) : ℚ) / d := by
    simp only [Int.fract, Rat.floor_natCast_div_natCast, ← Int.natCast_ediv, Int.cast_natCast]
    field_simp
    nlinarith
  simp only [tail, fractionValue, if_neg (by decide : ¬ (0 : ℕ) = 1), hfrac, inv_div]

def quotientRemainder : Com :=
  .seq (.assign "cf.a" (.div (.var "left.n") (.var "left.d")))
    (.seq (.assign "cf.r" (.sub (.var "left.n") (.mul (.var "cf.a") (.var "left.d"))))
      (.assign "rat.s" (.lit 0)))

def finish : Com := .ite (.eq (.var "cf.r") (.lit 0))
  (.seq (.assign "rat.n" (.lit 0)) (.assign "rat.d" (.lit 1)))
  (.seq (.assign "rat.n" (.var "left.d"))
    (.seq (.assign "rat.d" (.var "cf.r")) normalizeFraction))

def step : Com := .seq quotientRemainder finish

set_option maxHeartbeats 800000 in
theorem step_spec (B M n d : ℕ) (h1 : 1 < B) (hMB : M < B)
    (hn : n ≤ M) (hd : d ≤ M) (hdpos : 0 < d) :
    Spec B (fun σ => σ.vars "left.n" = n ∧ σ.vars "left.d" = d) step
      (fun _ τ => τ.vars "cf.a" = n / d ∧ FractionOutput (tail (fractionValue 0 n d)) τ)
      (36 * M.size + 96) := by
  have hnB := hn.trans_lt hMB
  have hdB := hd.trans_lt hMB
  have hquotB : n / d < B := (Nat.div_le_self _ _).trans_lt hnB
  have hprodB : n / d * d < B := (Nat.div_mul_le_self _ _).trans_lt hnB
  have hremB : n - n / d * d < B := (Nat.sub_le _ _).trans_lt hnB
  have hmod : n - n / d * d = n % d := by simpa only [Nat.mul_comm] using (Nat.mod_def n d).symm
  have hds := Nat.size_le_size hd
  have hp : Spec B (fun σ => σ.vars "left.n" = n ∧ σ.vars "left.d" = d) quotientRemainder
      (fun _ τ => τ.vars "cf.a" = n / d ∧ τ.vars "cf.r" = n % d ∧
        τ.vars "left.d" = d ∧ τ.vars "rat.s" = 0) 12 := by
    rintro σ ⟨hσn, hσd⟩
    run_vcg
    all_goals simp_all
  intro σ hσ
  obtain ⟨τ, hr₁, hτa, hτr, hτd, hτs⟩ := hp σ hσ
  have hrB : n % d < B := (Nat.mod_lt _ hdpos).trans hdB
  have hcond := evalB_condEq
    (evalB_var (B := B) (σ := τ) (x := "cf.r") (hτr ▸ hrB)) (evalB_lit (by omega : 0 < B))
  simp only [hτr] at hcond
  by_cases hz : n % d = 0
  · have hzero : Spec B (fun υ => υ.vars "rat.s" = 0)
        (.seq (.assign "rat.n" (.lit 0)) (.assign "rat.d" (.lit 1)))
        (fun _ υ => FractionOutput 0 υ ∧ υ.vars "rat.s" = τ.vars "rat.s") 4 := by
      intro υ hυs
      run_vcg
      all_goals simp_all [FractionOutput, fractionValue]
    obtain ⟨υ, hr₂, hυ, hυs⟩ := hzero τ hτs
    have hfinal : FractionOutput 0 υ := hυ
    have hυa := (hr₂.frame_var "cf.a" (by decide)).trans hτa
    refine ⟨υ, (hr₁.seq (Run.ite_true (by simpa [hz] using hcond) hr₂)).mono (by simp only [Cond.size, Expr.size]; omega), hυa, ?_⟩
    rw [nonnegative_tail n d hdpos]
    simpa only [hz, fractionValue, if_neg (by decide : ¬ (0 : ℕ) = 1), Nat.cast_zero, div_zero] using hfinal
  · have hnorm := RamFrame.spec_with_write_frame ["cf.a"]
      (normalizeFraction_output_spec B 0 d (n % d) (by decide) hdB hrB (Nat.pos_of_ne_zero hz))
      (by intro x hx; simp at hx; subst x; decide)
    have hfinish : Spec B
        (fun υ => υ.vars "left.d" = d ∧ υ.vars "cf.r" = n % d ∧ υ.vars "rat.s" = 0)
        (.seq (.assign "rat.n" (.var "left.d"))
          (.seq (.assign "rat.d" (.var "cf.r")) normalizeFraction))
        (fun υ ρ => FractionOutput (fractionValue 0 d (n % d)) ρ ∧ ρ.vars "cf.a" = υ.vars "cf.a")
        (36 * (n % d).size + 20) := by
      rintro υ ⟨hυd, hυr, hυs⟩
      run_vcg [hnorm]
      all_goals clear hnorm
      all_goals simp_all [RamFrame.FieldsAgree]
    obtain ⟨υ, hr₂, hυ, hυa⟩ := hfinish τ ⟨hτd, hτr, hτs⟩
    have hrs := (Nat.size_le_size (Nat.mod_lt n hdpos).le).trans hds
    refine ⟨υ, (hr₁.seq (Run.ite_false (by simpa [hz] using hcond) hr₂)).mono (by simp only [Cond.size, Expr.size]; omega), hυa.trans hτa, ?_⟩
    rw [nonnegative_tail n d hdpos]
    exact hυ

theorem nonnegative_representation (q : ℚ) (hq : 0 ≤ q) :
    fractionValue 0 q.num.natAbs q.den = q := by
  have hn : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  have hs : RamRationalArrays.rationalSign q = 0 := by
    simp [RamRationalArrays.rationalSign, not_lt.mpr hn]
  simpa only [hs] using RamRationalArrays.canonical_fractionValue q

theorem floor_toNat (q : ℚ) (hq : 0 ≤ q) :
    (Int.floor q).toNat = q.num.natAbs / q.den := by
  conv_lhs =>
    rw [← nonnegative_representation q hq]
    simp only [fractionValue, if_neg (by decide : ¬ (0 : ℕ) = 1),
      Rat.floor_natCast_div_natCast, ← Int.natCast_ediv, Int.toNat_natCast]

theorem step_nonnegative_spec (B M : ℕ) (q : ℚ) (hq : 0 ≤ q)
    (h1 : 1 < B) (hMB : M < B) (hh : RationalArithmeticBounds.Height q M) :
    Spec B (LeftValue q) step
      (fun _ τ => τ.vars "cf.a" = (Int.floor q).toNat ∧ FractionOutput (tail q) τ)
      (36 * M.size + 96) := by
  refine (step_spec B M q.num.natAbs q.den h1 hMB hh.1 hh.2 q.den_pos).pre
    (fun _ h => ⟨h.2.1, h.2.2.1⟩) |>.post ?_
  intro σ τ _ hτ
  simpa only [nonnegative_representation q hq, floor_toNat q hq] using hτ

end Lax109476Proofs.RamContinuedFractionStep

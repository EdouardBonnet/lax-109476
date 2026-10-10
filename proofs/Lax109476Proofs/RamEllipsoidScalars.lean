import Lax109476Proofs.RamEllipsoidForm
import Lax109476Proofs.EllipsoidArithmeticBounds
import Lax109476Proofs.RamPrimitiveBounds
import Lax109476Proofs.EllipsoidIteration

namespace Lax109476Proofs.RamEllipsoidScalars

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamArithmetic RamEllipsoidForm RationalSizeBounds RationalArithmeticBounds
open RamRounding RamPrimitiveBounds RamFrame

def alphaFraction : Com :=
  .seq (.assign "rat.s" (.lit 0))
    (.seq (.assign "rat.n" (.mul (.var "vec.n") (.var "vec.n")))
      (.seq (.assign "rat.d" (.sub (.var "rat.n") (.lit 1))) normalizeFraction))

theorem alphaFraction_spec (B n : ℕ) (hn : 2 ≤ n) (hnB : n ^ 2 < B) :
    Spec B (fun σ => σ.vars "vec.n" = n) alphaFraction
      (fun _ τ => FractionOutput ((n : ℚ) ^ 2 / ((n : ℚ) ^ 2 - 1)) τ)
      (36 * (n ^ 2 - 1).size + 26) := by
  have hnn : n < B := by nlinarith
  have h1 : 1 < B := by nlinarith
  have hd : n ^ 2 - 1 < B := (Nat.sub_le _ _).trans_lt hnB
  have hdpos : 0 < n ^ 2 - 1 := by
    have hsq : 1 < n ^ 2 := by nlinarith
    omega
  have hone : 1 ≤ n ^ 2 := by nlinarith
  have hnorm := normalizeFraction_output_spec B 0 (n ^ 2) (n ^ 2 - 1) (by omega) hnB hd hdpos
  have hval : fractionValue 0 (n ^ 2) (n ^ 2 - 1) = (n : ℚ) ^ 2 / ((n : ℚ) ^ 2 - 1) := by
    simp [fractionValue, Nat.cast_sub hone]
  intro σ hσ
  run_vcg [hnorm]
  all_goals clear hnorm
  all_goals simp_all [pow_two]

theorem alphaFraction_cost (n : ℕ) :
    36 * (n ^ 2 - 1).size + 26 ≤ 72 * n.size + 62 := by
  have hd := Nat.size_le_size (Nat.sub_le (n ^ 2) 1)
  have hp := size_pow_le n 2
  omega

def epsilonDenominator : Com :=
  .assign "ell.epsden" (.shiftl (.lit 1) (.add (.mul (.lit 2) (.var "vec.n")) (.lit 4)))

theorem epsilonDenominator_spec (B n : ℕ) (hB : 2 ^ (2 * n + 4) < B) :
    Spec B (fun σ => σ.vars "vec.n" = n) epsilonDenominator
      (fun _ τ => τ.vars "ell.epsden" = 2 ^ (2 * n + 4)) 8 := by
  have hexp := Nat.lt_two_pow_self (n := 2 * n + 4)
  have hn : n < B := by omega
  have htwo : 2 < B := by omega
  have hfour : 4 < B := by omega
  have h1 : 1 < B := by omega
  intro σ hσ
  run_vcg
  all_goals simp_all

def inflationFraction : Com :=
  .seq (.assign "infl.a" (.add (.var "ell.epsden") (.lit 1)))
    (.seq (.assign "rat.s" (.lit 0))
      (.seq (.assign "rat.n" (.mul (.var "infl.a") (.var "infl.a")))
        (.seq (.assign "rat.d" (.mul (.var "ell.epsden") (.var "ell.epsden"))) normalizeFraction)))

theorem inflationFraction_spec (B E : ℕ) (hE : 0 < E) (hB : (E + 1) ^ 2 < B) :
    Spec B (fun σ => σ.vars "ell.epsden" = E) inflationFraction
      (fun _ τ => FractionOutput ((1 + 1 / (E : ℚ)) ^ 2) τ)
      (36 * (E ^ 2).size + 30) := by
  have hEB : E < B := by nlinarith
  have hEaB : E + 1 < B := by nlinarith
  have h1 : 1 < B := by nlinarith
  have hdB : E ^ 2 < B := by nlinarith
  have hnorm := normalizeFraction_output_spec B 0 ((E + 1) ^ 2) (E ^ 2)
    (by omega) hB hdB (by positivity)
  have hval : fractionValue 0 ((E + 1) ^ 2) (E ^ 2) = (1 + 1 / (E : ℚ)) ^ 2 := by
    have hEq : (E : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hE
    simp only [fractionValue, show (0 : ℕ) ≠ 1 by decide, ite_false, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    field_simp
  intro σ hσ
  run_vcg [hnorm]
  all_goals clear hnorm
  all_goals simp_all [pow_two]

theorem inflationFraction_cost (E : ℕ) :
    36 * (E ^ 2).size + 30 ≤ 72 * E.size + 66 := by
  have hp := size_pow_le E 2
  omega

def precisionGrid : Com :=
  .assign "grid.D" (.shiftl (.lit 1)
    (.add (.add (.mul (.lit 2) (.var "iter.k")) (.mul (.lit 3) (.var "vec.n"))) (.lit 9)))

theorem precisionGrid_value (k n : ℕ) :
    EllipsoidPrecision.gridDenominator (2 * k + 2) (2 * n + 4) n = 2 ^ (2 * k + 3 * n + 9) := by
  unfold EllipsoidPrecision.gridDenominator
  congr 1
  omega

theorem precisionGrid_spec (B k n : ℕ) (hB : 2 ^ (2 * k + 3 * n + 9) < B) :
    Spec B (fun σ => σ.vars "iter.k" = k ∧ σ.vars "vec.n" = n) precisionGrid
      (fun _ τ => τ.vars "grid.D" =
        EllipsoidPrecision.gridDenominator (2 * k + 2) (2 * n + 4) n) 12 := by
  have hexp := Nat.lt_two_pow_self (n := 2 * k + 3 * n + 9)
  have hn : n < B := by omega
  have hk : k < B := by omega
  have htwo : 2 < B := by omega
  have hthree : 3 < B := by omega
  have hnine : 9 < B := by omega
  have h1 : 1 < B := by omega
  have hval := precisionGrid_value k n
  rintro σ ⟨hσk, hσn⟩
  run_vcg
  all_goals simp_all

theorem positive_num_ratio (q : ℚ) (hq : 0 < q) : (q.num.natAbs : ℚ) / q.den = q := by
  have hnum : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg (Rat.num_pos.mpr hq).le
  have hcast : (q.num.natAbs : ℚ) = (q.num : ℚ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) hnum
  rw [hcast, q.num_div_den]

def betaFraction : Com :=
  .seq (.assign "rat.s" (.lit 0))
    (.seq (.assign "rat.n" (.mul (.lit 2) (.var "ell.form.d")))
      (.seq (.assign "beta.nplus" (.add (.var "vec.n") (.lit 1)))
        (.seq (.assign "rat.d" (.mul (.var "beta.nplus") (.var "ell.form.n"))) normalizeFraction)))

theorem betaFraction_spec (B n M : ℕ) (q : ℚ) (hqpos : 0 < q) (hq : Height q M)
    (hn : n ≤ M) (hB : 2 * M ^ 2 + 3 < B) :
    Spec B (fun σ => FormOutput q σ ∧ σ.vars "vec.n" = n) betaFraction
      (fun _ τ => FractionOutput (2 / (((n : ℚ) + 1) * q)) τ)
      (36 * ((n + 1) * q.num.natAbs).size + 30) := by
  have hM : 1 ≤ M := le_trans q.den_pos hq.2
  have hMB : M < B := by nlinarith
  have hnB := hn.trans_lt hMB
  have h1 : 1 < B := by nlinarith
  have h2 : 2 < B := by nlinarith
  have hqnB := hq.1.trans_lt hMB
  have hqdB := hq.2.trans_lt hMB
  have hnpB : n + 1 < B := by nlinarith
  have hqnumpos : 0 < q.num.natAbs := Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hqpos))
  have hbetaN : 2 * q.den < B := by nlinarith [hq.2]
  have hmul := Nat.mul_le_mul (by omega : n + 1 ≤ M + 1) hq.1
  have hbetaD : (n + 1) * q.num.natAbs < B := by nlinarith
  have hnorm := normalizeFraction_output_spec B 0 (2 * q.den) ((n + 1) * q.num.natAbs)
    (by omega) hbetaN hbetaD (Nat.mul_pos (by omega) hqnumpos)
  have hval : fractionValue 0 (2 * q.den) ((n + 1) * q.num.natAbs) =
      2 / (((n : ℚ) + 1) * q) := by
    conv_rhs => rw [← positive_num_ratio q hqpos]
    simp only [fractionValue, show (0 : ℕ) ≠ 1 by decide, ite_false, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    field_simp
  rintro σ ⟨hσq, hσn⟩
  have hnum := hσq.2.1
  have hden := hσq.2.2.1
  run_vcg [hnorm]
  all_goals clear hnorm
  all_goals simp_all

theorem betaFraction_cost (n M : ℕ) (q : ℚ) (hn : n ≤ M) (hq : Height q M) :
    36 * ((n + 1) * q.num.natAbs).size + 30 ≤ 72 * M.size + 66 := by
  have hm := size_mul_le (n + 1) q.num.natAbs
  have hp := size_add_one_le n
  have hnsize := Nat.size_le_size hn
  have hqsize := Nat.size_le_size hq.1
  omega

def scaledInverseFraction : Com :=
  .seq (.assign "gamma.rootn" (.var "rat.n"))
    (.seq (.assign "gamma.nplus" (.add (.var "vec.n") (.lit 1)))
      (.seq (.assign "rat.n" (.var "rat.d"))
        (.seq (.assign "rat.d" (.mul (.var "gamma.nplus") (.var "gamma.rootn")))
          (.seq (.assign "rat.s" (.lit 0)) normalizeFraction))))

theorem scaledInverseFraction_spec (B n M : ℕ) (q : ℚ) (hqpos : 0 < q) (hq : Height q M)
    (hn : n ≤ M) (hB : 2 * M ^ 2 + 3 < B) :
    Spec B (fun σ => FractionOutput q σ ∧ σ.vars "vec.n" = n) scaledInverseFraction
      (fun _ τ => FractionOutput (1 / (((n : ℚ) + 1) * q)) τ)
      (36 * ((n + 1) * q.num.natAbs).size + 30) := by
  have hM : 1 ≤ M := le_trans q.den_pos hq.2
  have hMB : M < B := by nlinarith
  have hnB := hn.trans_lt hMB
  have h1 : 1 < B := by nlinarith
  have hqnB := hq.1.trans_lt hMB
  have hqdB := hq.2.trans_lt hMB
  have hnpB : n + 1 < B := by nlinarith
  have hqnumpos : 0 < q.num.natAbs := Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hqpos))
  have hmul := Nat.mul_le_mul (by omega : n + 1 ≤ M + 1) hq.1
  have hgammaD : (n + 1) * q.num.natAbs < B := by nlinarith
  have hnorm := normalizeFraction_output_spec B 0 q.den ((n + 1) * q.num.natAbs)
    (by omega) hqdB hgammaD (Nat.mul_pos (by omega) hqnumpos)
  have hval : fractionValue 0 q.den ((n + 1) * q.num.natAbs) =
      1 / (((n : ℚ) + 1) * q) := by
    conv_rhs => rw [← positive_num_ratio q hqpos]
    simp only [fractionValue, show (0 : ℕ) ≠ 1 by decide, ite_false, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    field_simp
  rintro σ ⟨hσq, hσn⟩
  have hnum := hσq.2.1
  have hden := hσq.2.2.1
  run_vcg [hnorm]
  all_goals clear hnorm
  all_goals simp_all

theorem scaledInverseFraction_uniform_spec (B n M : ℕ) (q : ℚ)
    (hqpos : 0 < q) (hq : Height q M) (hn : n ≤ M) (hB : 2 * M ^ 2 + 3 < B) :
    Spec B (fun σ => FractionOutput q σ ∧ σ.vars "vec.n" = n) scaledInverseFraction
      (fun _ τ => FractionOutput (1 / (((n : ℚ) + 1) * q)) τ) (72 * M.size + 66) :=
  (scaledInverseFraction_spec B n M q hqpos hq hn hB).mono (betaFraction_cost n M q hn hq)

theorem sqrtUpper_pos (q : ℚ) (D : ℕ) (hD : 0 < D) : 0 < RationalRounding.sqrtUpper q D := by
  unfold RationalRounding.sqrtUpper
  positivity

def gammaFraction : Com :=
  .seq (.assign "left.s" (.var "ell.form.s"))
    (.seq (.assign "left.n" (.var "ell.form.n"))
      (.seq (.assign "left.d" (.var "ell.form.d"))
        (.seq upperRootFraction scaledInverseFraction)))

set_option maxHeartbeats 800000 in
theorem gammaFraction_spec (B n M D : ℕ) (q : ℚ) (hq : Height q M)
    (hn : n ≤ M) (hD : D ≤ M) (hDpos : 0 < D)
    (hB : (2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3 < B) :
    Spec B (fun σ => FormOutput q σ ∧ σ.vars "vec.n" = n ∧ σ.vars "grid.D" = D)
      gammaFraction
      (fun _ τ => FractionOutput (1 / (((n : ℚ) + 1) * RationalRounding.sqrtUpper q D)) τ)
      (6 + (114 * M.size + 180 + (72 * (M ^ 3 + 1).size + 66))) := by
  have hM : 1 ≤ M := le_trans q.den_pos hq.2
  have hMpow : M ≤ M ^ 3 + 1 := by
    have hp := le_self_pow hM (by decide : (3 : ℕ) ≠ 0)
    omega
  have hMB : M < B := by nlinarith
  have h1 : 1 < B := by nlinarith
  have hqnB := hq.1.trans_lt hMB
  have hqdB := hq.2.trans_lt hMB
  have hnM := hn.trans hMpow
  have hB₂ : 2 * (M ^ 3 + 1) ^ 2 + 3 < B := by nlinarith
  have hsqrt : Height (RationalRounding.sqrtUpper q D) (M ^ 3 + 1) := by
    have ht := EllipsoidArithmeticBounds.height_sqrtUpper q M D hq hDpos
    have hm := Nat.mul_le_mul_left M (Nat.pow_le_pow_left hD 2)
    exact height_mono _ ht (by nlinarith)
  have hinv := scaledInverseFraction_uniform_spec B n (M ^ 3 + 1)
    (RationalRounding.sqrtUpper q D) (sqrtUpper_pos q D hDpos) hsqrt hnM hB₂
  rintro σ ⟨hσq, hσn, hσD⟩
  have hqval := hσq.1
  have hqnum := hσq.2.1
  have hqden := hσq.2.2.1
  have hqs := hσq.2.2.2.trans_lt h1
  have hroot := upperRootFraction_uniform_spec B M (σ.vars "ell.form.s") q.num.natAbs q.den D
    hB hσq.2.2.2 hq.1 hq.2 hD q.den_pos hDpos
  have hframe := spec_with_fields ["vec.n"] hroot
    (by
      intro x hx
      simp at hx
      subst x
      simp [upperRootFraction, RamSquareRoot.squareRoot, RamSquareRoot.sqrtLoop,
        RamSquareRoot.sqrtStep, normalizeFraction, gcdLoop, gcdDoubleStep, gcdStep, Com.wvars])
    (by simp [upperRootFraction, RamSquareRoot.squareRoot, RamSquareRoot.sqrtLoop,
        RamSquareRoot.sqrtStep, normalizeFraction, gcdLoop, gcdDoubleStep, gcdStep, Com.warrs])
  clear hroot
  run_vcg [hframe, hinv]
  all_goals clear hframe hinv
  all_goals simp_all [FormOutput, FractionOutput, FieldsAgree]
  all_goals aesop

theorem gammaFraction_cost (M : ℕ) :
    6 + (114 * M.size + 180 + (72 * (M ^ 3 + 1).size + 66)) ≤ 330 * M.size + 396 := by
  have hp := size_pow_le M 3
  have ha := size_add_one_le (M ^ 3)
  omega

def diagonalFraction : Com :=
  .seq (.assign "rat.s" (.lit 0))
    (.seq (.assign "rat.n" (.var "vec.n")) (.seq (.assign "rat.d" (.var "grid.D")) normalizeFraction))

theorem diagonalFraction_spec (B n D : ℕ) (hn : n < B) (hD : D < B) (hDpos : 0 < D) :
    Spec B (fun σ => σ.vars "vec.n" = n ∧ σ.vars "grid.D" = D) diagonalFraction
      (fun _ τ => FractionOutput ((n : ℚ) / D) τ) (36 * D.size + 22) := by
  have hnorm := normalizeFraction_output_spec B 0 n D (by omega) hn hD hDpos
  have h0 : 0 < B := hDpos.trans hD
  have hval : fractionValue 0 n D = (n : ℚ) / D := by simp [fractionValue]
  rintro σ ⟨hσn, hσD⟩
  run_vcg [hnorm]
  all_goals clear hnorm
  all_goals simp_all

end Lax109476Proofs.RamEllipsoidScalars

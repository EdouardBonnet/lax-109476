import Lax109476Proofs.RamRational
import Lax109476Proofs.RamSquareRoot
import Lax109476Proofs.RationalRounding

namespace Lax109476Proofs.RamRounding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamArithmetic RationalRounding

def ceilQuotient (n d : ℕ) : ℕ := n / d + if n % d = 0 then 0 else 1

theorem ceilQuotient_int (n d : ℕ) (hd : 0 < d) :
    Int.ceil ((n : ℚ) / d) = (ceilQuotient n d : ℤ) := by
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hrem : ((n % d : ℕ) : ℚ) < d := by exact_mod_cast Nat.mod_lt n hd
  have heq : (d : ℚ) * (n / d : ℕ) + (n % d : ℕ) = n := by
    exact_mod_cast Nat.div_add_mod n d
  apply Int.ceil_eq_iff.mpr
  rw [lt_div_iff₀ hdq, div_le_iff₀ hdq]
  by_cases hz : n % d = 0
  · rw [hz, Nat.cast_zero, add_zero] at heq
    simp only [ceilQuotient, if_pos hz, add_zero, Int.cast_natCast]
    constructor <;> nlinarith
  · have hrpos : (0 : ℚ) < ((n % d : ℕ) : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hz
    simp only [ceilQuotient, if_neg hz, Int.cast_add, Int.cast_natCast, Int.cast_one,
      Nat.cast_add, Nat.cast_one]
    constructor <;> nlinarith

theorem ceilQuotient_nat (n d : ℕ) (hd : 0 < d) :
    Nat.ceil ((n : ℚ) / d) = ceilQuotient n d := by
  apply Int.ofNat_inj.mp
  rw [Int.natCast_ceil_eq_ceil (by positivity), ceilQuotient_int n d hd]

def roundMagnitude (s n d D : ℕ) : ℕ :=
  if s = 1 then ceilQuotient (n * D) d else (n * D) / d

theorem roundMagnitude_correct (s n d D : ℕ) (hd : 0 < d) :
    fractionValue s (roundMagnitude s n d D) D = roundDown (fractionValue s n d) D := by
  have hpos : (n : ℚ) / d * D = ((n * D : ℕ) : ℚ) / d := by push_cast; ring
  have hneg : -(n : ℚ) / d * D = -(((n * D : ℕ) : ℚ) / d) := by push_cast; ring
  unfold fractionValue roundMagnitude roundDown
  by_cases hs : s = 1
  · simp only [if_pos hs, hneg, Int.floor_neg, ceilQuotient_int (n * D) d hd,
      Int.cast_neg, Int.cast_natCast]
  · simp only [if_neg hs, hpos, Rat.floor_natCast_div_natCast]
    rw [← Int.natCast_ediv, Int.cast_natCast]

def roundFraction : Com :=
  .seq (.assign "round.a" (.mul (.var "left.n") (.var "grid.D")))
    (.seq (.assign "round.q" (.div (.var "round.a") (.var "left.d")))
      (.seq (.assign "round.r" (.sub (.var "round.a")
        (.mul (.var "round.q") (.var "left.d"))))
        (.seq (.assign "rat.n" (.var "round.q"))
          (.seq (.ite (.eq (.var "left.s") (.lit 1))
            (.ite (.eq (.var "round.r") (.lit 0)) .skip
              (.assign "rat.n" (.add (.var "rat.n") (.lit 1)))) .skip)
            (.seq (.assign "rat.s" (.var "left.s"))
              (.seq (.assign "rat.d" (.var "grid.D")) normalizeFraction))))))

set_option maxHeartbeats 800000 in
theorem roundFraction_spec (B M s n d D : ℕ) (hB : 2 * M ^ 2 + 3 < B)
    (hs : s ≤ 1) (hn : n ≤ M) (hd : d ≤ M) (hD : D ≤ M)
    (hdpos : 0 < d) (hDpos : 0 < D) :
    Spec B (fun σ => σ.vars "left.s" = s ∧ σ.vars "left.n" = n ∧
      σ.vars "left.d" = d ∧ σ.vars "grid.D" = D) roundFraction
      (fun _ σ' => FractionOutput (roundDown (fractionValue s n d) D) σ')
      (36 * D.size + 96) := by
  have hM : M < B := by nlinarith
  have hnB := hn.trans_lt hM
  have hdB := hd.trans_lt hM
  have hDB := hD.trans_lt hM
  have ha : n * D ≤ M * M := Nat.mul_le_mul hn hD
  have haB : n * D < B := ha.trans_lt (by nlinarith)
  have hqB : n * D / d < B := (Nat.div_le_self _ _).trans_lt haB
  have hqdB : n * D / d * d < B := (Nat.div_mul_le_self _ _).trans_lt haB
  have hrB : n * D - n * D / d * d < B := (Nat.sub_le _ _).trans_lt haB
  have hq1B : n * D / d + 1 < B := by have hq := Nat.div_le_self (n * D) d; nlinarith
  have h1 : 1 < B := by nlinarith
  have hsB := hs.trans_lt h1
  have hmB : roundMagnitude s n d D < B := by
    unfold roundMagnitude ceilQuotient
    split_ifs <;> omega
  have hnorm := normalizeFraction_output_spec B s (roundMagnitude s n d D) D
    hs hmB hDB hDpos
  have hc := roundMagnitude_correct s n d D hdpos
  have hmod : n * D - n * D / d * d = n * D % d := by
    simpa only [Nat.mul_comm] using (Nat.mod_def (n * D) d).symm
  rintro σ ⟨hσs, hσn, hσd, hσD⟩
  run_vcg [hnorm]
  all_goals simp_all [roundMagnitude, ceilQuotient]

def upperMagnitude (s n d D : ℕ) : ℕ :=
  if s = 1 then 0 else ceilQuotient (n * D ^ 2) d

theorem upperMagnitude_correct (s n d D : ℕ) (hd : 0 < d) :
    upperMagnitude s n d D = Nat.ceil (fractionValue s n d * (D : ℚ) ^ 2) := by
  by_cases hs : s = 1
  · have hq : fractionValue s n d * (D : ℚ) ^ 2 ≤ 0 := by
      simp only [fractionValue, if_pos hs, neg_div]
      have hp : (0 : ℚ) ≤ (n : ℚ) / d * (D : ℚ) ^ 2 := by positivity
      nlinarith
    rw [upperMagnitude, if_pos hs]
    exact (Nat.ceil_eq_zero.mpr hq).symm
  · have he : fractionValue s n d * (D : ℚ) ^ 2 = ((n * D ^ 2 : ℕ) : ℚ) / d := by
      simp only [fractionValue, if_neg hs, Nat.cast_mul, Nat.cast_pow]
      ring
    rw [he, ceilQuotient_nat _ _ hd]
    simp [upperMagnitude, hs]

theorem squareRoot_grid_spec (B N D : ℕ) (hB : (2 * (N + 1) + 1) ^ 2 < B) :
    Spec B (fun σ => σ.vars "sqrt.n" = N ∧ σ.vars "grid.D" = D) RamSquareRoot.squareRoot
      (fun _ τ => τ.vars "sqrt.lo" = Nat.sqrt N ∧ τ.vars "grid.D" = D)
      (26 * N.size + 12) := by
  rintro σ ⟨hσn, hσD⟩
  obtain ⟨τ, hr, hτ⟩ := RamSquareRoot.squareRoot_spec B N hB σ hσn
  exact ⟨τ, hr, hτ, (hr.frame_var "grid.D" (by decide)).trans hσD⟩

def upperRootFraction : Com :=
  .seq (.assign "round.a" (.mul (.mul (.var "left.n") (.var "grid.D")) (.var "grid.D")))
    (.seq (.assign "round.q" (.div (.var "round.a") (.var "left.d")))
      (.seq (.assign "round.r" (.sub (.var "round.a")
        (.mul (.var "round.q") (.var "left.d"))))
        (.seq (.assign "sqrt.n" (.var "round.q"))
          (.seq (.ite (.eq (.var "round.r") (.lit 0)) .skip
            (.assign "sqrt.n" (.add (.var "sqrt.n") (.lit 1))))
            (.seq (.ite (.eq (.var "left.s") (.lit 1)) (.assign "sqrt.n" (.lit 0)) .skip)
              (.seq RamSquareRoot.squareRoot
                (.seq (.assign "rat.n" (.add (.var "sqrt.lo") (.lit 1)))
                  (.seq (.assign "rat.s" (.lit 0))
                    (.seq (.assign "rat.d" (.var "grid.D")) normalizeFraction)))))))))

set_option maxHeartbeats 1000000 in
theorem upperRootFraction_spec (B M s n d D : ℕ)
    (hB : (2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3 < B)
    (hs : s ≤ 1) (hn : n ≤ M) (hd : d ≤ M) (hD : D ≤ M)
    (hdpos : 0 < d) (hDpos : 0 < D) :
    Spec B (fun σ => σ.vars "left.s" = s ∧ σ.vars "left.n" = n ∧
      σ.vars "left.d" = d ∧ σ.vars "grid.D" = D) upperRootFraction
      (fun _ σ' => FractionOutput (sqrtUpper (fractionValue s n d) D) σ')
      (26 * (upperMagnitude s n d D).size + 36 * D.size + 128) := by
  have hMpos : 1 ≤ M := hDpos.trans_le hD
  have hMpow : M ≤ M ^ 3 := le_self_pow hMpos (by decide)
  have hM : M < B := by nlinarith
  have hnB := hn.trans_lt hM
  have hdB := hd.trans_lt hM
  have hDB := hD.trans_lt hM
  have ha : n * D * D ≤ M ^ 3 := by
    simpa only [pow_succ, pow_zero, one_mul] using Nat.mul_le_mul (Nat.mul_le_mul hn hD) hD
  have haB : n * D * D < B := ha.trans_lt (by nlinarith)
  have hpartial : n * D < B := (Nat.le_mul_of_pos_right _ hDpos).trans_lt haB
  have hqB : n * D * D / d < B := (Nat.div_le_self _ _).trans_lt haB
  have hqdB : n * D * D / d * d < B := (Nat.div_mul_le_self _ _).trans_lt haB
  have hrB : n * D * D - n * D * D / d * d < B := (Nat.sub_le _ _).trans_lt haB
  have hq1B : n * D * D / d + 1 < B := by
    have hq := Nat.div_le_self (n * D * D) d
    nlinarith
  have h1 : 1 < B := by nlinarith
  have hsB := hs.trans_lt h1
  have hN : upperMagnitude s n d D ≤ M ^ 3 + 1 := by
    have hq := Nat.div_le_self (n * D ^ 2) d
    have ha' : n * D ^ 2 ≤ M ^ 3 := by simpa only [pow_two, Nat.mul_assoc] using ha
    unfold upperMagnitude ceilQuotient
    split_ifs <;> omega
  have hrootB : (2 * (upperMagnitude s n d D + 1) + 1) ^ 2 < B := by
    have hp := Nat.pow_le_pow_left (by omega :
      2 * (upperMagnitude s n d D + 1) + 1 ≤ 2 * (M ^ 3 + 2) + 1) 2
    omega
  have hnumB : Nat.sqrt (upperMagnitude s n d D) + 1 < B := by
    have hr := Nat.sqrt_le_self (upperMagnitude s n d D)
    nlinarith
  have hroot := squareRoot_grid_spec B (upperMagnitude s n d D) D hrootB
  have hnorm := normalizeFraction_output_spec B 0
    (Nat.sqrt (upperMagnitude s n d D) + 1) D (by omega) hnumB hDB hDpos
  have hc : fractionValue 0 (Nat.sqrt (upperMagnitude s n d D) + 1) D =
      sqrtUpper (fractionValue s n d) D := by
    simp only [fractionValue, if_neg (by decide : ¬ (0 : ℕ) = 1), sqrtUpper,
      upperMagnitude_correct s n d D hdpos]
  have hmod : n * D * D - n * D * D / d * d = n * D * D % d := by
    simpa only [Nat.mul_comm] using (Nat.mod_def (n * D * D) d).symm
  rintro σ ⟨hσs, hσn, hσd, hσD⟩
  run_vcg [hroot, hnorm]
  all_goals simp_all [upperMagnitude, ceilQuotient, pow_two, Nat.mul_assoc]

end Lax109476Proofs.RamRounding

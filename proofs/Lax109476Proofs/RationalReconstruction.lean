import Lax109476Proofs.RationalSizeBounds
import Mathlib.NumberTheory.DiophantineApproximation.Basic

namespace Lax109476Proofs.RationalReconstruction

/-- Distinct reduced rationals with denominator at most B are separated by
at least `1/B²`. No numerator or magnitude bound is required. -/
theorem rational_gap (q r : ℚ) (B : ℕ) (hq : q.den ≤ B) (hr : r.den ≤ B)
    (hne : q ≠ r) : (1 : ℚ) / (B : ℚ) ^ 2 ≤ |q - r| := by
  let a : ℤ := q.num * r.den - r.num * q.den
  have hD : (0 : ℚ) < (q.den : ℚ) * r.den := by positivity
  have hqd : (q.den : ℚ) ≠ 0 := by positivity
  have hrd : (r.den : ℚ) ≠ 0 := by positivity
  have hid : q - r = (a : ℚ) / ((q.den : ℚ) * r.den) := by
    conv_lhs => rw [← q.num_div_den, ← r.num_div_den]
    simp only [a, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    field_simp
  have ha : a ≠ 0 := by
    intro h
    rw [h, Int.cast_zero, zero_div] at hid
    exact hne (sub_eq_zero.mp hid)
  have habs : (1 : ℚ) ≤ |(a : ℚ)| := by
    have hn : (1 : ℕ) ≤ a.natAbs := Int.natAbs_pos.mpr ha
    have h : (1 : ℚ) ≤ (a.natAbs : ℚ) := by exact_mod_cast hn
    simpa only [Nat.cast_natAbs, Int.cast_abs] using h
  have hB : (0 : ℚ) < B := by
    have h : 0 < B := lt_of_lt_of_le q.den_pos hq
    exact_mod_cast h
  have hDb : (q.den : ℚ) * r.den ≤ (B : ℚ) ^ 2 := by
    have h₁ : (q.den : ℚ) ≤ B := by exact_mod_cast hq
    have h₂ : (r.den : ℚ) ≤ B := by exact_mod_cast hr
    simpa only [pow_two] using mul_le_mul h₁ h₂ (by positivity) hB.le
  rw [hid, abs_div, abs_of_pos hD]
  calc
    _ ≤ 1 / ((q.den : ℚ) * r.den) := one_div_le_one_div_of_le hD hDb
    _ ≤ _ := (div_le_div_iff_of_pos_right hD).mpr habs

theorem unique_in_interval (l u q r : ℚ) (B : ℕ)
    (hq : q.den ≤ B) (hr : r.den ≤ B) (hql : l ≤ q) (hqu : q ≤ u)
    (hrl : l ≤ r) (hru : r ≤ u) (hwidth : u - l < (1 : ℚ) / (B : ℚ) ^ 2) :
    q = r := by
  by_contra hne
  have hgap := rational_gap q r B hq hr hne
  have hdist : |q - r| ≤ u - l := by apply abs_le.mpr; constructor <;> linarith
  linarith

/-- Computable continued-fraction convergents of a rational approximation. -/
def convergent : ℚ → ℕ → ℚ
  | a, 0 => Int.floor a
  | a, k + 1 => Int.floor a + (convergent (Int.fract a)⁻¹ k)⁻¹

theorem convergent_eq_real (a : ℚ) (k : ℕ) : convergent a k = Real.convergent (a : ℝ) k := by
  induction k generalizing a with
  | zero => simp [convergent, Real.convergent_zero]
  | succ k ih =>
    simp only [convergent, Real.convergent_succ, Rat.floor_cast]
    rw [ih]
    congr 2
    simp

/-- Legendre's theorem guarantees that a sufficiently accurate approximation
contains the target rational among its computable convergents. -/
theorem exists_target_convergent (a q : ℚ)
    (h : |(a : ℝ) - (q : ℝ)| < 1 / (2 * (q.den : ℝ) ^ 2)) :
    ∃ k, convergent a k = q := by
  obtain ⟨k, hk⟩ := Real.exists_rat_eq_convergent h
  exact ⟨k, (convergent_eq_real a k).trans hk.symm⟩

theorem fract_numerator (q : ℚ) : (Int.fract q).num = q.num % q.den := by
  have hd : (q.den : ℚ) ≠ 0 := by positivity
  have hrep := (Int.fract q).num_div_den
  rw [Rat.den_intFract] at hrep
  have hnum : ((Int.fract q).num : ℚ) =
      (q.num : ℚ) - (Int.floor q : ℚ) * q.den := by
    calc
      _ = Int.fract q * q.den := (div_eq_iff hd).mp hrep
      _ = q * q.den - (Int.floor q : ℚ) * q.den := by rw [Int.fract, sub_mul]
      _ = _ := by rw [← Rat.mul_den_eq_num]
  have hnum' : (Int.fract q).num = q.num - Int.floor q * q.den := by exact_mod_cast hnum
  rw [hnum', Rat.floor_def', Int.emod_def]
  ring

def tail (q : ℚ) : ℚ := (Int.fract q)⁻¹

/-- A denominator-one value terminates the continued-fraction recursion. -/
theorem tail_eq_zero_of_den_one (q : ℚ) (hq : q.den = 1) : tail q = 0 := by
  have hfract : Int.fract q = 0 := by
    have hn : (Int.fract q).num = 0 := by rw [fract_numerator, hq]; simp
    exact Rat.num_eq_zero.mp hn
  simp [tail, hfract]

private theorem remainder_half (d r : ℕ) (hr : 0 < r) (hrd : r < d) : d % r ≤ d / 2 := by
  by_cases h : r ≤ d / 2
  · exact (Nat.mod_lt d hr).le.trans h
  · rw [Nat.mod_eq_sub_mod hrd.le, Nat.mod_eq_of_lt (by omega)]
    omega

/-- Two continued-fraction steps halve the denominator unless it has already
reached one. This supplies a logarithmic termination bound. -/
theorem tail_tail_den_half (q : ℚ) (hq : 1 < q.den) : (tail (tail q)).den ≤ q.den / 2 := by
  have hf : Int.fract q ≠ 0 := by
    intro h
    have hd := Rat.den_intFract q
    rw [h, Rat.den_zero] at hd
    omega
  have hfp : 0 < Int.fract q := lt_of_le_of_ne (Int.fract_nonneg q) hf.symm
  have hnp : 0 < (Int.fract q).num := Rat.num_pos.mpr hfp
  let r := (Int.fract q).num.natAbs
  have hr : 0 < r := Int.natAbs_pos.mpr (ne_of_gt hnp)
  have hrint : (r : ℤ) = (Int.fract q).num := Int.natAbs_of_nonneg hnp.le
  have hnumlt : (Int.fract q).num < (q.den : ℤ) := by
    simpa only [Int.floor_fract, zero_add, one_mul, Rat.den_intFract]
      using Rat.num_lt_succ_floor_mul_den (Int.fract q)
  have hrd : r < q.den := by rw [← hrint] at hnumlt; exact_mod_cast hnumlt
  have htden : (tail q).den = r := Rat.den_inv_of_ne_zero hf
  have htnum : (tail q).num = (q.den : ℤ) := by
    simp only [tail, Rat.num_inv, (Int.sign_eq_one_iff_pos).mpr hnp, one_mul, Rat.den_intFract]
  by_cases ht : Int.fract (tail q) = 0
  · change ((Int.fract (tail q))⁻¹).den ≤ q.den / 2
    rw [ht, inv_zero, Rat.den_zero]
    omega
  · rw [tail, Rat.den_inv_of_ne_zero ht, fract_numerator, htnum, htden]
    have hmod : ((q.den : ℤ) % (r : ℤ)).natAbs = q.den % r := by
      rw [← Int.natCast_emod, Int.natAbs_natCast]
    rw [hmod]
    exact remainder_half q.den r hr hrd

theorem convergent_zero_value (k : ℕ) : convergent 0 k = 0 := by
  induction k with
  | zero => simp [convergent]
  | succ k ih => simpa [convergent] using ih

theorem convergent_of_den_one (q : ℚ) (hq : q.den = 1) (k : ℕ) : convergent q k = q := by
  have hf : Int.fract q = 0 := inv_eq_zero.mp (tail_eq_zero_of_den_one q hq)
  have hfloor : (Int.floor q : ℚ) = q := by
    have h := Int.floor_add_fract q
    simpa [hf] using h
  cases k with
  | zero => exact hfloor
  | succ k => simp [convergent, hf, convergent_zero_value, hfloor]

theorem iterated_tail_den_one (s : ℕ) (q : ℚ) (hq : q.den ≤ 2 ^ s) :
    (tail^[2 * s] q).den = 1 := by
  induction s generalizing q with
  | zero => simpa using le_antisymm hq q.den_pos
  | succ s ih =>
    have hnext : (tail (tail q)).den ≤ 2 ^ s := by
      by_cases hd : q.den = 1
      · rw [tail_eq_zero_of_den_one q hd]
        simp only [tail, Int.fract_zero, inv_zero, Rat.den_zero]
        have hp : 0 < 2 ^ s := by positivity
        omega
      · have hhalf := tail_tail_den_half q (by have := q.den_pos; omega)
        have hpow : 2 ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; omega
        rw [hpow] at hq
        omega
    have h := ih (tail (tail q)) hnext
    simpa [Nat.mul_succ, Function.iterate_add_apply, Function.iterate_succ_apply] using h

theorem convergent_stable (j k : ℕ) (q : ℚ) (h : (tail^[j] q).den = 1)
    (hjk : j ≤ k) : convergent q k = q := by
  induction j generalizing q k with
  | zero => exact convergent_of_den_one q h k
  | succ j ih =>
    cases k with
    | zero => omega
    | succ k =>
      have ht : (tail^[j] (tail q)).den = 1 := by
        simpa only [Function.iterate_succ_apply] using h
      have he := ih k (tail q) ht (by omega)
      change (Int.floor q : ℚ) + (convergent (tail q) k)⁻¹ = q
      rw [he, tail, inv_inv]
      exact Int.floor_add_fract q

theorem convergent_stable_size (q : ℚ) (k : ℕ) (hk : 2 * q.den.size ≤ k) :
    convergent q k = q := by
  apply convergent_stable (2 * q.den.size) k q _ hk
  apply iterated_tail_den_one
  exact (Nat.lt_size_self q.den).le

theorem exists_bounded_target_convergent (a q : ℚ)
    (h : |(a : ℝ) - (q : ℝ)| < 1 / (2 * (q.den : ℝ) ^ 2)) :
    ∃ k ≤ 2 * a.den.size, convergent a k = q := by
  obtain ⟨k, hk⟩ := exists_target_convergent a q h
  by_cases hle : k ≤ 2 * a.den.size
  · exact ⟨k, hle, hk⟩
  · have ha : a = q := (convergent_stable_size a k (by omega)).symm.trans hk
    exact ⟨2 * a.den.size, le_rfl, (convergent_stable_size a _ le_rfl).trans ha⟩

/-- Scan only the logarithmically many convergents, checking exact rational
inequalities and the promised denominator bound. -/
def reconstruct (l u : ℚ) (B : ℕ) : Option ℚ :=
  ((List.range (2 * u.den.size + 1)).map (convergent u)).find?
    (fun q => decide (q.den ≤ B ∧ l ≤ q ∧ q ≤ u))

theorem reconstruct_spec (l u q : ℚ) (B : ℕ) (h : reconstruct l u B = some q) :
    q.den ≤ B ∧ l ≤ q ∧ q ≤ u := by
  have hp : decide (q.den ≤ B ∧ l ≤ q ∧ q ≤ u) = true :=
    List.find?_some (p := fun (r : ℚ) => decide (r.den ≤ B ∧ l ≤ r ∧ r ≤ u)) h
  exact of_decide_eq_true hp

theorem reconstruct_exact (l u q : ℚ) (B : ℕ) (hq : q.den ≤ B)
    (hql : l ≤ q) (hqu : q ≤ u) (hwidth : u - l < (1 : ℚ) / (2 * (B : ℚ) ^ 2)) :
    reconstruct l u B = some q := by
  have hB : (0 : ℚ) < B := by exact_mod_cast lt_of_lt_of_le q.den_pos hq
  have hqb : (q.den : ℚ) ≤ B := by exact_mod_cast hq
  have hgap : |u - q| < (1 : ℚ) / (2 * (q.den : ℚ) ^ 2) := by
    rw [abs_of_nonneg (sub_nonneg.mpr hqu)]
    have hd : 2 * (q.den : ℚ) ^ 2 ≤ 2 * (B : ℚ) ^ 2 := by nlinarith
    have hi := one_div_le_one_div_of_le (by positivity : (0 : ℚ) < 2 * (q.den : ℚ) ^ 2) hd
    linarith
  have hgapR : |(u : ℝ) - (q : ℝ)| < 1 / (2 * (q.den : ℝ) ^ 2) := by
    rw [abs_of_nonneg (by exact_mod_cast sub_nonneg.mpr hqu)]
    rw [abs_of_nonneg (sub_nonneg.mpr hqu)] at hgap
    have hc := (Rat.cast_strictMono (K := ℝ)) hgap
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_mul,
      Rat.cast_ofNat, Rat.cast_pow, Rat.cast_natCast] using hc
  obtain ⟨k, hk, he⟩ := exists_bounded_target_convergent u q hgapR
  have hmem : q ∈ (List.range (2 * u.den.size + 1)).map (convergent u) := by
    apply List.mem_map.mpr
    exact ⟨k, List.mem_range.mpr (by omega), he⟩
  have hnone : reconstruct l u B ≠ none := by
    intro h
    have hbad := List.find?_eq_none.mp h q hmem
    exact hbad (by simpa using And.intro hq (And.intro hql hqu))
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hnone
  have hs := reconstruct_spec l u r B hr
  have hwide : u - l < (1 : ℚ) / (B : ℚ) ^ 2 := by
    have hpos : (0 : ℚ) < (B : ℚ) ^ 2 := by positivity
    have hi : (1 : ℚ) / (2 * (B : ℚ) ^ 2) < 1 / (B : ℚ) ^ 2 := by
      apply one_div_lt_one_div_of_lt hpos
      nlinarith
    exact hwidth.trans hi
  have heq := unique_in_interval l u r q B hs.1 hq hs.2.1 hs.2.2 hql hqu hwide
  simpa [heq] using hr

end Lax109476Proofs.RationalReconstruction

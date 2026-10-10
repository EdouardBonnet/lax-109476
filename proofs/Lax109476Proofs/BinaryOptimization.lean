import Lax109476Proofs.RationalReconstruction

namespace Lax109476Proofs.BinaryOptimization

open RationalReconstruction

/-- A threshold query says that the attained minimum is at most `t`. -/
def bisect (query : ℚ → Bool) : ℚ → ℚ → ℕ → ℚ × ℚ
  | l, u, 0 => (l, u)
  | l, u, k + 1 =>
    let old := bisect query l u k
    let mid := (old.1 + old.2) / 2
    if query mid then (old.1, mid) else (mid, old.2)

theorem bisect_invariant (query : ℚ → Bool) (v l u : ℚ)
    (hquery : ∀ t, query t = true ↔ v ≤ t) (hl : l ≤ v) (hu : v ≤ u) (k : ℕ) :
    (bisect query l u k).1 ≤ v ∧ v ≤ (bisect query l u k).2 ∧
      (bisect query l u k).2 - (bisect query l u k).1 = (u - l) / (2 : ℚ) ^ k := by
  induction k with
  | zero =>
    simp only [bisect, pow_zero, div_one]
    exact ⟨hl, hu, True.intro⟩
  | succ k ih =>
    let old := bisect query l u k
    let mid := (old.1 + old.2) / 2
    change (if query mid then (old.1, mid) else (mid, old.2)).1 ≤ v ∧
      v ≤ (if query mid then (old.1, mid) else (mid, old.2)).2 ∧
      (if query mid then (old.1, mid) else (mid, old.2)).2 -
        (if query mid then (old.1, mid) else (mid, old.2)).1 = _
    by_cases hq : query mid = true
    · have hv := (hquery mid).mp hq
      rw [if_pos hq]
      refine ⟨ih.1, hv, ?_⟩
      change (old.1 + old.2) / 2 - old.1 = _
      rw [pow_succ, div_mul_eq_div_div, ← ih.2.2]
      ring
    · have hv : mid ≤ v := (lt_of_not_ge (fun h => hq ((hquery mid).mpr h))).le
      rw [if_neg hq]
      refine ⟨hv, ih.2.1, ?_⟩
      change old.2 - (old.1 + old.2) / 2 = _
      rw [pow_succ, div_mul_eq_div_div, ← ih.2.2]
      ring

def steps (B : ℕ) : ℕ := 3 * B.size + 2

theorem initial_width_small (B : ℕ) (hB : 0 < B) :
    (B : ℚ) / (2 : ℚ) ^ steps B < 1 / (2 * (B : ℚ) ^ 2) := by
  have hBR : (0 : ℚ) < B := by exact_mod_cast hB
  have hs : (B : ℚ) < (2 : ℚ) ^ B.size := by exact_mod_cast Nat.lt_size_self B
  have hcube : (B : ℚ) ^ 3 < ((2 : ℚ) ^ B.size) ^ 3 :=
    pow_lt_pow_left₀ hs hBR.le (by decide)
  have he : (2 : ℚ) ^ steps B = 4 * ((2 : ℚ) ^ B.size) ^ 3 := by
    unfold steps
    rw [pow_add, show 3 * B.size = B.size * 3 by omega, pow_mul]
    norm_num
    ring
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  rw [he]
  nlinarith [show (0 : ℚ) < ((2 : ℚ) ^ B.size) ^ 3 by positivity]

/-- Exact recovery of a bounded rational minimum uses logarithmically many
threshold queries followed by the bounded continued-fraction scan. -/
def minimum (query : ℚ → Bool) (B : ℕ) : Option ℚ :=
  let interval := bisect query 0 B (steps B)
  reconstruct interval.1 interval.2 B

theorem minimum_exact (query : ℚ → Bool) (v : ℚ) (B : ℕ)
    (hquery : ∀ t, query t = true ↔ v ≤ t) (hvl : 0 ≤ v) (hvu : v ≤ B)
    (hden : v.den ≤ B) : minimum query B = some v := by
  obtain ⟨hl, hu, hw⟩ := bisect_invariant query v 0 B hquery hvl hvu (steps B)
  apply reconstruct_exact _ _ v B hden hl hu
  rw [hw, sub_zero]
  exact initial_width_small B (lt_of_lt_of_le v.den_pos hden)

end Lax109476Proofs.BinaryOptimization

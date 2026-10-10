import Lax109476Proofs.StandardForm

open scoped BigOperators Matrix

namespace Lax109476Proofs.LexicographicSupport

open StandardForm

def Feasible {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (x : Fin n → ℚ) : Prop := (∀ j, 0 ≤ x j) ∧ C *ᵥ x = b

/-- Successive coordinate minima select one point of a standard-form
polyhedron, without introducing arbitrary rational equality coefficients. -/
def LexMinimum {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (x : Fin n → ℚ) : Prop :=
  Feasible C b x ∧ ∀ y, Feasible C b y → ∀ i,
    (∀ j, j < i → y j = x j) → x i ≤ y i

theorem lexMinimum_independent {m n : ℕ} (C : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) (x : Fin n → ℚ) (hx : LexMinimum C b x) :
    LinearIndepOn ℚ C.col (support x : Set (Fin n)) := by
  classical
  by_contra hdep
  obtain ⟨g, hg, j₀, hj₀, hgj₀⟩ := not_linearIndepOn_finset_iff.mp hdep
  let d : Fin n → ℚ := fun j => if j ∈ support x then g j else 0
  have hd : C *ᵥ d = 0 := by
    have hsum : (∑ j, d j • C.col j) = 0 := by
      simpa [d, ← Finset.sum_filter] using hg
    simpa [Matrix.mulVec_eq_sum, Matrix.col] using hsum
  let s := Finset.univ.filter (fun j => d j ≠ 0)
  have hs : s.Nonempty := ⟨j₀, by simp [s, d, hj₀, hgj₀]⟩
  have hpos : ∀ j ∈ s, 0 < x j := by
    intro j hj
    have hdj : d j ≠ 0 := (Finset.mem_filter.mp hj).2
    have hxs : j ∈ support x := by
      by_contra hn
      exact hdj (by simp [d, hn])
    exact lt_of_le_of_ne (hx.1.1 j) ((mem_support x j).mp hxs).symm
  obtain ⟨p, hp, hratio⟩ := s.exists_min_image (fun j => x j / |d j|) hs
  let t := x p / |d p|
  have hdp : 0 < |d p| := abs_pos.mpr (Finset.mem_filter.mp hp).2
  have ht : 0 < t := div_pos (hpos p hp) hdp
  have hmove : ∀ j, |t * d j| ≤ x j := by
    intro j
    by_cases hdj : d j = 0
    · simpa [hdj] using hx.1.1 j
    · have hj : j ∈ s := by simp [s, hdj]
      have hr := hratio j hj
      rw [abs_mul, abs_of_pos ht]
      exact (le_div_iff₀ (abs_pos.mpr hdj)).mp hr
  let yPlus : Fin n → ℚ := fun j => x j + t * d j
  let yMinus : Fin n → ℚ := fun j => x j - t * d j
  have hyPlus : Feasible C b yPlus := by
    constructor
    · intro j
      have h := abs_le.mp (hmove j)
      dsimp [yPlus]
      linarith
    · change C *ᵥ (x + t • d) = b
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hd, smul_zero, add_zero, hx.1.2]
  have hyMinus : Feasible C b yMinus := by
    constructor
    · intro j
      exact sub_nonneg.mpr ((le_abs_self _).trans (hmove j))
    · change C *ᵥ (x - t • d) = b
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hd, smul_zero, sub_zero, hx.1.2]
  let i := s.min' hs
  have hi : i ∈ s := s.min'_mem hs
  have hprior : ∀ j, j < i → d j = 0 := by
    intro j hj
    by_contra hdj
    have hjs : j ∈ s := by simp [s, hdj]
    exact (not_le_of_gt hj) (s.min'_le j hjs)
  have hplus := hx.2 yPlus hyPlus i (by intro j hj; simp [yPlus, hprior j hj])
  have hminus := hx.2 yMinus hyMinus i (by intro j hj; simp [yMinus, hprior j hj])
  have hzero : t * d i = 0 := by dsimp [yPlus, yMinus] at hplus hminus; linarith
  have hdi : d i = 0 := (mul_eq_zero.mp hzero).resolve_left (ne_of_gt ht)
  exact (Finset.mem_filter.mp hi).2 hdi

end Lax109476Proofs.LexicographicSupport

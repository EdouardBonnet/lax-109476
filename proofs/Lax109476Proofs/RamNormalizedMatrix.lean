import Lax109476Proofs.RamNormalizedEntry
import Lax109476Proofs.RamZeroArray
import Lax109476Proofs.RamAdvanceState

namespace Lax109476Proofs.RamNormalizedMatrix

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamMatrixStorage RamNormalizedEntry RationalArithmeticBounds
open RamCenterUpdate RamEllipsoidStep IntegerEncoding NormalizedFeasibility

def values {m n : ℕ} (P : Program ℤ m n) (R : ℕ) : Fin ((m + n) * n) → ℚ :=
  fun k => RamNormalizedEntry.entry P R k.divNat k.modNat

theorem values_eq {m n : ℕ} (P : Program ℤ m n) (R : ℕ) :
    List.ofFn (values P R) = RamMatrixStorage.flatten (fun i j => (normalizedMatrix P R i j : ℚ)) := by
  unfold values RamMatrixStorage.flatten
  congr 1
  funext k
  exact RamNormalizedEntry.entry_eq P R k.divNat k.modNat

def fields : List String := ["norm.k", "norm.count", "query.m", "query.n", "cap.R"]

def normalizeCoordinate : Com := .seq
  (.assign "norm.row" (.div (.var "norm.k") (.var "query.n")))
  (.seq (.assign "norm.col" (.sub (.var "norm.k")
    (.mul (.var "norm.row") (.var "query.n"))))
    (.seq RamNormalizedEntry.selectEntry
      (.seq (.assign "vec.i" (.var "norm.k")) (storeReduced "search.rows"))))

set_option maxHeartbeats 800000 in
theorem normalizeCoordinate_spec (B M m n : ℕ) (P : Program ℤ m n) (R : ℕ)
    (k : Fin ((m + n) * n)) (ys : List ℚ) (hy : k.val < ys.length)
    (hM : 1 ≤ M) (hR : R ≤ M) (hdim : (m + n) * n + m + n + 1 < B) (hB : 2 * M ^ 2 + 3 < B)
    (hA : ∀ i j, (P.A i j).natAbs ≤ M) :
    Spec B (fun σ => Represents "pad.A" (RamMatrixStorage.flatten (rationalProgram P).A) σ ∧ Represents "search.rows" ys σ ∧
        σ.vars "norm.k" = k.val ∧ σ.vars "query.m" = m ∧ σ.vars "query.n" = n ∧ σ.vars "cap.R" = R)
      normalizeCoordinate
      (fun _ τ => Represents "search.rows" (ys.set k.val (values P R k)) τ ∧
        Represents "pad.A" (RamMatrixStorage.flatten (rationalProgram P).A) τ ∧ τ.vars "norm.k" = k.val ∧
        τ.vars "query.m" = m ∧ τ.vars "query.n" = n ∧ τ.vars "cap.R" = R) (72 * M.size + 140) := by
  have hkB : k.val < B := k.isLt.trans (by omega)
  have h1 : 1 < B := by omega
  have h2 : 2 < B := by nlinarith
  have hmB : m < B := by omega
  have hnB : n < B := by omega
  have hmn : m * n ≤ (m + n) * n := Nat.mul_le_mul_right n (by omega)
  have hmnB : m * n < B := by omega
  have hdivB : k.val / n < B := (Nat.div_le_self _ _).trans_lt hkB
  have hmulB : (k.val / n) * n < B := (Nat.div_mul_le_self _ _).trans_lt hkB
  have hmodB : k.val - (k.val / n) * n < B := (Nat.sub_le _ _).trans_lt hkB
  have hmod : k.val - (k.val / n) * n = k.val % n := by
    simpa [Nat.mul_comm] using (show k.val % n = k.val - n * (k.val / n)
      from Nat.mod_eq_sub_mul_div).symm
  have hMB : M < B := by nlinarith
  have hM2B : M ^ 2 < B := by omega
  have hq := RamNormalizedEntry.entry_height P R M hM hR hA k.divNat k.modNat
  have hselect := spec_with_fields fields
    (RamNormalizedEntry.selectEntry_spec B M m n R P k.divNat k.modNat hM hR hB hdim hA)
    (by intro x hx; simp [fields] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide) (by rfl)
  have hstore := spec_with_write_frame fields
    (storeReduced_spec B "search.rows" ys (values P R k) k.val hy h1 hkB
      (hq.1.trans_lt hM2B) (hq.2.trans_lt hM2B))
    (by intro x hx; simp [fields] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)
  rintro σ ⟨hσA, hσy, hσk, hσm, hσn, hσR⟩
  run_vcg [hselect, hstore]
  all_goals clear hselect hstore
  all_goals simp_all [fields, FieldsAgree, Represents, values, Fin.divNat, Fin.modNat,
    storeReduced, Com.warrs]
  all_goals aesop

def Invariant {m n : ℕ} (P : Program ℤ m n) (R : ℕ) (σ : Env) : Prop :=
  Represents "pad.A" (RamMatrixStorage.flatten (rationalProgram P).A) σ ∧
    Represents "search.rows" (filled (values P R) (σ.vars "norm.k")) σ ∧
    σ.vars "norm.k" ≤ (m + n) * n ∧ σ.vars "norm.count" = (m + n) * n ∧
    σ.vars "query.m" = m ∧ σ.vars "query.n" = n ∧ σ.vars "cap.R" = R

def normalizeStep : Com := .seq normalizeCoordinate (.assign "norm.k" (.add (.var "norm.k") (.lit 1)))

theorem normalizeStep_spec (B M m n : ℕ) (P : Program ℤ m n) (R : ℕ)
    (hM : 1 ≤ M) (hR : R ≤ M) (hdim : (m + n) * n + m + n + 1 < B) (hB : 2 * M ^ 2 + 3 < B)
    (hA : ∀ i j, (P.A i j).natAbs ≤ M) :
    Spec B (fun σ => Invariant P R σ ∧ σ.vars "norm.k" < (m + n) * n) normalizeStep
      (fun σ τ => Invariant P R τ ∧ τ.vars "norm.k" = σ.vars "norm.k" + 1) (72 * M.size + 144) := by
  rintro σ ⟨⟨hσA, hσp, hσkN, hσcount, hσm, hσn, hσR⟩, hσk⟩
  let k : Fin ((m + n) * n) := ⟨σ.vars "norm.k", hσk⟩
  obtain ⟨τ, hr₁, hτp, hτA, hτk, hτm, hτn, hτR⟩ := normalizeCoordinate_spec B M m n P R k
    (filled (values P R) k.val) (by simpa only [filled, List.length_ofFn] using k.isLt) hM hR hdim hB hA σ ⟨hσA, hσp, rfl, hσm, hσn, hσR⟩
  have hτcount := (hr₁.frame_var "norm.count" (by decide)).trans hσcount
  have h1 : 1 < B := by omega
  have hkB : k.val < B := k.isLt.trans (by omega)
  have hi1B : k.val + 1 < B := lt_of_le_of_lt k.isLt (by omega)
  have hr₂ : Run B (.assign "norm.k" (.add (.var "norm.k") (.lit 1))) τ
      (τ.setVar "norm.k" (k.val + 1)) 4 := by
    exact Run.assign (by simpa only [hτk, Bop.apply_add] using (evalB_bin
      (evalB_var (B := B) (σ := τ) (x := "norm.k") (hτk ▸ hkB)) (evalB_lit h1)
      (show Bop.add.apply (τ.vars "norm.k") 1 < B by simpa [hτk] using hi1B)))
  have hfilled : Represents "search.rows" (filled (values P R) (k.val + 1)) τ := by
    rw [← filled_step]
    exact hτp
  refine ⟨_, hr₁.seq hr₂, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Represents, arrs_setVar] using hτA
  · simpa only [Represents, arrs_setVar, vars_setVar, ite_true] using hfilled
  · change k.val + 1 ≤ (m + n) * n
    exact k.isLt
  · simpa using hτcount
  · simpa using hτm
  · simpa using hτn
  · simpa using hτR
  · simp [k]

def normalizeLoop : Com := .seq (.assign "norm.k" (.lit 0))
  (.while (.lt (.var "norm.k") (.var "norm.count")) normalizeStep)

theorem normalizeLoop_spec (B M m n : ℕ) (P : Program ℤ m n) (R : ℕ)
    (hM : 1 ≤ M) (hR : R ≤ M) (hdim : (m + n) * n + m + n + 1 < B) (hB : 2 * M ^ 2 + 3 < B)
    (hA : ∀ i j, (P.A i j).natAbs ≤ M) :
    Spec B (fun σ => Represents "pad.A" (RamMatrixStorage.flatten (rationalProgram P).A) σ ∧
        Represents "search.rows" (List.replicate ((m + n) * n) 0) σ ∧
        σ.vars "norm.count" = (m + n) * n ∧ σ.vars "query.m" = m ∧ σ.vars "query.n" = n ∧ σ.vars "cap.R" = R)
      normalizeLoop
      (fun _ τ => Represents "search.rows" (RamMatrixStorage.flatten (fun i j => (normalizedMatrix P R i j : ℚ))) τ ∧
        Represents "pad.A" (RamMatrixStorage.flatten (rationalProgram P).A) τ ∧ τ.vars "query.m" = m ∧ τ.vars "query.n" = n ∧ τ.vars "cap.R" = R)
      ((72 * M.size + 148) * ((m + n) * n) + 6) := by
  have hlo := Spec.forRangeZero "norm.k" "norm.count" (Invariant P R) ((m + n) * n) (72 * M.size + 144)
    (by omega) (fun _ h => h.2.2.1) (fun _ h => h.2.2.2.1) (normalizeStep_spec B M m n P R hM hR hdim hB hA)
  refine (hlo.pre ?_).post ?_
  · rintro σ ⟨hA, hp, hcount, hm, hn, hR⟩
    simp_all [Invariant, Represents, filled_zero]
  · rintro σ τ _ ⟨hτ, hk⟩
    refine ⟨?_, hτ.1, hτ.2.2.2.2.1, hτ.2.2.2.2.2.1, hτ.2.2.2.2.2.2⟩
    simpa only [hk, filled_done, values_eq] using hτ.2.1

def normalizeMatrix : Com := .seq
  (.assign "norm.count" (.mul (.add (.var "query.m") (.var "query.n")) (.var "query.n")))
  (.seq (.assign "vec.n" (.var "norm.count")) (.seq (RamZeroArray.zeroRationalArray "search.rows") normalizeLoop))

set_option maxHeartbeats 800000 in
theorem normalizeMatrix_spec (B M m n : ℕ) (P : Program ℤ m n) (R : ℕ)
    (hM : 1 ≤ M) (hR : R ≤ M) (hdim : (m + n) * n + m + n + 1 < B) (hB : 2 * M ^ 2 + 3 < B)
    (hA : ∀ i j, (P.A i j).natAbs ≤ M) :
    Spec B (fun σ => Represents "pad.A" (RamMatrixStorage.flatten (rationalProgram P).A) σ ∧
        Extents "search.rows" ((m + n) * n) σ ∧ σ.vars "query.m" = m ∧ σ.vars "query.n" = n ∧ σ.vars "cap.R" = R)
      normalizeMatrix
      (fun _ τ => Represents "search.rows" (RamMatrixStorage.flatten (fun i j => (normalizedMatrix P R i j : ℚ))) τ ∧
        Represents "pad.A" (RamMatrixStorage.flatten (rationalProgram P).A) τ ∧
        τ.vars "query.m" = m ∧ τ.vars "query.n" = n ∧ τ.vars "cap.R" = R)
      ((72 * M.size + 181) * ((m + n) * n) + 36) := by
  have h1 : 1 < B := by omega
  have h2 : 2 < B := by nlinarith
  have hmB : m < B := by omega
  have hnB : n < B := by omega
  have hcountB : (m + n) * n < B := by omega
  have hsumB : m + n < B := by omega
  have hzero := spec_with_write_frame ["query.m", "query.n", "norm.count", "cap.R"]
    (RamZeroArray.zeroRationalArray_spec B ((m + n) * n) "search.rows" hcountB h1)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> decide)
  have hlo := normalizeLoop_spec B M m n P R hM hR hdim hB hA
  rintro σ ⟨hσA, hσpad, hσm, hσn, hσR⟩
  have hs := hσpad ".s" (by simp)
  have hn := hσpad ".n" (by simp)
  have hd := hσpad ".d" (by simp)
  have hcost : (72 * M.size + 181) * ((m + n) * n) =
      33 * ((m + n) * n) + (72 * M.size + 148) * ((m + n) * n) := by
    simp only [Nat.add_mul]
    omega
  rw [hcost]
  run_vcg [hzero, hlo]
  all_goals clear hzero hlo
  all_goals simp_all [FieldsAgree, Represents, Extents]
  all_goals aesop

end Lax109476Proofs.RamNormalizedMatrix

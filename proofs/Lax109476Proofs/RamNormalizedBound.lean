import Lax109476Proofs.RamNormalizedBoundEntry
import Lax109476Proofs.RamZeroArray
import Lax109476Proofs.RamAdvanceState

namespace Lax109476Proofs.RamNormalizedBound

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamMatrixStorage RamNormalizedBoundEntry RationalArithmeticBounds
open RamCenterUpdate RamEllipsoidStep IntegerEncoding NormalizedFeasibility

def values {m n : ℕ} (P : Program ℤ m n) (D : ℕ) : Fin (m + n) → ℚ :=
  fun k => RamNormalizedBoundEntry.entry P D k

theorem values_eq {m n : ℕ} (P : Program ℤ m n) (D : ℕ) :
    List.ofFn (values P D) = List.ofFn (normalizedBound P (1 / (D : ℚ))) := by
  unfold values
  congr 1
  funext k
  exact RamNormalizedBoundEntry.entry_eq P D k

def fields : List String := ["norm.k", "norm.count", "query.m", "query.n", "cap.D"]

def normalizeCoordinate : Com := .seq RamNormalizedBoundEntry.selectBound
  (.seq (.assign "vec.i" (.var "norm.k")) (storeReduced "search.rhs"))

set_option maxHeartbeats 800000 in
theorem normalizeCoordinate_spec (B M m n : ℕ) (P : Program ℤ m n) (D : ℕ)
    (k : Fin (m + n)) (ys : List ℚ) (hy : k.val < ys.length)
    (hM : 1 ≤ M) (hD : 0 < D) (hDM : D ≤ M) (hdim : m + n + 1 < B) (hB : 2 * M ^ 2 + 3 < B)
    (hb : ∀ i, (P.b i).natAbs ≤ M) :
    Spec B (fun σ => Represents "pad.b" (List.ofFn (rationalProgram P).b) σ ∧ Represents "search.rhs" ys σ ∧
        σ.vars "norm.k" = k.val ∧ σ.vars "query.m" = m ∧ σ.vars "query.n" = n ∧ σ.vars "cap.D" = D)
      normalizeCoordinate
      (fun _ τ => Represents "search.rhs" (ys.set k.val (values P D k)) τ ∧
        Represents "pad.b" (List.ofFn (rationalProgram P).b) τ ∧ τ.vars "norm.k" = k.val ∧
        τ.vars "query.m" = m ∧ τ.vars "query.n" = n ∧ τ.vars "cap.D" = D) (72 * M.size + 148) := by
  have hkB : k.val < B := k.isLt.trans (by omega)
  have h1 : 1 < B := by omega
  have h2 : 2 < B := by nlinarith
  have hmB : m < B := by omega
  have hnB : n < B := by omega
  have hMB : M < B := by nlinarith
  have hM2B : 2 * M ^ 2 < B := by omega
  have hq := RamNormalizedBoundEntry.entry_height P D M hM hD hDM hb k
  have hselect := spec_with_fields fields
    (RamNormalizedBoundEntry.selectBound_spec B M m n D P k hM hD hDM hB hdim hb)
    (by intro x hx; simp [fields] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide) (by rfl)
  have hstore := spec_with_write_frame fields
    (storeReduced_spec B "search.rhs" ys (values P D k) k.val hy h1 hkB
      (hq.1.trans_lt hM2B) (hq.2.trans_lt hM2B))
    (by intro x hx; simp [fields] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)
  rintro σ ⟨hσA, hσy, hσk, hσm, hσn, hσD⟩
  run_vcg [hselect, hstore]
  all_goals clear hselect hstore
  all_goals simp_all [fields, FieldsAgree, Represents, values, Fin.divNat, Fin.modNat,
    storeReduced, Com.warrs]
  all_goals aesop

def Invariant {m n : ℕ} (P : Program ℤ m n) (D : ℕ) (σ : Env) : Prop :=
  Represents "pad.b" (List.ofFn (rationalProgram P).b) σ ∧
    Represents "search.rhs" (filled (values P D) (σ.vars "norm.k")) σ ∧
    σ.vars "norm.k" ≤ m + n ∧ σ.vars "norm.count" = m + n ∧
    σ.vars "query.m" = m ∧ σ.vars "query.n" = n ∧ σ.vars "cap.D" = D

def normalizeStep : Com := .seq normalizeCoordinate (.assign "norm.k" (.add (.var "norm.k") (.lit 1)))

theorem normalizeStep_spec (B M m n : ℕ) (P : Program ℤ m n) (D : ℕ)
    (hM : 1 ≤ M) (hD : 0 < D) (hDM : D ≤ M) (hdim : m + n + 1 < B) (hB : 2 * M ^ 2 + 3 < B)
    (hb : ∀ i, (P.b i).natAbs ≤ M) :
    Spec B (fun σ => Invariant P D σ ∧ σ.vars "norm.k" < m + n) normalizeStep
      (fun σ τ => Invariant P D τ ∧ τ.vars "norm.k" = σ.vars "norm.k" + 1) (72 * M.size + 152) := by
  rintro σ ⟨⟨hσA, hσp, hσkN, hσcount, hσm, hσn, hσD⟩, hσk⟩
  let k : Fin (m + n) := ⟨σ.vars "norm.k", hσk⟩
  obtain ⟨τ, hr₁, hτp, hτA, hτk, hτm, hτn, hτD⟩ := normalizeCoordinate_spec B M m n P D k
    (filled (values P D) k.val) (by simpa only [filled, List.length_ofFn] using k.isLt) hM hD hDM hdim hB hb σ ⟨hσA, hσp, rfl, hσm, hσn, hσD⟩
  have hτcount := (hr₁.frame_var "norm.count" (by decide)).trans hσcount
  have h1 : 1 < B := by omega
  have hkB : k.val < B := k.isLt.trans (by omega)
  have hi1B : k.val + 1 < B := lt_of_le_of_lt k.isLt (by omega)
  have hr₂ : Run B (.assign "norm.k" (.add (.var "norm.k") (.lit 1))) τ
      (τ.setVar "norm.k" (k.val + 1)) 4 := by
    exact Run.assign (by simpa only [hτk, Bop.apply_add] using (evalB_bin
      (evalB_var (B := B) (σ := τ) (x := "norm.k") (hτk ▸ hkB)) (evalB_lit h1)
      (show Bop.add.apply (τ.vars "norm.k") 1 < B by simpa [hτk] using hi1B)))
  have hfilled : Represents "search.rhs" (filled (values P D) (k.val + 1)) τ := by
    rw [← filled_step]
    exact hτp
  refine ⟨_, hr₁.seq hr₂, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Represents, arrs_setVar] using hτA
  · simpa only [Represents, arrs_setVar, vars_setVar, ite_true] using hfilled
  · change k.val + 1 ≤ m + n
    exact k.isLt
  · simpa using hτcount
  · simpa using hτm
  · simpa using hτn
  · simpa using hτD
  · simp [k]

def normalizeLoop : Com := .seq (.assign "norm.k" (.lit 0))
  (.while (.lt (.var "norm.k") (.var "norm.count")) normalizeStep)

theorem normalizeLoop_spec (B M m n : ℕ) (P : Program ℤ m n) (D : ℕ)
    (hM : 1 ≤ M) (hD : 0 < D) (hDM : D ≤ M) (hdim : m + n + 1 < B) (hB : 2 * M ^ 2 + 3 < B)
    (hb : ∀ i, (P.b i).natAbs ≤ M) :
    Spec B (fun σ => Represents "pad.b" (List.ofFn (rationalProgram P).b) σ ∧
        Represents "search.rhs" (List.replicate (m + n) 0) σ ∧
        σ.vars "norm.count" = m + n ∧ σ.vars "query.m" = m ∧ σ.vars "query.n" = n ∧ σ.vars "cap.D" = D)
      normalizeLoop
      (fun _ τ => Represents "search.rhs" (List.ofFn (normalizedBound P (1 / (D : ℚ)))) τ ∧
        Represents "pad.b" (List.ofFn (rationalProgram P).b) τ ∧ τ.vars "query.m" = m ∧ τ.vars "query.n" = n ∧ τ.vars "cap.D" = D)
      ((72 * M.size + 156) * (m + n) + 6) := by
  have hlo := Spec.forRangeZero "norm.k" "norm.count" (Invariant P D) (m + n) (72 * M.size + 152)
    (by omega) (fun _ h => h.2.2.1) (fun _ h => h.2.2.2.1) (normalizeStep_spec B M m n P D hM hD hDM hdim hB hb)
  refine (hlo.pre ?_).post ?_
  · rintro σ ⟨hb, hp, hcount, hm, hn, hD⟩
    simp_all [Invariant, Represents, filled_zero]
  · rintro σ τ _ ⟨hτ, hk⟩
    refine ⟨?_, hτ.1, hτ.2.2.2.2.1, hτ.2.2.2.2.2.1, hτ.2.2.2.2.2.2⟩
    simpa only [hk, filled_done, values_eq] using hτ.2.1

def normalizeBound : Com := .seq
  (.assign "norm.count" (.add (.var "query.m") (.var "query.n")))
  (.seq (.assign "vec.n" (.var "norm.count")) (.seq (RamZeroArray.zeroRationalArray "search.rhs") normalizeLoop))

set_option maxHeartbeats 800000 in
theorem normalizeBound_spec (B M m n : ℕ) (P : Program ℤ m n) (D : ℕ)
    (hM : 1 ≤ M) (hD : 0 < D) (hDM : D ≤ M) (hdim : m + n + 1 < B) (hB : 2 * M ^ 2 + 3 < B)
    (hb : ∀ i, (P.b i).natAbs ≤ M) :
    Spec B (fun σ => Represents "pad.b" (List.ofFn (rationalProgram P).b) σ ∧
        Extents "search.rhs" (m + n) σ ∧ σ.vars "query.m" = m ∧ σ.vars "query.n" = n ∧ σ.vars "cap.D" = D)
      normalizeBound
      (fun _ τ => Represents "search.rhs" (List.ofFn (normalizedBound P (1 / (D : ℚ)))) τ ∧
        Represents "pad.b" (List.ofFn (rationalProgram P).b) τ ∧
        τ.vars "query.m" = m ∧ τ.vars "query.n" = n ∧ τ.vars "cap.D" = D)
      ((72 * M.size + 189) * (m + n) + 36) := by
  have h1 : 1 < B := by omega
  have h2 : 2 < B := by nlinarith
  have hmB : m < B := by omega
  have hnB : n < B := by omega
  have hcountB : m + n < B := by omega
  have hzero := spec_with_write_frame ["query.m", "query.n", "norm.count", "cap.D"]
    (RamZeroArray.zeroRationalArray_spec B (m + n) "search.rhs" hcountB h1)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> decide)
  have hlo := normalizeLoop_spec B M m n P D hM hD hDM hdim hB hb
  rintro σ ⟨hσA, hσpad, hσm, hσn, hσD⟩
  have hs := hσpad ".s" (by simp)
  have hn := hσpad ".n" (by simp)
  have hd := hσpad ".d" (by simp)
  have hcost : (72 * M.size + 189) * (m + n) =
      33 * (m + n) + (72 * M.size + 156) * (m + n) := by
    simp only [Nat.add_mul]
    omega
  rw [hcost]
  run_vcg [hzero, hlo]
  all_goals clear hzero hlo
  all_goals simp_all [FieldsAgree, Represents, Extents]
  all_goals aesop

end Lax109476Proofs.RamNormalizedBound

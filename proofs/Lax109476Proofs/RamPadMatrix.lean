import Lax109476Proofs.RamPadSelector
import Lax109476Proofs.RamZeroArray
import Lax109476Proofs.RamAdvanceState

namespace Lax109476Proofs.RamPadMatrix

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamMatrixStorage RamPadEntries RationalArithmeticBounds
open RamCenterUpdate RamEllipsoidStep

def fields : List String := ["pad.k", "pad.count", "source.m", "source.n"]

def padCoordinate : Com := .seq
  (.assign "pad.row" (.div (.var "pad.k") (.add (.var "source.n") (.lit 2))))
  (.seq (.assign "pad.col" (.sub (.var "pad.k")
    (.mul (.var "pad.row") (.add (.var "source.n") (.lit 2)))))
    (.seq RamPadSelector.selectEntry
      (.seq (.assign "vec.i" (.var "pad.k")) (storeReduced "pad.A"))))

set_option maxHeartbeats 800000 in
theorem padCoordinate_spec (B M m n : ℕ) (P : Program ℚ m n)
    (k : Fin ((m + 2) * (n + 2))) (ys : List ℚ) (hy : k.val < ys.length)
    (hM : 1 ≤ M) (hMB : M < B) (hB : (m + 2) * (n + 2) + m + n + 4 < B)
    (hA : ∀ i j, Height (P.A i j) M) :
    Spec B (fun σ => Represents "query.A" (RamMatrixStorage.flatten P.A) σ ∧ Represents "pad.A" ys σ ∧
        σ.vars "pad.k" = k.val ∧ σ.vars "source.m" = m ∧ σ.vars "source.n" = n)
      padCoordinate
      (fun _ τ => Represents "pad.A" (ys.set k.val (values P k)) τ ∧
        Represents "query.A" (RamMatrixStorage.flatten P.A) τ ∧ τ.vars "pad.k" = k.val ∧
        τ.vars "source.m" = m ∧ τ.vars "source.n" = n) 70 := by
  have hkB : k.val < B := k.isLt.trans (by omega)
  have h1 : 1 < B := by omega
  have h2 : 2 < B := by omega
  have hmB : m + 2 < B := by omega
  have hnB : n + 2 < B := by omega
  have hmn : m * n ≤ (m + 2) * (n + 2) := Nat.mul_le_mul (by omega) (by omega)
  have hmnB : m * n < B := by omega
  have hdivB : k.val / (n + 2) < B := (Nat.div_le_self _ _).trans_lt hkB
  have hmulB : (k.val / (n + 2)) * (n + 2) < B := (Nat.div_mul_le_self _ _).trans_lt hkB
  have hmodB : k.val - (k.val / (n + 2)) * (n + 2) < B := (Nat.sub_le _ _).trans_lt hkB
  have hmod : k.val - (k.val / (n + 2)) * (n + 2) = k.val % (n + 2) := by
    simpa [Nat.mul_comm] using (show k.val % (n + 2) = k.val - (n + 2) * (k.val / (n + 2))
      from Nat.mod_eq_sub_mul_div).symm
  have hq := entry_height P M hM hA k.divNat k.modNat
  have hselect := spec_with_fields fields
    (RamPadSelector.selectEntry_spec B M m n P k.divNat k.modNat h1 hM hMB hmB hnB hmnB hA)
    (by intro x hx; simp [fields] at hx; rcases hx with rfl | rfl | rfl | rfl <;> decide) (by rfl)
  have hstore := spec_with_write_frame fields
    (storeReduced_spec B "pad.A" ys (values P k) k.val hy h1 hkB
      (hq.1.trans_lt hMB) (hq.2.trans_lt hMB))
    (by intro x hx; simp [fields] at hx; rcases hx with rfl | rfl | rfl | rfl <;> decide)
  rintro σ ⟨hσA, hσy, hσk, hσm, hσn⟩
  run_vcg [hselect, hstore]
  all_goals clear hselect hstore
  all_goals simp_all [fields, FieldsAgree, Represents, values, Fin.divNat, Fin.modNat,
    storeReduced, Com.warrs]
  all_goals aesop

def Invariant {m n : ℕ} (P : Program ℚ m n) (σ : Env) : Prop :=
  Represents "query.A" (RamMatrixStorage.flatten P.A) σ ∧
    Represents "pad.A" (filled (values P) (σ.vars "pad.k")) σ ∧
    σ.vars "pad.k" ≤ (m + 2) * (n + 2) ∧ σ.vars "pad.count" = (m + 2) * (n + 2) ∧
    σ.vars "source.m" = m ∧ σ.vars "source.n" = n

def padStep : Com := .seq padCoordinate (.assign "pad.k" (.add (.var "pad.k") (.lit 1)))

theorem padStep_spec (B M m n : ℕ) (P : Program ℚ m n)
    (hM : 1 ≤ M) (hMB : M < B) (hB : (m + 2) * (n + 2) + m + n + 4 < B)
    (hA : ∀ i j, Height (P.A i j) M) :
    Spec B (fun σ => Invariant P σ ∧ σ.vars "pad.k" < (m + 2) * (n + 2)) padStep
      (fun σ τ => Invariant P τ ∧ τ.vars "pad.k" = σ.vars "pad.k" + 1) 74 := by
  rintro σ ⟨⟨hσA, hσp, hσkN, hσcount, hσm, hσn⟩, hσk⟩
  let k : Fin ((m + 2) * (n + 2)) := ⟨σ.vars "pad.k", hσk⟩
  obtain ⟨τ, hr₁, hτp, hτA, hτk, hτm, hτn⟩ := padCoordinate_spec B M m n P k
    (filled (values P) k.val) (by simpa only [filled, List.length_ofFn] using k.isLt) hM hMB hB hA σ ⟨hσA, hσp, rfl, hσm, hσn⟩
  have hτcount := (hr₁.frame_var "pad.count" (by decide)).trans hσcount
  have h1 : 1 < B := by omega
  have hkB : k.val < B := k.isLt.trans (by omega)
  have hi1B : k.val + 1 < B := lt_of_le_of_lt k.isLt (by omega)
  have hr₂ : Run B (.assign "pad.k" (.add (.var "pad.k") (.lit 1))) τ
      (τ.setVar "pad.k" (k.val + 1)) 4 := by
    exact Run.assign (by simpa only [hτk, Bop.apply_add] using (evalB_bin
      (evalB_var (B := B) (σ := τ) (x := "pad.k") (hτk ▸ hkB)) (evalB_lit h1)
      (show Bop.add.apply (τ.vars "pad.k") 1 < B by simpa [hτk] using hi1B)))
  have hfilled : Represents "pad.A" (filled (values P) (k.val + 1)) τ := by
    rw [← filled_step]
    exact hτp
  refine ⟨_, hr₁.seq hr₂, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Represents, arrs_setVar] using hτA
  · simpa only [Represents, arrs_setVar, vars_setVar, ite_true] using hfilled
  · change k.val + 1 ≤ (m + 2) * (n + 2)
    exact k.isLt
  · simpa using hτcount
  · simpa using hτm
  · simpa using hτn
  · simp [k]

def padLoop : Com := .seq (.assign "pad.k" (.lit 0))
  (.while (.lt (.var "pad.k") (.var "pad.count")) padStep)

theorem padLoop_spec (B M m n : ℕ) (P : Program ℚ m n)
    (hM : 1 ≤ M) (hMB : M < B) (hB : (m + 2) * (n + 2) + m + n + 4 < B)
    (hA : ∀ i j, Height (P.A i j) M) :
    Spec B (fun σ => Represents "query.A" (RamMatrixStorage.flatten P.A) σ ∧
        Represents "pad.A" (List.replicate ((m + 2) * (n + 2)) 0) σ ∧
        σ.vars "pad.count" = (m + 2) * (n + 2) ∧ σ.vars "source.m" = m ∧ σ.vars "source.n" = n)
      padLoop
      (fun _ τ => Represents "pad.A" (RamMatrixStorage.flatten (FeasibilityPadding.pad P).A) τ ∧
        Represents "query.A" (RamMatrixStorage.flatten P.A) τ ∧ τ.vars "source.m" = m ∧ τ.vars "source.n" = n)
      (78 * ((m + 2) * (n + 2)) + 6) := by
  have hlo := Spec.forRangeZero "pad.k" "pad.count" (Invariant P) ((m + 2) * (n + 2)) 74
    (by omega) (fun _ h => h.2.2.1) (fun _ h => h.2.2.2.1) (padStep_spec B M m n P hM hMB hB hA)
  refine (hlo.pre ?_).post ?_
  · rintro σ ⟨hA, hp, hcount, hm, hn⟩
    simp_all [Invariant, Represents, filled_zero]
  · rintro σ τ _ ⟨hτ, hk⟩
    refine ⟨?_, hτ.1, hτ.2.2.2.2.1, hτ.2.2.2.2.2⟩
    simpa only [hk, filled_done, values_eq] using hτ.2.1

def padMatrix : Com := .seq
  (.assign "pad.count" (.mul (.add (.var "source.m") (.lit 2)) (.add (.var "source.n") (.lit 2))))
  (.seq (.assign "vec.n" (.var "pad.count")) (.seq (RamZeroArray.zeroRationalArray "pad.A") padLoop))

set_option maxHeartbeats 800000 in
theorem padMatrix_spec (B M m n : ℕ) (P : Program ℚ m n)
    (hM : 1 ≤ M) (hMB : M < B) (hB : (m + 2) * (n + 2) + m + n + 4 < B)
    (hA : ∀ i j, Height (P.A i j) M) :
    Spec B (fun σ => Represents "query.A" (RamMatrixStorage.flatten P.A) σ ∧
        Extents "pad.A" ((m + 2) * (n + 2)) σ ∧ σ.vars "source.m" = m ∧ σ.vars "source.n" = n)
      padMatrix
      (fun _ τ => Represents "pad.A" (RamMatrixStorage.flatten (FeasibilityPadding.pad P).A) τ ∧
        Represents "query.A" (RamMatrixStorage.flatten P.A) τ ∧
        τ.vars "source.m" = m ∧ τ.vars "source.n" = n)
      (111 * ((m + 2) * (n + 2)) + 36) := by
  have h1 : 1 < B := by omega
  have h2 : 2 < B := by omega
  have hmB : m + 2 < B := by omega
  have hnB : n + 2 < B := by omega
  have hcountB : (m + 2) * (n + 2) < B := by omega
  have hzero := spec_with_write_frame ["source.m", "source.n", "pad.count"]
    (RamZeroArray.zeroRationalArray_spec B ((m + 2) * (n + 2)) "pad.A" hcountB h1)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> decide)
  have hlo := padLoop_spec B M m n P hM hMB hB hA
  rintro σ ⟨hσA, hσpad, hσm, hσn⟩
  have hs := hσpad ".s" (by simp)
  have hn := hσpad ".n" (by simp)
  have hd := hσpad ".d" (by simp)
  run_vcg [hzero, hlo]
  all_goals clear hzero hlo
  all_goals simp_all [FieldsAgree, Represents, Extents]
  all_goals aesop

end Lax109476Proofs.RamPadMatrix

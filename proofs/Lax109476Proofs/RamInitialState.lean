import Lax109476Proofs.RamShapeUpdate
import Lax109476Proofs.RamAdvanceState

open scoped Matrix

namespace Lax109476Proofs.RamInitialState

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamZeroArray RamMatrixStorage RamCenterUpdate

def identityEntry (n k : ℕ) : ℚ := if k / n = k % n then 1 else 0

def identityValues (n : ℕ) : Fin (n * n) → ℚ := fun k => identityEntry n k.val

def identityCoordinate : Com :=
  .seq (.assign "vec.i" (.var "init.k"))
    (.seq (.assign "init.row" (.div (.var "init.k") (.var "vec.n")))
      (.seq (.assign "init.col" (.sub (.var "init.k") (.mul (.var "init.row") (.var "vec.n"))))
        (.seq (.assign "rat.s" (.lit 0))
          (.seq (.assign "rat.d" (.lit 1))
            (.seq (.ite (.eq (.var "init.row") (.var "init.col"))
              (.assign "rat.n" (.lit 1)) (.assign "rat.n" (.lit 0))) (storeReduced "ell.shape"))))))

set_option maxHeartbeats 500000 in
theorem identityCoordinate_spec (B n k : ℕ) (xs : List ℚ)
    (hnB : n < B) (hkB : k < B) (h1 : 1 < B) (hk : k < xs.length) :
    Spec B (fun σ => Represents "ell.shape" xs σ ∧ σ.vars "vec.n" = n ∧ σ.vars "init.k" = k)
      identityCoordinate
      (fun _ τ => Represents "ell.shape" (xs.set k (identityEntry n k)) τ) 35 := by
  have hdiv : k / n < B := (Nat.div_le_self k n).trans_lt hkB
  have hprod : (k / n) * n < B := (Nat.div_mul_le_self k n).trans_lt hkB
  have hmod : k % n < B := (Nat.mod_le k n).trans_lt hkB
  have hmodEq : k - (k / n) * n = k % n := by
    simpa [Nat.mul_comm] using (show k % n = k - n * (k / n) from Nat.mod_eq_sub_mul_div).symm
  have hnum : (identityEntry n k).num.natAbs < B := by
    unfold identityEntry
    split_ifs <;> simp_all <;> omega
  have hden : (identityEntry n k).den < B := by unfold identityEntry; split_ifs <;> simp_all
  have hstore := storeReduced_spec B "ell.shape" xs (identityEntry n k) k hk h1 hkB hnum hden
  rintro σ ⟨hσA, hσn, hσk⟩
  run_vcg [hstore]
  all_goals clear hstore
  all_goals simp_all [FractionOutput, identityEntry, Represents, fractionValue]

def IdentityInvariant (n : ℕ) (σ : Env) : Prop :=
  Represents "ell.shape" (filled (identityValues n) (σ.vars "init.k")) σ ∧
    σ.vars "init.k" ≤ n * n ∧ σ.vars "init.count" = n * n ∧ σ.vars "vec.n" = n

def identityStep : Com := .seq identityCoordinate (.assign "init.k" (.add (.var "init.k") (.lit 1)))

theorem identityStep_spec (B n : ℕ) (hnB : n < B) (hnnB : n * n < B) (h1 : 1 < B) :
    Spec B (fun σ => IdentityInvariant n σ ∧ σ.vars "init.k" < n * n) identityStep
      (fun σ τ => IdentityInvariant n τ ∧ τ.vars "init.k" = σ.vars "init.k" + 1) 39 := by
  rintro σ ⟨⟨hσA, hσkN, hσcount, hσn⟩, hσk⟩
  let k : Fin (n * n) := ⟨σ.vars "init.k", hσk⟩
  obtain ⟨τ, hr₁, hτA⟩ := identityCoordinate_spec B n k.val (filled (identityValues n) k.val)
    hnB (k.isLt.trans hnnB) h1 (by simp [filled]) σ ⟨hσA, hσn, rfl⟩
  have hτk : τ.vars "init.k" = k.val := hr₁.frame_var _ (by decide)
  have hτn : τ.vars "vec.n" = n := (hr₁.frame_var _ (by decide)).trans hσn
  have hτcount : τ.vars "init.count" = n * n := (hr₁.frame_var _ (by decide)).trans hσcount
  have haddB : Bop.add.apply (τ.vars "init.k") 1 < B := by
    simpa [Bop.apply, hτk] using lt_of_le_of_lt k.isLt hnnB
  have hr₂ : Run B (.assign "init.k" (.add (.var "init.k") (.lit 1))) τ
      (τ.setVar "init.k" (k.val + 1)) 4 := by
    exact Run.assign (by simpa [Bop.apply, hτk] using
      (evalB_bin (evalB_var (hτk ▸ k.isLt.trans hnnB)) (evalB_lit h1) haddB))
  have hfilled : Represents "ell.shape" (filled (identityValues n) (k.val + 1)) τ := by
    rw [← filled_step]
    exact hτA
  refine ⟨_, hr₁.seq hr₂, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Represents, arrs_setVar, vars_setVar, ite_true] using hfilled
  · change k.val + 1 ≤ n * n
    exact k.isLt
  · simpa using hτcount
  · simpa using hτn
  · simp [k]

def identityLoop : Com := .seq (.assign "init.count" (.mul (.var "vec.n") (.var "vec.n")))
  (.seq (.assign "init.k" (.lit 0)) (.while (.lt (.var "init.k") (.var "init.count")) identityStep))

theorem identityValues_eq (n : ℕ) : List.ofFn (identityValues n) = flatten (1 : Matrix (Fin n) (Fin n) ℚ) := by
  unfold flatten
  congr 1
  funext k
  simp [identityValues, identityEntry, Matrix.one_apply, Fin.ext_iff, Fin.divNat, Fin.modNat]

theorem identityLoop_spec (B n : ℕ) (hnB : n < B) (hnnB : n * n < B) (h1 : 1 < B) :
    Spec B (fun σ => Represents "ell.shape" (List.replicate (n * n) 0) σ ∧ σ.vars "vec.n" = n)
      identityLoop
      (fun _ τ => Represents "ell.shape" (flatten (1 : Matrix (Fin n) (Fin n) ℚ)) τ ∧ τ.vars "vec.n" = n)
      (43 * (n * n) + 10) := by
  have hlo := Spec.forRangeZero "init.k" "init.count" (IdentityInvariant n) (n * n) 39 hnnB
    (fun _ h => h.2.1) (fun _ h => h.2.2.1) (identityStep_spec B n hnB hnnB h1)
  have hloop : Spec B (fun σ => Represents "ell.shape" (List.replicate (n * n) 0) σ ∧
      σ.vars "init.count" = n * n ∧ σ.vars "vec.n" = n)
      (.seq (.assign "init.k" (.lit 0)) (.while (.lt (.var "init.k") (.var "init.count")) identityStep))
      (fun _ τ => Represents "ell.shape" (flatten (1 : Matrix (Fin n) (Fin n) ℚ)) τ ∧ τ.vars "vec.n" = n)
      (43 * (n * n) + 6) := by
    refine (hlo.pre ?_).post ?_
    · rintro σ ⟨hA, hcount, hn⟩
      simp_all [IdentityInvariant, Represents, filled_zero]
    · rintro σ τ _ ⟨hτ, hk⟩
      refine ⟨?_, hτ.2.2.2⟩
      simpa only [hk, filled_done, identityValues_eq] using hτ.1
  rintro σ ⟨hσA, hσn⟩
  run_vcg [hloop]
  all_goals clear hloop hlo
  all_goals simp_all [Represents]

def initializeIdentity : Com := .seq (.assign "init.savedn" (.var "vec.n"))
  (.seq (.assign "vec.n" (.mul (.var "vec.n") (.var "vec.n")))
    (.seq (zeroRationalArray "ell.shape")
      (.seq (.assign "vec.n" (.var "init.savedn")) identityLoop)))

theorem initializeIdentity_spec (B n : ℕ) (hnB : n < B) (hnnB : n * n < B) (h1 : 1 < B) :
    Spec B (fun σ => (σ.arrs "ell.shape.s").length = n * n ∧
        (σ.arrs "ell.shape.n").length = n * n ∧ (σ.arrs "ell.shape.d").length = n * n ∧ σ.vars "vec.n" = n)
      initializeIdentity
      (fun _ τ => Represents "ell.shape" (flatten (1 : Matrix (Fin n) (Fin n) ℚ)) τ ∧ τ.vars "vec.n" = n)
      (76 * (n * n) + 36) := by
  have hz := spec_with_write_frame ["init.savedn"] (zeroRationalArray_spec B (n * n) "ell.shape" hnnB h1)
    (by decide)
  have hi := identityLoop_spec B n hnB hnnB h1
  rintro σ ⟨hs, hnum, hd, hn⟩
  run_vcg [hz, hi]
  all_goals clear hz hi
  all_goals simp_all [Represents, FieldsAgree]

def initialState : Com := .seq (zeroRationalArray "ell.center")
  (.seq initializeIdentity (.assign "iter.k" (.lit 0)))

theorem initialState_spec (B n : ℕ) (hnB : n < B) (hnnB : n * n < B) (h1 : 1 < B) :
    Spec B (fun σ => RamEllipsoidStep.Extents "ell.center" n σ ∧
        RamEllipsoidStep.Extents "ell.shape" (n * n) σ ∧ RamEllipsoidStep.Workspace n σ ∧
        σ.vars "vec.n" = n)
      initialState
      (fun _ τ => Represents "ell.center" (List.ofFn (0 : Fin n → ℚ)) τ ∧
        Represents "ell.shape" (flatten (1 : Matrix (Fin n) (Fin n) ℚ)) τ ∧
        RamEllipsoidStep.Workspace n τ ∧ τ.vars "vec.n" = n ∧ τ.vars "iter.k" = 0)
      (33 * n + 76 * (n * n) + 56) := by
  rintro σ ⟨hσc, hσA, hσw, hσn⟩
  obtain ⟨τ, hr₁, hτc, hτn, _⟩ := zeroRationalArray_spec B n "ell.center" hnB h1 σ
    ⟨hσc ".s" (by simp), hσc ".n" (by simp), hσc ".d" (by simp), hσn⟩
  have hτA := RamAdvanceState.extents_of_run hr₁ "ell.shape" (n * n) hσA
  obtain ⟨υ, hr₂, hυA, hυn⟩ := initializeIdentity_spec B n hnB hnnB h1 τ
    ⟨hτA ".s" (by simp), hτA ".n" (by simp), hτA ".d" (by simp), hτn⟩
  have hυc := RamEllipsoidUpdate.represents_frame hr₂ "ell.center" _ hτc
    (by decide) (by decide) (by decide)
  have hr₃ : Run B (.assign "iter.k" (.lit 0)) υ (υ.setVar "iter.k" 0) 2 :=
    Run.assign (evalB_lit (by omega))
  have hr := hr₁.seq (hr₂.seq hr₃)
  have hzero : List.ofFn (0 : Fin n → ℚ) = List.replicate n 0 := List.ofFn_const n 0
  refine ⟨_, hr.mono (by omega), ?_, ?_, RamAdvanceState.workspace_of_run hr n hσw, ?_, ?_⟩
  · simpa only [hzero, Represents, arrs_setVar] using hυc
  · simpa only [Represents, arrs_setVar] using hυA
  · simpa using hυn
  · simp

end Lax109476Proofs.RamInitialState

import Lax109476Proofs.RamNonzero
import Lax109476Proofs.RamRowCopy
import Lax109476Proofs.RamTrajectoryBounds

namespace Lax109476Proofs.RamNormalSelection

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds RamZeroArray
open RamEllipsoidStep RamAdvanceState RamMatrixRows EllipsoidSearch

def fallbackNormal : Com := .seq (zeroRationalArray "ell.normal")
  (.seq (.assign "vec.i" (.lit 0))
    (.seq (.assign "rat.s" (.lit 0)) (.seq (.assign "rat.n" (.lit 1))
      (.seq (.assign "rat.d" (.lit 1)) (storeReduced "ell.normal")))))

theorem fallback_values (n : ℕ) :
    (List.replicate n (0 : ℚ)).set 0 1 = List.ofFn (EllipsoidSearch.fallbackNormal n) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    rw [List.getElem_set]
    simp [EllipsoidSearch.fallbackNormal, List.getElem_replicate, eq_comm]

theorem fallbackNormal_spec (B n : ℕ) (hn : 0 < n) (hnB : n < B) (h1 : 1 < B) :
    Spec B (fun σ => Extents "ell.normal" n σ ∧ σ.vars "vec.n" = n)
      fallbackNormal
      (fun _ τ => Represents "ell.normal" (List.ofFn (EllipsoidSearch.fallbackNormal n)) τ ∧
        τ.vars "vec.n" = n) (33 * n + 39) := by
  have hz := zeroRationalArray_spec B n "ell.normal" hnB h1
  have hs := spec_with_write_frame ["vec.n"]
    (storeReduced_spec B "ell.normal" (List.replicate n 0) 1 0 (by simpa using hn) h1
      (by omega) (by simpa using h1) (by simpa using h1)) (by decide)
  rintro σ ⟨hσExt, hσn⟩
  run_vcg [hz, hs]
  all_goals clear hz hs
  all_goals simp_all [Extents, Represents, FieldsAgree, FractionOutput, fractionValue, fallback_values]
  all_goals first | omega | (exfalso; omega) | aesop

def copySelectedRow (a : String) : Com :=
  .seq (.assign "row.base" (.mul (.var "row.first") (.var "vec.n")))
    (RamRowCopy.copyRow a "ell.normal")

theorem copySelectedRow_spec (B m n H : ℕ) (a : String)
    (A : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) (h1 : 1 < B)
    (hdims : m + n + m * n + 1 < B) (hHB : H < B)
    (hA : ∀ j, Height (A i j) H) (ha : RamCopy.Disjoint a "ell.normal") :
    Spec B (fun σ => MatrixRows a A σ ∧ Extents "ell.normal" n σ ∧
        σ.vars "vec.n" = n ∧ σ.vars "row.first" = i.val)
      (copySelectedRow a)
      (fun _ τ => Represents "ell.normal" (List.ofFn (A i)) τ ∧ τ.vars "vec.n" = n)
      (77 * n + 28) := by
  have hib : i.val < B := by have := i.isLt; omega
  have hnB : n < B := by omega
  have hbase : i.val * n + n ≤ m * n := by
    calc
      i.val * n + n = (i.val + 1) * n := by ring
      _ ≤ m * n := Nat.mul_le_mul_right n i.isLt
  have hbaseB : i.val * n + n < B := by omega
  have hc := RamRowCopy.copyRow_spec B n H (i.val * n) a "ell.normal" (A i) h1 hbaseB hHB hA ha
  rintro σ ⟨hσrows, hσExt, hσn, hσi⟩
  have hrow := hσrows i
  run_vcg [hc]
  all_goals clear hc
  all_goals simp_all [Extents, Slice]
  all_goals first | omega | (exfalso; omega) | aesop

def ensureNormal : Com := .seq (RamNonzero.scan "ell.normal")
  (.ite (.eq (.var "nonzero.flag") (.lit 0)) fallbackNormal .skip)

theorem ensureNormal_spec (B n H : ℕ) (v : Fin n → ℚ) (hn : 0 < n) (hnB : n < B)
    (h1 : 1 < B) (hHB : H < B) (hv : ∀ i, Height (v i) H) :
    Spec B (fun σ => Represents "ell.normal" (List.ofFn v) σ ∧ σ.vars "vec.n" = n)
      ensureNormal
      (fun _ τ => Represents "ell.normal"
          (List.ofFn (if v = 0 then EllipsoidSearch.fallbackNormal n else v)) τ ∧ τ.vars "vec.n" = n)
      (49 * n + 51) := by
  rintro σ ⟨hσv, hσn⟩
  obtain ⟨τ, hr₁, hflag, hiff, hτv, hτn⟩ := RamNonzero.scan_spec B n H "ell.normal" v
    hnB h1 hHB hv σ ⟨hσv, hσn⟩
  have hflagB : τ.vars "nonzero.flag" < B := hflag.trans_lt h1
  have h0 : 0 < B := by omega
  by_cases hvzero : v = 0
  · have hflag0 : τ.vars "nonzero.flag" = 0 := by
      have hnot : τ.vars "nonzero.flag" ≠ 1 := fun hf => (hiff.mp hf) hvzero
      omega
    have hτExt : Extents "ell.normal" n τ := by simpa using represents_extents _ _ _ hτv
    obtain ⟨υ, hr₂, hυv, hυn⟩ := fallbackNormal_spec B n hn hnB h1 τ ⟨hτExt, hτn⟩
    have hb : (Cond.eq (.var "nonzero.flag") (.lit 0)).evalB B τ = some true := by
      simpa [hflag0] using (evalB_condEq (evalB_var hflagB) (evalB_lit h0))
    refine ⟨υ, (hr₁.seq (Run.ite_true hb hr₂)).mono (by simp only [Cond.size, Expr.size]; omega), ?_, hυn⟩
    simpa only [if_pos hvzero] using hυv
  · have hflag1 : τ.vars "nonzero.flag" = 1 := hiff.mpr hvzero
    have hb : (Cond.eq (.var "nonzero.flag") (.lit 0)).evalB B τ = some false := by
      simpa [hflag1] using (evalB_condEq (evalB_var hflagB) (evalB_lit h0))
    refine ⟨τ, (hr₁.seq (Run.ite_false hb Run.skip)).mono (by simp only [Cond.size, Expr.size]; omega), ?_, hτn⟩
    simpa only [if_neg hvzero] using hτv

def selectNormal (a : String) : Com :=
  .ite (.lt (.var "row.first") (.var "row.m"))
    (.seq (copySelectedRow a) ensureNormal) fallbackNormal

theorem selectNormal_integer_spec (B m n H : ℕ) (a : String)
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ) (c : Fin n → ℚ)
    (hn : 0 < n) (h1 : 1 < B) (hdims : m + n + m * n + 1 < B)
    (hH : 1 ≤ H) (hHB : H < B) (hA : ∀ i j, (A i j).natAbs ≤ H)
    (ha : RamCopy.Disjoint a "ell.normal") :
    Spec B (fun σ => MatrixRows a (fun i j => (A i j : ℚ)) σ ∧ Extents "ell.normal" n σ ∧
        σ.vars "vec.n" = n ∧ σ.vars "row.m" = m ∧ σ.vars "row.first" =
          ((RationalSeparation.firstViolation A b c).map Fin.val).getD m)
      (selectNormal a)
      (fun _ τ => Represents "ell.normal" (List.ofFn (EllipsoidSearch.selectedNormal A b c)) τ ∧
        τ.vars "vec.n" = n) (126 * n + 83) := by
  have hnB : n < B := by omega
  have hmB : m < B := by omega
  have hfall := fallbackNormal_spec B n hn hnB h1
  rintro σ ⟨hσrows, hσExt, hσn, hσm, hσfirst⟩
  cases hf : RationalSeparation.firstViolation A b c with
  | none =>
    simp only [hf, Option.map_none, Option.getD_none] at hσfirst
    obtain ⟨τ, hr, hτ, hτn⟩ := hfall σ ⟨hσExt, hσn⟩
    have hb : (Cond.lt (.var "row.first") (.var "row.m")).evalB B σ = some false := by
      simpa [hσfirst, hσm] using
        (evalB_condLt (evalB_var (by omega : σ.vars "row.first" < B))
          (evalB_var (by omega : σ.vars "row.m" < B)))
    refine ⟨τ, (Run.ite_false hb hr).mono (by simp only [Cond.size, Expr.size]; omega), ?_, hτn⟩
    simpa only [EllipsoidSearch.selectedNormal, hf] using hτ
  | some i =>
    simp only [hf, Option.map_some, Option.getD_some] at hσfirst
    have hib : i.val < B := i.isLt.trans hmB
    have hrow : ∀ j, Height (A i j : ℚ) H := by
      intro j
      simpa [Height] using And.intro (hA i j) hH
    have hc := copySelectedRow_spec B m n H a (fun i j => (A i j : ℚ)) i h1 hdims hHB hrow ha
    have he := ensureNormal_spec B n H (fun j => (A i j : ℚ)) hn hnB h1 hHB hrow
    have hrowzero : (fun j => (A i j : ℚ)) = (0 : Fin n → ℚ) ↔ A i = 0 := by
      simp only [funext_iff, Pi.zero_apply]
      constructor
      · intro h j
        exact_mod_cast h j
      · intro h j
        exact_mod_cast h j
    run_vcg [hc, he, hfall]
    all_goals clear hc he hfall
    all_goals simp_all [EllipsoidSearch.selectedNormal, RationalSeparation.rationalRow, Extents, hrowzero]
    all_goals aesop


end Lax109476Proofs.RamNormalSelection

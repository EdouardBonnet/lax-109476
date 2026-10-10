import Lax109476Proofs.RamScaleCoordinate

namespace Lax109476Proofs.RamScaleArray

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamScaleCoordinate RamRationalArrays RamRational RamCenterUpdate RamCopy RationalArithmeticBounds

def scaled {n : ℕ} (v : Fin n → ℚ) (D : ℕ) : Fin n → ℚ := fun i => v i * (D : ℚ)

def Invariant {n : ℕ} (a b : String) (v : Fin n → ℚ) (D : ℕ) (σ : Env) : Prop :=
  Represents a (List.ofFn v) σ ∧ Represents b (filled (scaled v D) (σ.vars "scale.i")) σ ∧
    σ.vars "scale.i" ≤ n ∧ σ.vars "vec.n" = n ∧ σ.vars "scale.factor" = D

theorem coordinate_wvars (a b : String) :
    (scaleCoordinate a b).wvars = (scaleCoordinate "" "").wvars := by rfl

def scaleStep (a b : String) : Com := .seq (scaleCoordinate a b)
  (.assign "scale.i" (.add (.var "scale.i") (.lit 1)))

theorem scaleStep_spec (B M n D : ℕ) (a b : String) (v : Fin n → ℚ)
    (hM : 1 ≤ M) (hnB : n < B) (hB : 2 * M ^ 2 + 3 < B)
    (hv : ∀ i, Height (v i) M) (hD : D ≤ M) (hab : RamCopy.Disjoint a b) :
    Spec B (fun σ => Invariant a b v D σ ∧ σ.vars "scale.i" < n) (scaleStep a b)
      (fun σ τ => Invariant a b v D τ ∧ τ.vars "scale.i" = σ.vars "scale.i" + 1)
      (72 * M.size + 98) := by
  rintro σ ⟨⟨hσa, hσb, hσiN, hσn, hσD⟩, hσi⟩
  let i : Fin n := ⟨σ.vars "scale.i", hσi⟩
  have hvi : Height (List.ofFn v)[i.val] M := by simpa using hv i
  obtain ⟨τ, hr₁, hτb, hτa⟩ := scaleCoordinate_spec B M i.val D a b (List.ofFn v)
    (filled (scaled v D) i.val) (by simp) (by simp [filled]) (i.isLt.trans hnB) hM hB
      hvi hD hab σ ⟨hσa, hσb, rfl, hσD⟩
  have hτi : τ.vars "scale.i" = i.val := hr₁.frame_var _ (by rw [coordinate_wvars]; decide)
  have hτn : τ.vars "vec.n" = n :=
    (hr₁.frame_var _ (by rw [coordinate_wvars]; decide)).trans hσn
  have hτD : τ.vars "scale.factor" = D :=
    (hr₁.frame_var _ (by rw [coordinate_wvars]; decide)).trans hσD
  have h1 : 1 < B := by nlinarith
  have he : (Expr.add (.var "scale.i") (.lit 1)).evalB B τ = some (i.val + 1) := by
    simpa only [hτi, Bop.apply_add] using evalB_bin
      (evalB_var (B := B) (σ := τ) (x := "scale.i") (by rw [hτi]; exact i.isLt.trans hnB))
      (evalB_lit h1)
      (show Bop.add.apply (τ.vars "scale.i") 1 < B by rw [hτi]; simp only [Bop.apply_add]; omega)
  have hr₂ := Run.assign (x := "scale.i") he
  have hnext : Represents b (filled (scaled v D) (i.val + 1)) τ := by
    rw [← filled_step]
    simpa only [List.getElem_ofFn, Fin.eta, scaled] using hτb
  refine ⟨_, (hr₁.seq hr₂).mono (by simp only [Expr.size]; omega), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Represents, arrs_setVar] using hτa
  · simpa only [Represents, arrs_setVar, vars_setVar, ite_true] using hnext
  · change i.val + 1 ≤ n; exact i.isLt
  · simpa [Env.setVar] using hτn
  · simpa [Env.setVar] using hτD
  · simp [i]

def scaleLoop (a b : String) : Com := .seq (.assign "scale.i" (.lit 0))
  (.while (.lt (.var "scale.i") (.var "vec.n")) (scaleStep a b))

theorem scaleLoop_spec (B M n D : ℕ) (a b : String) (v : Fin n → ℚ)
    (hM : 1 ≤ M) (hnB : n < B) (hB : 2 * M ^ 2 + 3 < B)
    (hv : ∀ i, Height (v i) M) (hD : D ≤ M) (hab : RamCopy.Disjoint a b) :
    Spec B (fun σ => Represents a (List.ofFn v) σ ∧ Represents b (List.replicate n 0) σ ∧
        σ.vars "vec.n" = n ∧ σ.vars "scale.factor" = D)
      (scaleLoop a b)
      (fun _ τ => Represents b (List.ofFn (scaled v D)) τ ∧ Represents a (List.ofFn v) τ ∧
        τ.vars "vec.n" = n ∧ τ.vars "scale.factor" = D)
      ((72 * M.size + 102) * n + 6) := by
  have hlo := Spec.forRangeZero "scale.i" "vec.n" (Invariant a b v D) n (72 * M.size + 98) hnB
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2.1)
    (scaleStep_spec B M n D a b v hM hnB hB hv hD hab)
  refine ((hlo.pre ?_).post ?_).mono (by simp only [Nat.add_assoc, Nat.reduceAdd]; omega)
  · rintro σ ⟨hσa, hσb, hσn, hσD⟩
    clear hlo
    simp_all [Invariant, filled_zero, Represents, Env.setVar]
  · rintro σ τ _ ⟨hτ, hcounter⟩
    exact ⟨by simpa only [hcounter, filled_done] using hτ.2.1,
      hτ.1, hτ.2.2.2.1, hτ.2.2.2.2⟩

def scaleArray (a b : String) : Com := .seq (RamZeroArray.zeroRationalArray b) (scaleLoop a b)

theorem scaleArray_spec (B M n D : ℕ) (a b : String) (v : Fin n → ℚ)
    (hM : 1 ≤ M) (hnB : n < B) (hB : 2 * M ^ 2 + 3 < B)
    (hv : ∀ i, Height (v i) M) (hD : D ≤ M) (hab : RamCopy.Disjoint a b) :
    Spec B (fun σ => Represents a (List.ofFn v) σ ∧
        (σ.arrs (b ++ ".s")).length = n ∧ (σ.arrs (b ++ ".n")).length = n ∧
        (σ.arrs (b ++ ".d")).length = n ∧ σ.vars "vec.n" = n ∧ σ.vars "scale.factor" = D)
      (scaleArray a b)
      (fun _ τ => Represents b (List.ofFn (scaled v D)) τ ∧ Represents a (List.ofFn v) τ ∧
        τ.vars "vec.n" = n ∧ τ.vars "scale.factor" = D)
      ((72 * M.size + 135) * n + 24) := by
  rintro σ ⟨hσa, hσs, hσnum, hσd, hσn, hσD⟩
  obtain ⟨τ, hr₁, hτb, hτn, harr⟩ := RamZeroArray.zeroRationalArray_spec B n b hnB (by nlinarith)
    σ ⟨hσs, hσnum, hσd, hσn⟩
  have hτa : Represents a (List.ofFn v) τ := by
    simpa only [Represents, harr (a ++ ".s") (disjoint_not_mem a b ".s" hab (by simp [suffixes])),
      harr (a ++ ".n") (disjoint_not_mem a b ".n" hab (by simp [suffixes])),
      harr (a ++ ".d") (disjoint_not_mem a b ".d" hab (by simp [suffixes]))] using hσa
  have hτD : τ.vars "scale.factor" = D := (hr₁.frame_var _ (by simp [RamZeroArray.zeroRationalArray,
    RamZeroArray.fillConstant, Lib.Fill.put, Com.wvars])).trans hσD
  obtain ⟨υ, hr₂, hυ⟩ := scaleLoop_spec B M n D a b v hM hnB hB hv hD hab τ ⟨hτa, hτb, hτn, hτD⟩
  exact ⟨υ, (hr₁.seq hr₂).mono (by simp only [Nat.add_mul]; omega), hυ⟩

end Lax109476Proofs.RamScaleArray

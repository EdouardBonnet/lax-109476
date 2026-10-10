import Lax109476Proofs.RamEllipsoidScalars
import Lax109476Proofs.RamFractionInterface

namespace Lax109476Proofs.RamEllipsoidCoefficients

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamEllipsoidScalars RamEllipsoidForm
open RationalArithmeticBounds

def scalarFields : List String :=
  ["vec.n", "grid.D", "ell.form.s", "ell.form.n", "ell.form.d", "ell.epsden"]

def storeCoefficient (i : ℕ) : Com :=
  .seq (.assign "vec.i" (.lit i)) (storeReduced "ell.coeff")

theorem storeCoefficient_spec (B i : ℕ) (gs : List ℚ) (q : ℚ)
    (hi : i < gs.length) (hiB : i < B) (h1 : 1 < B)
    (hn : q.num.natAbs < B) (hd : q.den < B) :
    Spec B (fun σ => Represents "ell.coeff" gs σ ∧ FractionOutput q σ) (storeCoefficient i)
      (fun _ τ => Represents "ell.coeff" (gs.set i q) τ) 15 := by
  rintro σ ⟨hσg, hσq⟩
  have hr₁ : Run B (.assign "vec.i" (.lit i)) σ (σ.setVar "vec.i" i) 2 :=
    Run.assign (evalB_lit hiB)
  obtain ⟨τ, hr₂, hτ⟩ := storeReduced_spec B "ell.coeff" gs q i hi h1 hiB hn hd
    (σ.setVar "vec.i" i) ⟨by simpa [Represents] using hσg, by simp,
      by simpa [FractionOutput] using hσq⟩
  exact ⟨τ, hr₁.seq hr₂, hτ⟩

theorem scalar_frames (c : Com)
    (hc : c ∈ [alphaFraction, betaFraction, gammaFraction, inflationFraction, diagonalFraction]) :
    (∀ x ∈ scalarFields, x ∉ c.wvars) ∧ c.warrs = [] := by
  simp at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals constructor
  all_goals try (intro x hx; simp [scalarFields] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals simp [alphaFraction, betaFraction, gammaFraction, scaledInverseFraction, inflationFraction,
    diagonalFraction, RamRounding.upperRootFraction, RamSquareRoot.squareRoot, RamSquareRoot.sqrtLoop,
    RamSquareRoot.sqrtStep, RamArithmetic.normalizeFraction, RamArithmetic.gcdLoop,
    RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.wvars, Com.warrs]

def computeAndStore (c : Com) (i : ℕ) : Com := .seq c (storeCoefficient i)

theorem computeAndStore_spec {B K : ℕ} {P : Env → Prop} (c : Com) (i : ℕ) (gs : List ℚ) (q : ℚ)
    (hc : c ∈ [alphaFraction, betaFraction, gammaFraction, inflationFraction, diagonalFraction])
    (hprod : Spec B P c (fun _ τ => FractionOutput q τ) K)
    (hi : i < gs.length) (hiB : i < B) (h1 : 1 < B)
    (hn : q.num.natAbs < B) (hd : q.den < B) :
    Spec B (fun σ => P σ ∧ Represents "ell.coeff" gs σ) (computeAndStore c i)
      (fun σ τ => Represents "ell.coeff" (gs.set i q) τ ∧ FieldsAgree scalarFields σ τ ∧
        ∀ a ∉ ["ell.coeff.s", "ell.coeff.n", "ell.coeff.d"], τ.arrs a = σ.arrs a)
      (K + 15) := by
  have hproducer := spec_with_fields scalarFields hprod (scalar_frames c hc).1 (scalar_frames c hc).2
  have hstore := spec_with_write_frame scalarFields
    (storeCoefficient_spec B i gs q hi hiB h1 hn hd)
    (by
      intro x hx
      simp [scalarFields] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [storeCoefficient, storeReduced, Com.wvars])
  rintro σ ⟨hσP, hσg⟩
  run_vcg [hproducer, hstore]
  all_goals clear hproducer hstore hprod
  all_goals simp_all [Represents, FieldsAgree, scalarFields, storeCoefficient, storeReduced, Com.warrs]

def coefficients (n : ℕ) (q : ℚ) (D E : ℕ) : List ℚ :=
  [(n : ℚ) ^ 2 / ((n : ℚ) ^ 2 - 1), 2 / (((n : ℚ) + 1) * q),
    1 / (((n : ℚ) + 1) * RationalRounding.sqrtUpper q D),
    (1 + 1 / (E : ℚ)) ^ 2, (n : ℚ) / D]

def computeCoefficients : Com :=
  .seq (computeAndStore alphaFraction 0)
    (.seq (computeAndStore betaFraction 1)
      (.seq (computeAndStore gammaFraction 2)
        (.seq (computeAndStore inflationFraction 3) (computeAndStore diagonalFraction 4))))



def ScalarInput (n : ℕ) (q : ℚ) (D E : ℕ) (σ : Env) : Prop :=
  FormOutput q σ ∧ σ.vars "vec.n" = n ∧ σ.vars "grid.D" = D ∧ σ.vars "ell.epsden" = E

theorem scalarInput_frame (n : ℕ) (q : ℚ) (D E : ℕ) (σ τ : Env)
    (hσ : ScalarInput n q D E σ) (hf : FieldsAgree scalarFields σ τ) : ScalarInput n q D E τ := by
  simpa only [ScalarInput, FormOutput, hf "vec.n" (by simp [scalarFields]),
    hf "grid.D" (by simp [scalarFields]), hf "ell.epsden" (by simp [scalarFields]),
    hf "ell.form.s" (by simp [scalarFields]), hf "ell.form.n" (by simp [scalarFields]),
    hf "ell.form.d" (by simp [scalarFields])] using hσ

theorem computeAndStore_input_spec {B K : ℕ} {P : Env → Prop} (c : Com) (i n D E : ℕ)
    (gs : List ℚ) (q v : ℚ)
    (hc : c ∈ [alphaFraction, betaFraction, gammaFraction, inflationFraction, diagonalFraction])
    (hprod : Spec B P c (fun _ τ => FractionOutput v τ) K)
    (hP : ∀ σ, ScalarInput n q D E σ → P σ)
    (hi : i < gs.length) (hiB : i < B) (h1 : 1 < B)
    (hn : v.num.natAbs < B) (hd : v.den < B) :
    Spec B (fun σ => ScalarInput n q D E σ ∧ Represents "ell.coeff" gs σ) (computeAndStore c i)
      (fun _ τ => ScalarInput n q D E τ ∧ Represents "ell.coeff" (gs.set i v) τ) (K + 15) := by
  intro σ hσ
  obtain ⟨τ, hr, hτg, hf, _⟩ := computeAndStore_spec c i gs v hc hprod hi hiB h1 hn hd
    σ ⟨hP σ hσ.1, hσ.2⟩
  exact ⟨τ, hr, scalarInput_frame n q D E σ τ hσ.1 hf, hτg⟩

set_option maxHeartbeats 800000 in
theorem computeCoefficients_spec (B n M C D E : ℕ) (q : ℚ) (hn : 2 ≤ n)
    (hqpos : 0 < q) (hq : Height q M) (hnM : n ≤ M) (hDM : D ≤ M) (hEM : E ≤ M)
    (hDpos : 0 < D) (hEpos : 0 < E) (hnnB : n ^ 2 < B) (hInflB : (E + 1) ^ 2 < B)
    (hPrimB : 2 * M ^ 2 + 3 < B)
    (hRootB : (2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3 < B)
    (hCB : C < B) (hcoeff : ∀ v ∈ coefficients n q D E, Height v C) :
    Spec B (fun σ => ScalarInput n q D E σ ∧ Represents "ell.coeff" (List.replicate 5 0) σ)
      computeCoefficients
      (fun _ τ => Represents "ell.coeff" (coefficients n q D E) τ ∧ ScalarInput n q D E τ)
      (582 * M.size + 687) := by
  have h1 : 1 < B := by nlinarith only [hn, hnnB]
  have h4 : 4 < B := by nlinarith only [hn, hnnB]
  have hMB : M < B := by nlinarith only [hPrimB]
  have hnsize := Nat.size_le_size hnM
  have hDsize := Nat.size_le_size hDM
  have hEsize := Nat.size_le_size hEM
  have hα := hcoeff ((n : ℚ) ^ 2 / ((n : ℚ) ^ 2 - 1)) (by simp [coefficients])
  have hβ := hcoeff (2 / (((n : ℚ) + 1) * q)) (by simp [coefficients])
  have hγ := hcoeff (1 / (((n : ℚ) + 1) * RationalRounding.sqrtUpper q D)) (by simp [coefficients])
  have hρ := hcoeff ((1 + 1 / (E : ℚ)) ^ 2) (by simp [coefficients])
  have hδ := hcoeff ((n : ℚ) / D) (by simp [coefficients])
  have hαprod := (alphaFraction_spec B n hn hnnB).mono
    (show 36 * (n ^ 2 - 1).size + 26 ≤ 72 * M.size + 62 from
      (alphaFraction_cost n).trans (by omega))
  have hβprod := (betaFraction_spec B n M q hqpos hq hnM hPrimB).mono
    (betaFraction_cost n M q hnM hq)
  have hγprod := (gammaFraction_spec B n M D q hq hnM hDM hDpos hRootB).mono (gammaFraction_cost M)
  have hρprod := (inflationFraction_spec B E hEpos hInflB).mono
    (show 36 * (E ^ 2).size + 30 ≤ 72 * M.size + 66 from
      (inflationFraction_cost E).trans (by omega))
  have hδprod := (diagonalFraction_spec B n D (hnM.trans_lt hMB) (hDM.trans_lt hMB) hDpos).mono
    (show 36 * D.size + 22 ≤ 36 * M.size + 22 by omega)
  have hαstore := computeAndStore_input_spec alphaFraction 0 n D E (List.replicate 5 0) q _ (by simp) hαprod
    (fun _ h => h.2.1) (by simp) (by omega) h1 (hα.1.trans_lt hCB) (hα.2.trans_lt hCB)
  have hβstore := computeAndStore_input_spec betaFraction 1 n D E
    [(n : ℚ) ^ 2 / ((n : ℚ) ^ 2 - 1), 0, 0, 0, 0] q _ (by simp) hβprod
    (fun _ h => ⟨h.1, h.2.1⟩) (by simp) (by omega) h1 (hβ.1.trans_lt hCB) (hβ.2.trans_lt hCB)
  have hγstore := computeAndStore_input_spec gammaFraction 2 n D E
    [(n : ℚ) ^ 2 / ((n : ℚ) ^ 2 - 1), 2 / (((n : ℚ) + 1) * q), 0, 0, 0] q _ (by simp) hγprod
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩) (by simp) (by omega) h1 (hγ.1.trans_lt hCB) (hγ.2.trans_lt hCB)
  have hρstore := computeAndStore_input_spec inflationFraction 3 n D E
    [(n : ℚ) ^ 2 / ((n : ℚ) ^ 2 - 1), 2 / (((n : ℚ) + 1) * q),
      1 / (((n : ℚ) + 1) * RationalRounding.sqrtUpper q D), 0, 0] q _ (by simp) hρprod
    (fun _ h => h.2.2.2) (by simp) (by omega) h1 (hρ.1.trans_lt hCB) (hρ.2.trans_lt hCB)
  have hδstore := computeAndStore_input_spec diagonalFraction 4 n D E
    [(n : ℚ) ^ 2 / ((n : ℚ) ^ 2 - 1), 2 / (((n : ℚ) + 1) * q),
      1 / (((n : ℚ) + 1) * RationalRounding.sqrtUpper q D), (1 + 1 / (E : ℚ)) ^ 2, 0] q _ (by simp) hδprod
    (fun _ h => ⟨h.2.1, h.2.2.1⟩) (by simp) (by omega) h1 (hδ.1.trans_lt hCB) (hδ.2.trans_lt hCB)
  rintro σ ⟨hσinput, hσg⟩
  run_vcg [hαstore, hβstore, hγstore, hρstore, hδstore]
  all_goals clear hαstore hβstore hγstore hρstore hδstore hαprod hβprod hγprod hρprod hδprod
  all_goals simp_all [coefficients, List.replicate_succ, List.replicate_zero]



def coefficientCap (M : ℕ) : ℕ := 4 * (M + 1) ^ 4

theorem coefficients_height (n M D E : ℕ) (q : ℚ) (hq : Height q M)
    (hnM : n ≤ M) (hDM : D ≤ M) (hEM : E ≤ M) (hDpos : 0 < D) :
    ∀ v ∈ coefficients n q D E, Height v (coefficientCap M) := by
  have hM : 1 ≤ M := le_trans q.den_pos hq.2
  have hn := height_nat n M hnM hM
  have hD := height_nat D M hDM hM
  have hE := height_nat E M hEM hM
  have hone : Height (1 : ℚ) 1 := by simp [Height]
  have htwo : Height (2 : ℚ) 2 := by simp [Height]
  have hnp : Height ((n : ℚ) + 1) (M + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using height_nat (n + 1) (M + 1) (by omega) (by omega)
  have hpow := height_pow _ M 2 hn
  have hsub := height_sub _ _ (M ^ 2) 1 hpow hone
  have hα := height_div _ _ (M ^ 2) (2 * M ^ 2 * 1) hpow hsub
  have hβ := height_div _ _ 2 ((M + 1) * M) htwo (height_mul _ _ (M + 1) M hnp hq)
  have hroot : Height (RationalRounding.sqrtUpper q D) (M ^ 3 + 1) := by
    apply height_mono _ (EllipsoidArithmeticBounds.height_sqrtUpper q M D hq hDpos)
    calc
      M * D ^ 2 + 1 ≤ M * M ^ 2 + 1 := Nat.add_le_add_right
        (Nat.mul_le_mul_left M (Nat.pow_le_pow_left hDM 2)) 1
      _ = M ^ 3 + 1 := by ring
  have hγ := height_div _ _ 1 ((M + 1) * (M ^ 3 + 1)) hone
    (height_mul _ _ (M + 1) (M ^ 3 + 1) hnp hroot)
  have hρ := height_pow _ (2 * M) 2
    (by simpa using height_add _ _ 1 M hone (by simpa only [one_mul] using height_div _ _ 1 M hone hE))
  have hδ := height_div _ _ M M hn hD
  have hp1 := Nat.pow_le_pow_right (by omega : 1 ≤ M + 1) (by decide : (1 : ℕ) ≤ 4)
  have hp2 := Nat.pow_le_pow_right (by omega : 1 ≤ M + 1) (by decide : (2 : ℕ) ≤ 4)
  have hp4 := Nat.pow_le_pow_left (by omega : M ≤ M + 1) 4
  have hrootpow : M ^ 3 + 1 ≤ (M + 1) ^ 3 := by nlinarith only [hM]
  have hγbound : 1 * ((M + 1) * (M ^ 3 + 1)) ≤ coefficientCap M := by
    calc
      1 * ((M + 1) * (M ^ 3 + 1)) ≤ (M + 1) * (M + 1) ^ 3 := by
        simpa using Nat.mul_le_mul_left (M + 1) hrootpow
      _ = (M + 1) ^ 4 := by ring
      _ ≤ coefficientCap M := by unfold coefficientCap; omega
  intro v hv
  simp only [coefficients, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · apply height_mono _ hα
    calc
      M ^ 2 * (2 * M ^ 2 * 1) = 2 * M ^ 4 := by ring
      _ ≤ coefficientCap M := by unfold coefficientCap; omega
  · apply height_mono _ hβ
    calc
      2 * ((M + 1) * M) ≤ 2 * (M + 1) ^ 2 := by nlinarith only [hM]
      _ ≤ coefficientCap M := by unfold coefficientCap; omega
  · exact height_mono _ hγ hγbound
  · apply height_mono _ hρ
    have hp := (Nat.pow_le_pow_left (by omega : M ≤ M + 1) 2).trans hp2
    calc
      (2 * M) ^ 2 = 4 * M ^ 2 := by ring
      _ ≤ coefficientCap M := by unfold coefficientCap; omega
  · apply height_mono _ hδ
    have hp := (Nat.pow_le_pow_left (by omega : M ≤ M + 1) 2).trans hp2
    calc
      M * M = M ^ 2 := by ring
      _ ≤ coefficientCap M := by unfold coefficientCap; omega

theorem computeCoefficients_bounded_spec (B n M D E : ℕ) (q : ℚ) (hn : 2 ≤ n)
    (hqpos : 0 < q) (hq : Height q M) (hnM : n ≤ M) (hDM : D ≤ M) (hEM : E ≤ M)
    (hDpos : 0 < D) (hEpos : 0 < E) (hnnB : n ^ 2 < B) (hInflB : (E + 1) ^ 2 < B)
    (hPrimB : 2 * M ^ 2 + 3 < B)
    (hRootB : (2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3 < B)
    (hCB : coefficientCap M < B) :
    Spec B (fun σ => ScalarInput n q D E σ ∧ Represents "ell.coeff" (List.replicate 5 0) σ)
      computeCoefficients
      (fun _ τ => Represents "ell.coeff" (coefficients n q D E) τ ∧ ScalarInput n q D E τ)
      (582 * M.size + 687) :=
  computeCoefficients_spec B n M (coefficientCap M) D E q hn hqpos hq hnM hDM hEM
    hDpos hEpos hnnB hInflB hPrimB hRootB hCB (coefficients_height n M D E q hq hnM hDM hEM hDpos)



def initializeCoefficients : Com :=
  .seq (.assign "coeff.savedn" (.var "vec.n"))
    (.seq (.assign "vec.n" (.lit 5))
      (.seq (RamZeroArray.zeroRationalArray "ell.coeff") (.assign "vec.n" (.var "coeff.savedn"))))

theorem initializeCoefficients_spec (B n : ℕ) (hnB : n < B) (h5B : 5 < B) :
    Spec B (fun σ => (σ.arrs "ell.coeff.s").length = 5 ∧ (σ.arrs "ell.coeff.n").length = 5 ∧
        (σ.arrs "ell.coeff.d").length = 5 ∧ σ.vars "vec.n" = n)
      initializeCoefficients
      (fun σ τ => Represents "ell.coeff" (List.replicate 5 0) τ ∧ FieldsAgree scalarFields σ τ ∧
        ∀ a ∉ ["ell.coeff.s", "ell.coeff.n", "ell.coeff.d"], τ.arrs a = σ.arrs a) 189 := by
  have hzero := spec_with_write_frame ("coeff.savedn" :: scalarFields)
    (RamZeroArray.zeroRationalArray_spec B 5 "ell.coeff" h5B (by omega))
    (by
      intro x hx
      simp [scalarFields] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [RamZeroArray.zeroRationalArray, RamZeroArray.fillConstant, Lib.Fill.put, Com.wvars])
  rintro σ ⟨hσs, hσnum, hσd, hσn⟩
  run_vcg [hzero]
  all_goals clear hzero
  all_goals simp_all [Represents, FieldsAgree, scalarFields]

def prepareCoefficients : Com := .seq initializeCoefficients computeCoefficients

theorem prepareCoefficients_spec (B n M D E : ℕ) (q : ℚ) (hn : 2 ≤ n)
    (hqpos : 0 < q) (hq : Height q M) (hnM : n ≤ M) (hDM : D ≤ M) (hEM : E ≤ M)
    (hDpos : 0 < D) (hEpos : 0 < E) (hnnB : n ^ 2 < B) (hInflB : (E + 1) ^ 2 < B)
    (hPrimB : 2 * M ^ 2 + 3 < B)
    (hRootB : (2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3 < B)
    (hCB : coefficientCap M < B) (h5B : 5 < B) :
    Spec B (fun σ => ScalarInput n q D E σ ∧ (σ.arrs "ell.coeff.s").length = 5 ∧
        (σ.arrs "ell.coeff.n").length = 5 ∧ (σ.arrs "ell.coeff.d").length = 5)
      prepareCoefficients
      (fun _ τ => Represents "ell.coeff" (coefficients n q D E) τ ∧ ScalarInput n q D E τ)
      (582 * M.size + 876) := by
  have hMB : M < B := by nlinarith only [hPrimB]
  rintro σ ⟨hσinput, hσs, hσnum, hσd⟩
  obtain ⟨τ, hr₁, hτg, hf, _⟩ := initializeCoefficients_spec B n (hnM.trans_lt hMB) h5B
    σ ⟨hσs, hσnum, hσd, hσinput.2.1⟩
  have hτinput := scalarInput_frame n q D E σ τ hσinput hf
  obtain ⟨υ, hr₂, hυ⟩ := computeCoefficients_bounded_spec B n M D E q hn hqpos hq hnM hDM hEM
    hDpos hEpos hnnB hInflB hPrimB hRootB hCB τ ⟨hτinput, hτg⟩
  exact ⟨υ, (hr₁.seq hr₂).mono (by omega), hυ⟩

end Lax109476Proofs.RamEllipsoidCoefficients

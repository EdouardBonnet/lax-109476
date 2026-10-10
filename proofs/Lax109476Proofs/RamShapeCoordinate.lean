import Lax109476Proofs.RamCenterCoordinate
import Lax109476Proofs.RamMatrixStorage

namespace Lax109476Proofs.RamShapeCoordinate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface RamFrame RationalArithmeticBounds

def addDiagonal : Com :=
  .ite (.eq (.var "entry.i") (.var "entry.j"))
    (.seq resultToLeft (.seq (.assign "vec.i" (.lit 4))
      (.seq (loadRight "ell.coeff") addFraction))) .skip

def entryIndex : Com :=
  .seq (.assign "entry.i" (.div (.var "entry.k") (.var "vec.n")))
    (.assign "entry.j" (.sub (.var "entry.k") (.mul (.var "entry.i") (.var "vec.n"))))

def entryProduct : Com :=
  .seq entryIndex (.seq (.assign "vec.i" (.var "entry.i")) (.seq (loadLeft "ell.u") (.seq (.assign "vec.i" (.var "entry.j")) (.seq (loadRight "ell.u") (multiplyFraction)))))

def shapeDifference : Com :=
  .seq resultToRight (.seq (.assign "vec.i" (.lit 1)) (.seq (loadLeft "ell.coeff") (.seq multiplyFraction (.seq resultToRight (.seq (.assign "vec.i" (.var "entry.k")) (.seq (loadLeft "ell.shape") (subtractFraction)))))))

def roundedEntry : Com :=
  .seq resultToRight (.seq (.assign "vec.i" (.lit 0)) (.seq (loadLeft "ell.coeff") (.seq multiplyFraction (.seq resultToLeft (RamRounding.roundFraction)))))

def inflatedEntry : Com :=
  .seq addDiagonal (.seq resultToRight (.seq (.assign "vec.i" (.lit 3)) (.seq (loadLeft "ell.coeff") (.seq multiplyFraction (.seq (.assign "vec.i" (.var "entry.k")) ((storeReduced "ell.nextshape")))))))

/-- One rounded shape entry, using the stored vector and step coefficients. -/
def shapeCoordinate : Com :=
  .seq entryProduct (.seq shapeDifference (.seq roundedEntry inflatedEntry))

def shapeCap (M : ℕ) : ℕ := 8 * (M + 1) ^ 8

theorem shapeCap_pow (M k : ℕ) (hk : k ≤ 8) : M ^ k ≤ (M + 1) ^ 8 :=
  (Nat.pow_le_pow_left (by omega : M ≤ M + 1) k).trans
    (Nat.pow_le_pow_right (by omega : 1 ≤ M + 1) hk)

theorem shapeCap_bounds (M : ℕ) :
    M ≤ shapeCap M ∧ M ^ 2 ≤ shapeCap M ∧ M ^ 3 ≤ shapeCap M ∧
      2 * M ^ 4 ≤ shapeCap M ∧ 2 * M ^ 5 ≤ shapeCap M ∧
      2 * M ^ 6 + 1 ≤ shapeCap M ∧ 6 * M ^ 7 ≤ shapeCap M ∧ 6 * M ^ 8 ≤ shapeCap M := by
  have hp1 := shapeCap_pow M 1 (by omega)
  have hp2 := shapeCap_pow M 2 (by omega)
  have hp3 := shapeCap_pow M 3 (by omega)
  have hp4 := shapeCap_pow M 4 (by omega)
  have hp5 := shapeCap_pow M 5 (by omega)
  have hp6 := shapeCap_pow M 6 (by omega)
  have hp7 := shapeCap_pow M 7 (by omega)
  have hp8 := shapeCap_pow M 8 (by omega)
  have hbase : 1 ≤ (M + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
  simp only [pow_one] at hp1
  unfold shapeCap
  exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
    by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

def loopFields : List String := ["entry.k", "entry.i", "entry.j", "vec.n", "grid.D"]



theorem arithmetic_frames (c : Com)
    (hc : c ∈ [multiplyFraction, subtractFraction, addFraction, resultToRight,
      resultToLeft, RamRounding.roundFraction]) :
    (∀ x ∈ loopFields, x ∉ c.wvars) ∧ c.warrs = [] := by
  simp at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor
  all_goals try (intro x hx; simp [loopFields] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl)
  all_goals simp [multiplyFraction, subtractFraction, negateRight, resultToRight, resultToLeft,
    RamRounding.roundFraction, addFraction, RamArithmetic.normalizeFraction, RamArithmetic.gcdLoop,
    RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.wvars, Com.warrs]

theorem framed_arithmetic {B K : ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {c : Com}
    (hc : c ∈ [multiplyFraction, subtractFraction, addFraction, resultToRight,
      resultToLeft, RamRounding.roundFraction]) (h : Spec B P c Q K) :
    Spec B P c (fun σ τ => Q σ τ ∧ FieldsAgree loopFields σ τ ∧ τ.arrs = σ.arrs) K :=
  spec_with_fields loopFields h (arithmetic_frames c hc).1 (arithmetic_frames c hc).2

theorem framed_loadLeft (B M : ℕ) (a : String) (xs : List ℚ) (i : ℕ)
    (hi : i < xs.length) (h1 : 1 < B) (hiB : i < B) (hmB : M < B) (hq : Height xs[i] M) :
    Spec B (fun σ => Represents a xs σ ∧ σ.vars "vec.i" = i) (loadLeft a)
      (fun σ τ => LeftValue xs[i] τ ∧
        FieldsAgree (loopFields ++ ["right.s", "right.n", "right.d"]) σ τ ∧ τ.arrs = σ.arrs) 9 :=
  spec_with_fields _
    ((loadLeft_spec B a xs i hi h1 hiB (hq.1.trans_lt hmB) (hq.2.trans_lt hmB)).post
      (fun _ τ _ h => leftValue_of_output _ τ h))
    (by
      intro x hx
      simp [loopFields] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [loadLeft, Com.wvars])
    (by simp [loadLeft, Com.warrs])

theorem framed_loadRight (B M : ℕ) (a : String) (xs : List ℚ) (i : ℕ)
    (hi : i < xs.length) (h1 : 1 < B) (hiB : i < B) (hmB : M < B) (hq : Height xs[i] M) :
    Spec B (fun σ => Represents a xs σ ∧ σ.vars "vec.i" = i) (loadRight a)
      (fun σ τ => RightValue xs[i] τ ∧
        FieldsAgree (loopFields ++ ["left.s", "left.n", "left.d"]) σ τ ∧ τ.arrs = σ.arrs) 9 :=
  spec_with_fields _
    ((loadRight_spec B a xs i hi h1 hiB (hq.1.trans_lt hmB) (hq.2.trans_lt hmB)).post
      (fun _ τ _ h => rightValue_of_output _ τ h))
    (by
      intro x hx
      simp [loopFields] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [loadRight, Com.wvars])
    (by simp [loadRight, Com.warrs])

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem addDiagonal_spec (B S i j : ℕ) (q : ℚ) (gs : List ℚ)
    (hig : 4 < gs.length) (hiB : i < B) (hjB : j < B) (hB : 2 * S ^ 2 + 3 < B)
    (hq : Height q S) (hg : Height gs[4] S) :
    Spec B (fun σ => FractionOutput q σ ∧ Represents "ell.coeff" gs σ ∧
        σ.vars "entry.i" = i ∧ σ.vars "entry.j" = j)
      addDiagonal
      (fun _ τ => FractionOutput (q + if i = j then gs[4] else 0) τ)
      (72 * S.size + 117) := by
  have hSB : S < B := by nlinarith
  have h1 : 1 < B := by nlinarith
  have hSpos : 1 ≤ S := le_trans q.den_pos hq.2
  have h4 : 4 < B := by nlinarith
  have hleft := framed_arithmetic (by simp)
    (resultToLeft_spec B q h1 (hq.1.trans_lt hSB) (hq.2.trans_lt hSB))
  have hload : Spec B (fun σ => Represents "ell.coeff" gs σ ∧ σ.vars "vec.i" = 4 ∧ LeftValue q σ)
      (loadRight "ell.coeff") (fun σ τ => RightValue gs[4] τ ∧ LeftValue q τ ∧ τ.arrs = σ.arrs) 9 := by
    rintro σ ⟨hσg, hσidx, hσq⟩
    obtain ⟨τ, hr, hτg, hfields, harrs⟩ :=
      framed_loadRight B S "ell.coeff" gs 4 hig h1 h4 hSB hg σ ⟨hσg, hσidx⟩
    refine ⟨τ, hr, hτg, ?_, harrs⟩
    simpa only [LeftValue, hfields "left.s" (by simp), hfields "left.n" (by simp),
      hfields "left.d" (by simp)] using hσq
  have hadd := framed_arithmetic (by simp) (add_spec B S q gs[4] hB hq hg)
  rintro σ ⟨hσq, hσg, hσi, hσj⟩
  run_vcg [hleft, hload, hadd]
  all_goals clear hleft hload hadd
  all_goals simp_all [Represents, FieldsAgree, loopFields]
  all_goals aesop

theorem addDiagonal_frame (B S i j : ℕ) (q : ℚ) (gs : List ℚ)
    (hig : 4 < gs.length) (hiB : i < B) (hjB : j < B) (hB : 2 * S ^ 2 + 3 < B)
    (hq : Height q S) (hg : Height gs[4] S) :
    Spec B (fun σ => FractionOutput q σ ∧ Represents "ell.coeff" gs σ ∧
        σ.vars "entry.i" = i ∧ σ.vars "entry.j" = j)
      addDiagonal
      (fun σ τ => FractionOutput (q + if i = j then gs[4] else 0) τ ∧
        FieldsAgree loopFields σ τ ∧ τ.arrs = σ.arrs)
      (72 * S.size + 117) :=
  spec_with_fields loopFields (addDiagonal_spec B S i j q gs hig hiB hjB hB hq hg)
    (by
      intro x hx
      simp [loopFields] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      all_goals simp [addDiagonal, resultToLeft, loadRight, addFraction, RamArithmetic.normalizeFraction,
        RamArithmetic.gcdLoop, RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.wvars])
    (by simp [addDiagonal, resultToLeft, loadRight, addFraction, RamArithmetic.normalizeFraction,
      RamArithmetic.gcdLoop, RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.warrs])



theorem entryIndex_spec (B k n : ℕ) (hk : k < B) (hn : n < B) :
    Spec B (fun σ => σ.vars "entry.k" = k ∧ σ.vars "vec.n" = n) entryIndex
      (fun σ τ => τ.vars "entry.i" = k / n ∧ τ.vars "entry.j" = k % n ∧
        τ.vars "entry.k" = k ∧ τ.vars "vec.n" = n ∧
        τ.vars "grid.D" = σ.vars "grid.D" ∧ τ.arrs = σ.arrs) 10 := by
  have hdiv : k / n < B := (Nat.div_le_self k n).trans_lt hk
  have hmul : k / n * n < B := (Nat.div_mul_le_self k n).trans_lt hk
  have hsub : k - k / n * n < B := (Nat.sub_le k _).trans_lt hk
  rintro σ ⟨hσk, hσn⟩
  run_vcg
  all_goals simp_all [Nat.mod_def, Nat.mul_comm]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1200000 in
theorem shapeCoordinate_spec (B M D n k : ℕ) (us xs gs next : List ℚ)
    (hkn : k < n * n) (hnM : n * n ≤ M) (huLen : us.length = n)
    (hiu : k / n < us.length) (hju : k % n < us.length)
    (hix : k < xs.length) (hig : 4 < gs.length) (hin : k < next.length)
    (hM : 1 ≤ M) (hD : D ≤ M) (hDpos : 0 < D)
    (hu : Height us[k / n] M) (hv : Height us[k % n] M) (hx : Height xs[k] M)
    (hα : Height gs[0] M) (hβ : Height gs[1] M)
    (hρ : Height gs[3] M) (hδ : Height gs[4] M)
    (hB : 2 * (shapeCap M) ^ 2 + 3 < B) :
    Spec B (fun σ => Represents "ell.u" us σ ∧ Represents "ell.shape" xs σ ∧
        Represents "ell.coeff" gs σ ∧ Represents "ell.nextshape" next σ ∧
        σ.vars "entry.k" = k ∧ σ.vars "vec.n" = n ∧ σ.vars "grid.D" = D)
      shapeCoordinate
      (fun _ τ => Represents "ell.nextshape"
          (next.set k (gs[3] * (RationalRounding.roundDown
            (gs[0] * (xs[k] - gs[1] * (us[k / n] * us[k % n]))) D +
              if k / n = k % n then gs[4] else 0))) τ ∧
        Represents "ell.u" us τ ∧ Represents "ell.shape" xs τ ∧ Represents "ell.coeff" gs τ)
      (468 * (shapeCap M).size + 690) := by
  have hnpos : 0 < n := by
    by_contra h
    have hn : n = 0 := by omega
    simp [hn] at hkn
  have hcaps := shapeCap_bounds M
  have hSB : shapeCap M < B := by nlinarith only [hB]
  have hmB : M < B := hcaps.1.trans_lt hSB
  have hkB : k < B := hkn.trans_le hnM |>.trans hmB
  have hnB : n < B := (le_self_pow (by omega : 1 ≤ n) (by decide : (2 : ℕ) ≠ 0)).trans
    (by simpa [pow_two] using hnM) |>.trans_lt hmB
  have hiB : k / n < B := (Nat.div_le_self k n).trans_lt hkB
  have hjB : k % n < B := (Nat.mod_lt k hnpos).trans hnB
  have h1 : 1 < B := hM.trans_lt hmB
  have h4 : 4 < B := by have hp := Nat.one_le_pow 8 (M + 1) (by omega); unfold shapeCap at hSB; omega
  let q₁ := us[k / n] * us[k % n]
  let q₂ := gs[1] * q₁
  let q₃ := xs[k] - q₂
  let q₄ := gs[0] * q₃
  let q₅ := RationalRounding.roundDown q₄ D
  let q₆ := q₅ + if k / n = k % n then gs[4] else 0
  have hq₁ : Height q₁ (M ^ 2) := by simpa [q₁, pow_two] using height_mul _ _ M M hu hv
  have hq₂ : Height q₂ (M ^ 3) := by
    have h := height_mul _ _ M (M ^ 2) hβ hq₁
    convert h using 1 <;> ring
  have hq₃ : Height q₃ (2 * M ^ 4) := by
    have h := height_sub _ _ M (M ^ 3) hx hq₂
    convert h using 1 <;> ring
  have hq₄ : Height q₄ (2 * M ^ 5) := by
    have h := height_mul _ _ M (2 * M ^ 4) hα hq₃
    convert h using 1 <;> ring
  have hq₅ : Height q₅ (2 * M ^ 6 + 1) := by
    apply height_mono _ (EllipsoidArithmeticBounds.height_roundDown q₄ (2 * M ^ 5) D hq₄ hDpos)
    calc
      2 * M ^ 5 * D + 1 ≤ 2 * M ^ 5 * M + 1 := Nat.add_le_add_right (Nat.mul_le_mul_left _ hD) 1
      _ = 2 * M ^ 6 + 1 := by ring
  have hq₆ : Height q₆ (6 * M ^ 7) := by
    by_cases hij : k / n = k % n
    · have h := height_add _ _ (2 * M ^ 6 + 1) M hq₅ hδ
      simp only [q₆, if_pos hij]
      apply height_mono _ h
      have hp : M ≤ M ^ 7 := le_self_pow hM (by decide : (7 : ℕ) ≠ 0)
      calc
        2 * (2 * M ^ 6 + 1) * M = 4 * M ^ 7 + 2 * M := by ring
        _ ≤ 6 * M ^ 7 := by omega
    · simp only [q₆, if_neg hij, add_zero]
      apply height_mono _ hq₅
      have hp := Nat.pow_le_pow_right hM (by decide : (6 : ℕ) ≤ 7)
      have hp1 : 1 ≤ M ^ 7 := Nat.one_le_pow _ _ hM
      omega
  have hfinal : Height (gs[3] * q₆) (shapeCap M) := by
    have h := height_mul _ _ M (6 * M ^ 7) hρ hq₆
    apply height_mono _ h
    convert hcaps.2.2.2.2.2.2.2 using 1 <;> ring
  have huS := height_mono _ hu hcaps.1
  have hvS := height_mono _ hv hcaps.1
  have hxS := height_mono _ hx hcaps.1
  have hαS := height_mono _ hα hcaps.1
  have hβS := height_mono _ hβ hcaps.1
  have hρS := height_mono _ hρ hcaps.1
  have hδS := height_mono _ hδ hcaps.1
  have hq₁S := height_mono _ hq₁ hcaps.2.1
  have hq₂S := height_mono _ hq₂ hcaps.2.2.1
  have hq₃S := height_mono _ hq₃ hcaps.2.2.2.1
  have hq₄S := height_mono _ hq₄ hcaps.2.2.2.2.1
  have hq₅S := height_mono _ hq₅ hcaps.2.2.2.2.2.1
  have hq₆S := height_mono _ hq₆ hcaps.2.2.2.2.2.2.1
  have hindex := entryIndex_spec B k n hkB hnB
  have hloadU := framed_loadLeft B M "ell.u" us (k / n) hiu h1 hiB hmB hu
  have hloadV := framed_loadRight B M "ell.u" us (k % n) hju h1 hjB hmB hv
  have hmul₁ := framed_arithmetic (by simp) (multiply_spec B (shapeCap M) _ _ hB huS hvS)
  have hright₁ := framed_arithmetic (by simp) (resultToRight_spec B q₁ h1 (hq₁S.1.trans_lt hSB) (hq₁S.2.trans_lt hSB))
  have hloadβ := framed_loadLeft B M "ell.coeff" gs 1 (by omega) h1 h1 hmB hβ
  have hmul₂ := framed_arithmetic (by simp) (multiply_spec B (shapeCap M) _ _ hB hβS hq₁S)
  have hright₂ := framed_arithmetic (by simp) (resultToRight_spec B q₂ h1 (hq₂S.1.trans_lt hSB) (hq₂S.2.trans_lt hSB))
  have hloadX := framed_loadLeft B M "ell.shape" xs k hix h1 hkB hmB hx
  have hsub := framed_arithmetic (by simp) (subtract_spec B (shapeCap M) _ _ hB hxS hq₂S)
  have hright₃ := framed_arithmetic (by simp) (resultToRight_spec B q₃ h1 (hq₃S.1.trans_lt hSB) (hq₃S.2.trans_lt hSB))
  have hloadα := framed_loadLeft B M "ell.coeff" gs 0 (by omega) h1 (by omega) hmB hα
  have hmul₃ := framed_arithmetic (by simp) (multiply_spec B (shapeCap M) _ _ hB hαS hq₃S)
  have hleft := framed_arithmetic (by simp) (resultToLeft_spec B q₄ h1 (hq₄S.1.trans_lt hSB) (hq₄S.2.trans_lt hSB))
  have hround := framed_arithmetic (by simp) (round_spec B (shapeCap M) D q₄ hB hq₄S (hD.trans hcaps.1) hDpos)
  have hdiag := addDiagonal_frame B (shapeCap M) (k / n) (k % n) q₅ gs hig hiB hjB hB hq₅S hδS
  have hright₄ := framed_arithmetic (by simp) (resultToRight_spec B q₆ h1 (hq₆S.1.trans_lt hSB) (hq₆S.2.trans_lt hSB))
  have hloadρ := framed_loadLeft B M "ell.coeff" gs 3 (by omega) h1 (by omega) hmB hρ
  have hmul₄ := framed_arithmetic (by simp) (multiply_spec B (shapeCap M) _ _ hB hρS hq₆S)
  have hstore := spec_with_write_frame loopFields
    (storeReduced_spec B "ell.nextshape" next (gs[3] * q₆) k hin h1 hkB
      (hfinal.1.trans_lt hSB) (hfinal.2.trans_lt hSB))
    (by
      intro x hx
      simp [loopFields] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [storeReduced, Com.wvars])
  have hphaseFrames (c : Com) (hc : c ∈ [shapeDifference, roundedEntry]) :
      (∀ x ∈ loopFields, x ∉ c.wvars) ∧ c.warrs = [] := by
    simp at hc
    rcases hc with rfl | rfl
    all_goals constructor
    all_goals try (intro x hx; simp [loopFields] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl)
    all_goals simp [shapeDifference, roundedEntry, multiplyFraction, subtractFraction, negateRight,
      resultToRight, resultToLeft, loadLeft, RamRounding.roundFraction, addFraction,
      RamArithmetic.normalizeFraction, RamArithmetic.gcdLoop, RamArithmetic.gcdDoubleStep,
      RamArithmetic.gcdStep, Com.wvars, Com.warrs]
  have hproduct : Spec B (fun σ => Represents "ell.u" us σ ∧ σ.vars "entry.k" = k ∧ σ.vars "vec.n" = n)
      entryProduct
      (fun σ τ => FractionOutput q₁ τ ∧ τ.vars "entry.i" = k / n ∧ τ.vars "entry.j" = k % n ∧
        τ.vars "entry.k" = k ∧ τ.vars "vec.n" = n ∧ τ.vars "grid.D" = σ.vars "grid.D" ∧ τ.arrs = σ.arrs)
      (72 * (shapeCap M).size + 96) := by
    rintro σ ⟨hσu, hσk, hσn⟩
    run_vcg [hindex, hloadU, hloadV, hmul₁]
    all_goals clear hindex hloadU hloadV hmul₁ hright₁ hloadβ hmul₂ hright₂ hloadX hsub hright₃ hloadα hmul₃ hleft hround hdiag hright₄ hloadρ hmul₄ hstore
    all_goals simp_all [q₁, LeftValue, RightValue, FractionOutput, Represents, FieldsAgree, loopFields]
    all_goals aesop
  have hdifferencePlain : Spec B (fun σ => FractionOutput q₁ σ ∧ Represents "ell.coeff" gs σ ∧
      Represents "ell.shape" xs σ ∧ σ.vars "entry.k" = k) shapeDifference
      (fun _ τ => FractionOutput q₃ τ) (144 * (shapeCap M).size + 198) := by
    rintro σ ⟨hσq, hσg, hσx, hσk⟩
    run_vcg [hright₁, hloadβ, hmul₂, hright₂, hloadX, hsub]
    all_goals clear hproduct hphaseFrames hindex hloadU hloadV hmul₁ hright₁ hloadβ hmul₂ hright₂ hloadX hsub hright₃ hloadα hmul₃ hleft hround hdiag hright₄ hloadρ hmul₄ hstore
    all_goals simp_all [q₁, q₂, q₃, LeftValue, RightValue, FractionOutput, Represents, FieldsAgree, loopFields]
    all_goals aesop
  have hdifference := spec_with_fields loopFields hdifferencePlain
    (hphaseFrames shapeDifference (by simp)).1 (hphaseFrames shapeDifference (by simp)).2
  have hroundedPlain : Spec B (fun σ => FractionOutput q₃ σ ∧ Represents "ell.coeff" gs σ ∧
      σ.vars "grid.D" = D) roundedEntry
      (fun _ τ => FractionOutput q₅ τ) (108 * (shapeCap M).size + 183) := by
    rintro σ ⟨hσq, hσg, hσD⟩
    run_vcg [hright₃, hloadα, hmul₃, hleft, hround]
    all_goals clear hproduct hdifferencePlain hdifference hphaseFrames hindex hloadU hloadV hmul₁ hright₁ hloadβ hmul₂ hright₂ hloadX hsub hright₃ hloadα hmul₃ hleft hround hdiag hright₄ hloadρ hmul₄ hstore
    all_goals simp_all [q₁, q₂, q₃, q₄, q₅, LeftValue, RightValue, FractionOutput, Represents, FieldsAgree, loopFields]
    all_goals aesop
  have hrounded := spec_with_fields loopFields hroundedPlain
    (hphaseFrames roundedEntry (by simp)).1 (hphaseFrames roundedEntry (by simp)).2
  have hinflatedPlain : Spec B (fun σ => FractionOutput q₅ σ ∧ Represents "ell.coeff" gs σ ∧
      Represents "ell.nextshape" next σ ∧ σ.vars "entry.i" = k / n ∧
      σ.vars "entry.j" = k % n ∧ σ.vars "entry.k" = k) inflatedEntry
      (fun _ τ => Represents "ell.nextshape" (next.set k (gs[3] * q₆)) τ)
      (144 * (shapeCap M).size + 213) := by
    rintro σ ⟨hσq, hσg, hσnext, hσi, hσj, hσk⟩
    run_vcg [hdiag, hright₄, hloadρ, hmul₄, hstore]
    all_goals clear hproduct hdifferencePlain hdifference hroundedPlain hrounded hphaseFrames hindex hloadU hloadV hmul₁ hright₁ hloadβ hmul₂ hright₂ hloadX hsub hright₃ hloadα hmul₃ hleft hround hdiag hright₄ hloadρ hmul₄ hstore
    all_goals simp_all [q₁, q₂, q₃, q₄, q₅, q₆, LeftValue, RightValue, FractionOutput,
      Represents, FieldsAgree, loopFields, storeReduced, Com.warrs]
    all_goals aesop
  have hinflated := spec_with_write_frame loopFields hinflatedPlain
    (by
      intro x hx
      simp [loopFields] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      all_goals simp [inflatedEntry, addDiagonal, storeReduced, multiplyFraction, addFraction,
        resultToRight, resultToLeft, loadLeft, loadRight, RamArithmetic.normalizeFraction,
        RamArithmetic.gcdLoop, RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.wvars])
  rintro σ ⟨hσu, hσx, hσg, hσnext, hσk, hσn, hσD⟩
  run_vcg [hproduct, hdifference, hrounded, hinflated]
  all_goals clear hproduct hdifference hrounded hinflated hdifferencePlain hroundedPlain hinflatedPlain hphaseFrames hindex hloadU hloadV hmul₁ hright₁ hloadβ hmul₂ hright₂ hloadX hsub hright₃ hloadα hmul₃ hleft hround hdiag hright₄ hloadρ hmul₄ hstore
  all_goals simp_all [q₁, q₂, q₃, q₄, q₅, q₆, FractionOutput, Represents, FieldsAgree,
    loopFields, inflatedEntry, addDiagonal, storeReduced, multiplyFraction, addFraction, resultToRight,
    resultToLeft, loadLeft, loadRight, RamArithmetic.normalizeFraction, RamArithmetic.gcdLoop,
    RamArithmetic.gcdDoubleStep, RamArithmetic.gcdStep, Com.warrs]
  all_goals aesop

end Lax109476Proofs.RamShapeCoordinate

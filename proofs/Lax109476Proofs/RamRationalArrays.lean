import Lax109476Proofs.RamRational
import Lax109476Proofs.RamEncoding
import Lax109476.RationalEncoding

namespace Lax109476Proofs.RamRationalArrays

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational

def rationalSign (q : ℚ) : ℕ := if q.num < 0 then 1 else 0

theorem rationalSign_le_one (q : ℚ) : rationalSign q ≤ 1 := by unfold rationalSign; split_ifs <;> omega

theorem canonical_fractionValue (q : ℚ) :
    fractionValue (rationalSign q) q.num.natAbs q.den = q := by
  calc
    _ = (q.num : ℚ) / q.den := by
      by_cases h : q.num < 0
      · have hq : (q.num : ℚ) < 0 := by exact_mod_cast h
        simp [fractionValue, rationalSign, h, Nat.cast_natAbs, Int.cast_abs, abs_of_neg hq]
      · have hq : (0 : ℚ) ≤ q.num := by exact_mod_cast le_of_not_gt h
        simp [fractionValue, rationalSign, h, Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg hq]
    _ = q := q.num_div_den

/-- Three arrays hold reduced rational coordinates. Separating the three
fields avoids index multiplication when scanning a vector or matrix row. -/
def Represents (a : String) (qs : List ℚ) (σ : Env) : Prop :=
  σ.arrs (a ++ ".s") = qs.map rationalSign ∧
    σ.arrs (a ++ ".n") = qs.map (fun q => q.num.natAbs) ∧
    σ.arrs (a ++ ".d") = qs.map (fun q => q.den)

def loadLeft (a : String) : Com :=
  .seq (.assign "left.s" (.get (a ++ ".s") (.var "vec.i")))
    (.seq (.assign "left.n" (.get (a ++ ".n") (.var "vec.i")))
      (.assign "left.d" (.get (a ++ ".d") (.var "vec.i"))))

def LeftOutput (q : ℚ) (σ : Env) : Prop :=
  σ.vars "left.s" = rationalSign q ∧ σ.vars "left.n" = q.num.natAbs ∧ σ.vars "left.d" = q.den

theorem map_getD {α : Type*} (f : α → ℕ) (xs : List α) (i : ℕ) (hi : i < xs.length) :
    (xs.map f).getD i 0 = f xs[i] := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem loadLeft_spec (B : ℕ) (a : String) (qs : List ℚ) (i : ℕ) (hi : i < qs.length)
    (hB : 1 < B) (hiB : i < B) (hn : qs[i].num.natAbs < B) (hd : qs[i].den < B) :
    Spec B (fun σ => Represents a qs σ ∧ σ.vars "vec.i" = i) (loadLeft a)
      (fun _ τ => LeftOutput qs[i] τ) 9 := by
  rintro σ ⟨⟨hσs, hσn, hσd⟩, hσi⟩
  have hsB := (rationalSign_le_one qs[i]).trans_lt hB
  have hsl : i < (σ.arrs (a ++ ".s")).length := by rw [hσs, List.length_map]; exact hi
  have hnl : i < (σ.arrs (a ++ ".n")).length := by rw [hσn, List.length_map]; exact hi
  have hdl : i < (σ.arrs (a ++ ".d")).length := by rw [hσd, List.length_map]; exact hi
  have hsg : (σ.arrs (a ++ ".s")).getD i 0 = rationalSign qs[i] := by
    rw [hσs]; exact map_getD _ _ _ hi
  have hng : (σ.arrs (a ++ ".n")).getD i 0 = qs[i].num.natAbs := by
    rw [hσn]; exact map_getD _ _ _ hi
  have hdg : (σ.arrs (a ++ ".d")).getD i 0 = qs[i].den := by
    rw [hσd]; exact map_getD _ _ _ hi
  run_vcg
  all_goals simp_all [LeftOutput]

theorem loadLeft_frame_spec (B : ℕ) (a : String) (qs : List ℚ) (i : ℕ) (hi : i < qs.length)
    (hB : 1 < B) (hiB : i < B) (hn : qs[i].num.natAbs < B) (hd : qs[i].den < B) :
    Spec B (fun σ => Represents a qs σ ∧ σ.vars "vec.i" = i) (loadLeft a)
      (fun σ τ => LeftOutput qs[i] τ ∧ τ.vars "vec.i" = i ∧ τ.arrs = σ.arrs) 9 := by
  intro σ hσ
  obtain ⟨τ, hr, hτ⟩ := loadLeft_spec B a qs i hi hB hiB hn hd σ hσ
  refine ⟨τ, hr, hτ, (hr.frame_var "vec.i" (by simp [loadLeft, Com.wvars])).trans hσ.2, ?_⟩
  funext b
  exact hr.frame_arr b (by simp [loadLeft, Com.warrs])

def loadRight (a : String) : Com :=
  .seq (.assign "right.s" (.get (a ++ ".s") (.var "vec.i")))
    (.seq (.assign "right.n" (.get (a ++ ".n") (.var "vec.i")))
      (.assign "right.d" (.get (a ++ ".d") (.var "vec.i"))))

def RightOutput (q : ℚ) (σ : Env) : Prop :=
  σ.vars "right.s" = rationalSign q ∧ σ.vars "right.n" = q.num.natAbs ∧ σ.vars "right.d" = q.den

theorem loadRight_spec (B : ℕ) (a : String) (qs : List ℚ) (i : ℕ) (hi : i < qs.length)
    (hB : 1 < B) (hiB : i < B) (hn : qs[i].num.natAbs < B) (hd : qs[i].den < B) :
    Spec B (fun σ => Represents a qs σ ∧ σ.vars "vec.i" = i) (loadRight a)
      (fun _ τ => RightOutput qs[i] τ) 9 := by
  rintro σ ⟨⟨hσs, hσn, hσd⟩, hσi⟩
  have hsB := (rationalSign_le_one qs[i]).trans_lt hB
  have hsl : i < (σ.arrs (a ++ ".s")).length := by rw [hσs, List.length_map]; exact hi
  have hnl : i < (σ.arrs (a ++ ".n")).length := by rw [hσn, List.length_map]; exact hi
  have hdl : i < (σ.arrs (a ++ ".d")).length := by rw [hσd, List.length_map]; exact hi
  have hsg : (σ.arrs (a ++ ".s")).getD i 0 = rationalSign qs[i] := by
    rw [hσs]; exact map_getD _ _ _ hi
  have hng : (σ.arrs (a ++ ".n")).getD i 0 = qs[i].num.natAbs := by
    rw [hσn]; exact map_getD _ _ _ hi
  have hdg : (σ.arrs (a ++ ".d")).getD i 0 = qs[i].den := by
    rw [hσd]; exact map_getD _ _ _ hi
  run_vcg
  all_goals simp_all [RightOutput]

theorem loadRight_frame_spec (B : ℕ) (a : String) (qs : List ℚ) (i : ℕ) (hi : i < qs.length)
    (hB : 1 < B) (hiB : i < B) (hn : qs[i].num.natAbs < B) (hd : qs[i].den < B) :
    Spec B (fun σ => Represents a qs σ ∧ σ.vars "vec.i" = i) (loadRight a)
      (fun σ τ => RightOutput qs[i] τ ∧ τ.vars "vec.i" = i ∧ τ.arrs = σ.arrs ∧
        τ.vars "left.s" = σ.vars "left.s" ∧ τ.vars "left.n" = σ.vars "left.n" ∧
        τ.vars "left.d" = σ.vars "left.d") 9 := by
  intro σ hσ
  obtain ⟨τ, hr, hτ⟩ := loadRight_spec B a qs i hi hB hiB hn hd σ hσ
  refine ⟨τ, hr, hτ, (hr.frame_var "vec.i" (by simp [loadRight, Com.wvars])).trans hσ.2,
    ?_, hr.frame_var "left.s" (by simp [loadRight, Com.wvars]),
    hr.frame_var "left.n" (by simp [loadRight, Com.wvars]),
    hr.frame_var "left.d" (by simp [loadRight, Com.wvars])⟩
  funext b
  exact hr.frame_arr b (by simp [loadRight, Com.warrs])

def storeReduced (a : String) : Com :=
  .seq (.ite (.eq (.var "rat.n") (.lit 0))
    (.store (a ++ ".s") (.var "vec.i") (.lit 0))
    (.store (a ++ ".s") (.var "vec.i") (.var "rat.s")))
    (.seq (.store (a ++ ".n") (.var "vec.i") (.var "rat.n"))
      (.store (a ++ ".d") (.var "vec.i") (.var "rat.d")))

theorem storeReduced_spec (B : ℕ) (a : String) (qs : List ℚ) (q : ℚ) (i : ℕ)
    (hi : i < qs.length) (hB : 1 < B) (hiB : i < B)
    (hn : q.num.natAbs < B) (hd : q.den < B) :
    Spec B (fun σ => Represents a qs σ ∧ σ.vars "vec.i" = i ∧ FractionOutput q σ)
      (storeReduced a) (fun _ τ => Represents a (qs.set i q) τ) 13 := by
  rintro σ ⟨⟨hσs, hσn, hσd⟩, hσi, hv, hratn, hratd, hrats⟩
  have hnB : σ.vars "rat.n" < B := hratn ▸ hn
  have hdB : σ.vars "rat.d" < B := hratd ▸ hd
  have hsB : σ.vars "rat.s" < B := hrats.trans_lt hB
  have hsl : i < (σ.arrs (a ++ ".s")).length := by rw [hσs, List.length_map]; exact hi
  have hnl : i < (σ.arrs (a ++ ".n")).length := by rw [hσn, List.length_map]; exact hi
  have hdl : i < (σ.arrs (a ++ ".d")).length := by rw [hσd, List.length_map]; exact hi
  have hsn : a ++ ".s" ≠ a ++ ".n" := by simp
  have hsd : a ++ ".s" ≠ a ++ ".d" := by simp
  have hnd : a ++ ".n" ≠ a ++ ".d" := by simp
  have hns := Ne.symm hsn
  have hds := Ne.symm hsd
  have hdn := Ne.symm hnd
  have hsign := RamEncoding.fractionValue_sign (σ.vars "rat.s") (σ.vars "rat.n")
    (σ.vars "rat.d") hrats (hratd ▸ q.den_pos)
  rw [hv] at hsign
  change rationalSign q = _ at hsign
  run_vcg
  all_goals simp_all [Represents, Env.setArr, List.map_set]

end Lax109476Proofs.RamRationalArrays

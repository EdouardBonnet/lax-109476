import Lax109476Proofs.RamRationalArrays
import Lax808846Proofs.Lib.Fill

namespace Lax109476Proofs.RamZeroArray

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays

/-- Array extent is a ghost parameter of the verified RAM compiler; this
phase initializes every field that will subsequently represent a rational. -/
def fillConstant (a : String) (v : ℕ) : Com :=
  .seq (.assign "vec.i" (.lit 0))
    (.while (.lt (.var "vec.i") (.var "vec.n")) (Lib.Fill.put a "vec.i" (.lit v)))

theorem exists_arrOf (xs : List ℕ) (n : ℕ) (h : xs.length = n) : ∃ g, xs = arrOf n g := by
  refine ⟨fun i => xs.getD i 0, ?_⟩
  apply List.ext_getElem
  · simp [h]
  · intro i hi hj
    simp [arrOf, List.getD_eq_getElem?_getD, hi]

theorem fillConstant_spec (B n v : ℕ) (a : String) (hnB : n < B) (hvB : v < B) :
    Spec B (fun σ => (σ.arrs a).length = n ∧ σ.vars "vec.n" = n) (fillConstant a v)
      (fun σ τ => τ.arrs a = List.replicate n v ∧ τ.vars "vec.n" = n ∧
        ∀ b ≠ a, τ.arrs b = σ.arrs b) (11 * n + 6) := by
  have hfill := Lib.Fill.loop_spec B n a "vec.i" "vec.n" (.lit v) (fun _ => v)
    (by decide) hnB (by intros; exact evalB_lit hvB)
  intro σ hσ
  obtain ⟨τ, hr, ⟨g, hτg, hg⟩, _⟩ := hfill σ ⟨exists_arrOf _ _ hσ.1, hσ.2⟩
  refine ⟨τ, hr, ?_, ?_, ?_⟩
  · rw [hτg, replicate_eq_arrOf]
    exact arrOf_congr hg
  · exact (hr.frame_var "vec.n" (by simp [Lib.Fill.put, Com.wvars])).trans hσ.2
  · intro b hb
    exact hr.frame_arr b (by simp [Lib.Fill.put, Com.warrs, hb])

def zeroRationalArray (a : String) : Com :=
  .seq (fillConstant (a ++ ".s") 0)
    (.seq (fillConstant (a ++ ".n") 0) (fillConstant (a ++ ".d") 1))

theorem zeroRationalArray_spec (B n : ℕ) (a : String) (hnB : n < B) (h1 : 1 < B) :
    Spec B (fun σ => (σ.arrs (a ++ ".s")).length = n ∧
        (σ.arrs (a ++ ".n")).length = n ∧ (σ.arrs (a ++ ".d")).length = n ∧ σ.vars "vec.n" = n)
      (zeroRationalArray a)
      (fun σ τ => Represents a (List.replicate n 0) τ ∧ τ.vars "vec.n" = n ∧
        ∀ b ∉ [a ++ ".s", a ++ ".n", a ++ ".d"], τ.arrs b = σ.arrs b)
      (33 * n + 18) := by
  have h0 : 0 < B := by omega
  have hsn : a ++ ".s" ≠ a ++ ".n" := by simp
  have hsd : a ++ ".s" ≠ a ++ ".d" := by simp
  have hnd : a ++ ".n" ≠ a ++ ".d" := by simp
  rintro σ ⟨hσs, hσn, hσd, hσN⟩
  obtain ⟨τ, hr₁, hτs, hτN, hτa⟩ := fillConstant_spec B n 0 (a ++ ".s") hnB h0 σ ⟨hσs, hσN⟩
  have hτn : (τ.arrs (a ++ ".n")).length = n := by rw [hτa _ hsn.symm]; exact hσn
  obtain ⟨υ, hr₂, hυn, hυN, hυa⟩ := fillConstant_spec B n 0 (a ++ ".n") hnB h0 τ ⟨hτn, hτN⟩
  have hυd : (υ.arrs (a ++ ".d")).length = n := by
    rw [hυa _ hnd.symm, hτa _ hsd.symm]; exact hσd
  obtain ⟨ρ, hr₃, hρd, hρN, hρa⟩ := fillConstant_spec B n 1 (a ++ ".d") hnB h1 υ ⟨hυd, hυN⟩
  have hρs : ρ.arrs (a ++ ".s") = List.replicate n 0 := by rw [hρa _ hsd, hυa _ hsn, hτs]
  have hρn : ρ.arrs (a ++ ".n") = List.replicate n 0 := by rw [hρa _ hnd, hυn]
  refine ⟨ρ, (hr₁.seq (hr₂.seq hr₃)).mono (by omega), ?_, hρN, ?_⟩
  · simp [Represents, hρs, hρn, hρd, rationalSign]
  · intro b hb
    simp at hb
    exact (hρa b hb.2.2).trans ((hυa b hb.2.1).trans (hτa b hb.1))

end Lax109476Proofs.RamZeroArray

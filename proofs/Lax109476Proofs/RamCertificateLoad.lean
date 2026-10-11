import Lax109476Proofs.RamCertificateSource

namespace Lax109476Proofs.RamCertificateLoad

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds RamCertificateSource IntegerEncoding

def matrix : Com := .seq (.assign "vec.i"
  (.add (.mul (.var "query.a.row") (.var "source.n")) (.var "query.a.col"))) (RamArrayResult.load "source.A")

def loadFields : List String := ["source.m", "source.n", "query.row", "query.col", "query.a.row", "query.a.col", "certificate.kind"]

set_option maxHeartbeats 800000 in
theorem matrix_spec (B M m n : ℕ) (P : Program ℤ m n) (i : Fin m) (j : Fin n)
    (hM : 1 ≤ M) (hMB : M < B) (hB : m * n + m + n + 4 < B) (hq : (P.A i j).natAbs ≤ M) :
    Spec B (fun σ => Data P σ ∧ σ.vars "query.a.row" = i.val ∧ σ.vars "query.a.col" = j.val) matrix
      (fun _ τ => Data P τ ∧ FractionOutput (P.A i j : ℚ) τ) 21 := by
  have h1 : 1 < B := by omega
  have hi : i.val < B := i.isLt.trans (by omega)
  have hj : j.val < B := j.isLt.trans (by omega)
  have hn : n < B := by omega
  let index := i.val * n + j.val
  have hindex : index < (RamMatrixStorage.flatten (rationalProgram P).A).length := by
    simpa [RamMatrixStorage.flatten, index] using RamMatrixStorage.row_index_lt i j
  have hindexB : index < B := (by simpa only [RamMatrixStorage.flatten, List.length_ofFn] using hindex : index < m * n).trans (by omega)
  have hmul : i.val * n < B := by dsimp only [index] at hindexB; omega
  have he : (RamMatrixStorage.flatten (rationalProgram P).A)[index] = (P.A i j : ℚ) :=
    RamMatrixStorage.flatten_entry (rationalProgram P).A i j
  have hqH : Height (P.A i j : ℚ) M := ⟨by simpa using hq, by simpa using hM⟩
  have hload := spec_with_fields loadFields
    (RamArrayResult.load_spec B "source.A" (RamMatrixStorage.flatten (rationalProgram P).A) index hindex h1 hindexB
      (by rw [he]; exact hqH.1.trans_lt hMB) (by rw [he]; exact hqH.2.trans_lt hMB))
    (by intro a ha; simp [loadFields] at ha; rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by rfl)
  have hbase : Spec B (fun σ => Data P σ ∧ σ.vars "query.a.row" = i.val ∧ σ.vars "query.a.col" = j.val) matrix
      (fun _ τ => FractionOutput (P.A i j : ℚ) τ) 21 := by
    rintro σ ⟨⟨hσA, hσb, hσc, hσm, hσn⟩, hσi, hσj⟩
    run_vcg [hload]
    all_goals clear hload
    all_goals simp_all [loadFields, FieldsAgree, Represents, index]
  intro σ hσ
  obtain ⟨τ, hr, hτ⟩ := hbase σ hσ
  refine ⟨τ, hr, data_frame hr P hσ.1 ?_ ?_, hτ⟩
  · intro a ha; simp [RamCertificateSource.fields] at ha; rcases ha with rfl | rfl <;> decide
  · intro a ha s hs; change a ++ s ∉ ([] : List String); simp

def vector (a : String) : Com := .seq (.assign "vec.i" (.var "query.a.row")) (RamArrayResult.load a)

theorem vector_wvars (a : String) : (vector a).wvars = (vector "").wvars := by rfl

theorem vector_spec (B m n r : ℕ) (P : Program ℤ m n) (a : String) (v : Fin r → ℚ) (i : Fin r)
    (h1 : 1 < B) (hi : i.val < B) (hn : (v i).num.natAbs < B) (hd : (v i).den < B) :
    Spec B (fun σ => Data P σ ∧ Represents a (List.ofFn v) σ ∧ σ.vars "query.a.row" = i.val) (vector a)
      (fun _ τ => Data P τ ∧ FractionOutput (v i) τ) 17 := by
  have hload := RamArrayResult.load_spec B a (List.ofFn v) i.val (by simpa using i.isLt) h1 hi
    (by simpa using hn) (by simpa using hd)
  have hbase : Spec B (fun σ => Represents a (List.ofFn v) σ ∧ σ.vars "query.a.row" = i.val) (vector a)
      (fun _ τ => FractionOutput (v i) τ) 17 := by
    rintro σ ⟨hσa, hσi⟩
    run_vcg [hload]
    all_goals clear hload
    all_goals simp_all [Represents, arrs_setVar]
  rintro σ ⟨hσData, hσa, hσi⟩
  obtain ⟨τ, hr, hτ⟩ := hbase σ ⟨hσa, hσi⟩
  refine ⟨τ, hr, data_frame hr P hσData ?_ ?_, hτ⟩
  · intro f hf; rw [vector_wvars]; simp [RamCertificateSource.fields] at hf; rcases hf with rfl | rfl <;> decide
  · intro a ha s hs; change a ++ s ∉ ([] : List String); simp

theorem bound_spec (B m n : ℕ) (P : Program ℤ m n) (i : Fin m)
    (h1 : 1 < B) (hi : i.val < B) (hn : (P.b i).natAbs < B) :
    Spec B (fun σ => Data P σ ∧ σ.vars "query.a.row" = i.val) (vector "source.b")
      (fun _ τ => Data P τ ∧ FractionOutput (P.b i : ℚ) τ) 17 := by
  exact (vector_spec B m n m P "source.b" (rationalProgram P).b i h1 hi
    (by simpa [rationalProgram] using hn) (by simpa [rationalProgram] using h1)).pre
      (fun _ h => ⟨h.1, h.1.2.1, h.2⟩)

theorem objective_spec (B m n : ℕ) (P : Program ℤ m n) (i : Fin n)
    (h1 : 1 < B) (hi : i.val < B) (hn : (P.c i).natAbs < B) :
    Spec B (fun σ => Data P σ ∧ σ.vars "query.a.row" = i.val) (vector "source.c")
      (fun _ τ => Data P τ ∧ FractionOutput (P.c i : ℚ) τ) 17 := by
  exact (vector_spec B m n n P "source.c" (rationalProgram P).c i h1 hi
    (by simpa [rationalProgram] using hn) (by simpa [rationalProgram] using h1)).pre
      (fun _ h => ⟨h.1, h.1.2.2.1, h.2⟩)

end Lax109476Proofs.RamCertificateLoad

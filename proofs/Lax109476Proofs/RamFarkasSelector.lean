import Lax109476Proofs.RamCertificateLoad
import Lax109476Proofs.CertificateFamilyEntries
import Lax109476Proofs.RamPadSelector
import Lax109476Proofs.RamResultNegation

namespace Lax109476Proofs.RamFarkasSelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds RamCertificateSource IntegerEncoding

def selectEntry : Com := .ite (.lt (.var "query.row") (.var "source.n"))
  (.seq (.assign "query.a.row" (.var "query.col"))
    (.seq (.assign "query.a.col" (.var "query.row"))
      (.seq RamCertificateLoad.matrix RamResultNegation.negateResult)))
  (.seq (.assign "query.a.row" (.var "query.col")) (RamCertificateLoad.vector "source.b"))

set_option maxHeartbeats 1000000 in
theorem selectEntry_spec (B M m n : ℕ) (P : Program ℤ m n) (i : Fin (n + 1)) (j : Fin m)
    (hM : 1 ≤ M) (hMB : M < B) (hB : m * n + 2 * m + 2 * n + 8 < B)
    (hA : ∀ r s, (P.A r s).natAbs ≤ M) (hb : ∀ r, (P.b r).natAbs ≤ M) :
    Spec B (fun σ => Data P σ ∧ σ.vars "query.row" = i.val ∧ σ.vars "query.col" = j.val)
      selectEntry (fun _ τ => Data P τ ∧ FractionOutput (CertificateFamilyEntries.farkasEntry P i j : ℚ) τ) 40 := by
  have h1 : 1 < B := by omega
  have hn : n < B := by omega
  have hiB : i.val < B := i.isLt.trans (by omega)
  have hjB : j.val < B := j.isLt.trans (by omega)
  have hbase : Spec B (fun σ => Data P σ ∧ σ.vars "query.row" = i.val ∧ σ.vars "query.col" = j.val)
      selectEntry (fun _ τ => FractionOutput (CertificateFamilyEntries.farkasEntry P i j : ℚ) τ) 40 := by
    rintro σ ⟨⟨hσA, hσb, hσc, hσm, hσn⟩, hσrow, hσcol⟩
    by_cases hi : i.val < n
    · let ii : Fin n := ⟨i.val, hi⟩
      have hload := RamCertificateLoad.matrix_spec B M m n P j ii hM hMB (by omega) (hA j ii)
      have hneg := RamResultNegation.negateResult_spec B (P.A j ii : ℚ) h1
      run_vcg [hload, hneg]
      all_goals clear hload hneg
      all_goals simp_all [CertificateFamilyEntries.farkasEntry, ii, Data, Represents, arrs_setVar]
      all_goals (try split_ifs) <;> (try simp_all) <;> omega
    · have hload := RamCertificateLoad.bound_spec B m n P j h1 hjB ((hb j).trans_lt hMB)
      run_vcg [hload]
      all_goals clear hload
      all_goals simp_all [CertificateFamilyEntries.farkasEntry, Data, Represents, arrs_setVar]
      all_goals (try split_ifs) <;> (try simp_all) <;> omega
  intro σ hσ
  obtain ⟨τ, hr, hτ⟩ := hbase σ hσ
  refine ⟨τ, hr, data_frame hr P hσ.1 ?_ ?_, hτ⟩
  · intro a ha; simp [RamCertificateSource.fields] at ha; rcases ha with rfl | rfl <;> decide
  · intro a ha s hs; change a ++ s ∉ ([] : List String); simp

def selectBound : Com := .ite (.lt (.var "query.row") (.var "source.n"))
  (RamPadSelector.constantFraction 0)
  (.seq (RamPadSelector.constantFraction 1) RamResultNegation.negateResult)

theorem selectBound_spec (B m n : ℕ) (P : Program ℤ m n) (i : Fin (n + 1))
    (hB : n + 2 < B) :
    Spec B (fun σ => Data P σ ∧ σ.vars "query.row" = i.val) selectBound
      (fun _ τ => Data P τ ∧ FractionOutput (CertificateFamilyEntries.farkasRhs i : ℚ) τ) 16 := by
  have h1 : 1 < B := by omega
  have hiB : i.val < B := i.isLt.trans (by omega)
  have hn : n < B := by omega
  have hz := RamPadSelector.constantFraction_spec B 0 h1 (by omega)
  have ho := RamPadSelector.constantFraction_spec B 1 h1 h1
  have hneg := RamResultNegation.negateResult_spec B 1 h1
  have hbase : Spec B (fun σ => Data P σ ∧ σ.vars "query.row" = i.val) selectBound
      (fun _ τ => FractionOutput (CertificateFamilyEntries.farkasRhs i : ℚ) τ) 16 := by
    rintro σ ⟨⟨hσA, hσb, hσc, hσm, hσn⟩, hσrow⟩
    by_cases hi : i.val < n
    all_goals run_vcg [hz, ho, hneg]
    all_goals clear hz ho hneg
    all_goals simp_all [CertificateFamilyEntries.farkasRhs]
    all_goals (try split_ifs) <;> (try simp_all) <;> omega
  intro σ hσ
  obtain ⟨τ, hr, hτ⟩ := hbase σ hσ
  refine ⟨τ, hr, data_frame hr P hσ.1 ?_ ?_, hτ⟩
  · intro a ha; simp [RamCertificateSource.fields] at ha; rcases ha with rfl | rfl <;> decide
  · intro a ha s hs; change a ++ s ∉ ([] : List String); simp

end Lax109476Proofs.RamFarkasSelector

import Lax109476Proofs.RamCertificateLoad
import Lax109476Proofs.CertificateFamilyEntries
import Lax109476Proofs.RamPadSelector
import Lax109476Proofs.RamResultNegation

namespace Lax109476Proofs.RamPairSelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds RamCertificateSource IntegerEncoding

def primalEntry : Com := .ite (.lt (.var "query.col") (.var "source.n"))
  (.seq (.assign "query.a.row" (.var "query.row"))
    (.seq (.assign "query.a.col" (.var "query.col")) RamCertificateLoad.matrix))
  (RamPadSelector.constantFraction 0)

def dualEntry : Com := .ite (.lt (.var "query.col") (.var "source.n"))
  (RamPadSelector.constantFraction 0)
  (.seq (.assign "query.a.row" (.sub (.var "query.col") (.var "source.n")))
    (.seq (.assign "query.a.col" (.sub (.var "query.row") (.var "source.m")))
      (.seq RamCertificateLoad.matrix RamResultNegation.negateResult)))

def gapEntry : Com := .ite (.lt (.var "query.col") (.var "source.n"))
  (.seq (.assign "query.a.row" (.var "query.col")) (RamCertificateLoad.vector "source.c"))
  (.seq (.assign "query.a.row" (.sub (.var "query.col") (.var "source.n")))
    (.seq (RamCertificateLoad.vector "source.b") RamResultNegation.negateResult))

def selectEntry : Com := .ite (.lt (.var "query.row") (.var "source.m")) primalEntry
  (.ite (.lt (.var "query.row") (.add (.var "source.m") (.var "source.n"))) dualEntry
    (.ite (.eq (.var "query.row") (.add (.var "source.m") (.var "source.n"))) gapEntry
      (.seq gapEntry RamResultNegation.negateResult)))

set_option maxHeartbeats 1600000 in
theorem selectEntry_spec (B M m n : ℕ) (P : Program ℤ m n) (i : Fin (m + (n + 2))) (j : Fin (n + m))
    (hM : 1 ≤ M) (hMB : M < B) (hB : m * n + 2 * m + 2 * n + 8 < B)
    (hA : ∀ r s, (P.A r s).natAbs ≤ M) (hb : ∀ r, (P.b r).natAbs ≤ M)
    (hc : ∀ s, (P.c s).natAbs ≤ M) :
    Spec B (fun σ => Data P σ ∧ σ.vars "query.row" = i.val ∧ σ.vars "query.col" = j.val)
      selectEntry (fun _ τ => Data P τ ∧ FractionOutput (CertificateFamilyEntries.pairEntry P i j : ℚ) τ) 72 := by
  have h1 : 1 < B := by omega
  have hm : m < B := by omega
  have hn : n < B := by omega
  have hmn : m + n < B := by omega
  have hiB : i.val < B := i.isLt.trans (by omega)
  have hjB : j.val < B := j.isLt.trans (by omega)
  have hisub : i.val - m < B := (Nat.sub_le _ _).trans_lt hiB
  have hjsub : j.val - n < B := (Nat.sub_le _ _).trans_lt hjB
  have hz := RamPadSelector.constantFraction_spec B 0 h1 (by omega)
  have hbase : Spec B (fun σ => Data P σ ∧ σ.vars "query.row" = i.val ∧ σ.vars "query.col" = j.val)
      selectEntry (fun _ τ => FractionOutput (CertificateFamilyEntries.pairEntry P i j : ℚ) τ) 72 := by
    rintro σ ⟨⟨hσA, hσb, hσc, hσm, hσn⟩, hσrow, hσcol⟩
    by_cases hi : i.val < m
    · by_cases hj : j.val < n
      · let ii : Fin m := ⟨i.val, hi⟩
        let jj : Fin n := ⟨j.val, hj⟩
        have hload := RamCertificateLoad.matrix_spec B M m n P ii jj hM hMB (by omega) (hA ii jj)
        run_vcg [hload, hz]
        all_goals clear hload hz
        all_goals simp_all [CertificateFamilyEntries.pairEntry, ii, jj, Data, Represents, arrs_setVar]
        all_goals (try split_ifs) <;> (try simp_all) <;> omega
      · run_vcg [hz]
        all_goals clear hz
        all_goals simp_all [CertificateFamilyEntries.pairEntry, Data, Represents, arrs_setVar]
        all_goals (try split_ifs) <;> (try simp_all) <;> omega
    · by_cases hir : i.val < m + n
      · by_cases hj : j.val < n
        · run_vcg [hz]
          all_goals clear hz
          all_goals simp_all [CertificateFamilyEntries.pairEntry, Data, Represents, arrs_setVar]
          all_goals (try split_ifs) <;> (try simp_all) <;> omega
        · let ii : Fin m := ⟨j.val - n, by omega⟩
          let jj : Fin n := ⟨i.val - m, by omega⟩
          have hload := RamCertificateLoad.matrix_spec B M m n P ii jj hM hMB (by omega) (hA ii jj)
          have hneg := RamResultNegation.negateResult_spec B (P.A ii jj : ℚ) h1
          run_vcg [hload, hneg, hz]
          all_goals clear hload hneg hz
          all_goals simp_all [CertificateFamilyEntries.pairEntry, ii, jj, Data, Represents, arrs_setVar]
          all_goals (try split_ifs) <;> (try simp_all) <;> omega
      · by_cases hj : j.val < n
        · let jj : Fin n := ⟨j.val, hj⟩
          have hload := RamCertificateLoad.objective_spec B m n P jj h1 (jj.isLt.trans hn) ((hc jj).trans_lt hMB)
          have hneg := RamResultNegation.negateResult_spec B (P.c jj : ℚ) h1
          by_cases he : i.val = m + n
          all_goals run_vcg [hload, hneg, hz]
          all_goals clear hload hneg hz
          all_goals simp_all [CertificateFamilyEntries.pairEntry, jj, Data, Represents, arrs_setVar]
          all_goals (try split_ifs) <;> (try simp_all) <;> omega
        · let jj : Fin m := ⟨j.val - n, by omega⟩
          have hload := RamCertificateLoad.bound_spec B m n P jj h1 (jj.isLt.trans hm) ((hb jj).trans_lt hMB)
          have hneg := RamResultNegation.negateResult_spec B (P.b jj : ℚ) h1
          have hneg₂ := RamResultNegation.negateResult_spec B (-(P.b jj : ℚ)) h1
          by_cases he : i.val = m + n
          all_goals run_vcg [hload, hneg, hneg₂, hz]
          all_goals clear hload hneg hneg₂ hz
          all_goals simp_all [CertificateFamilyEntries.pairEntry, jj, Data, Represents, arrs_setVar]
          all_goals (try split_ifs) <;> (try simp_all) <;> omega
  intro σ hσ
  obtain ⟨τ, hr, hτ⟩ := hbase σ hσ
  refine ⟨τ, hr, data_frame hr P hσ.1 ?_ ?_, hτ⟩
  · intro a ha; simp [RamCertificateSource.fields] at ha; rcases ha with rfl | rfl <;> decide
  · intro a ha s hs; change a ++ s ∉ ([] : List String); simp

def selectBound : Com := .ite (.lt (.var "query.row") (.var "source.m"))
  (.seq (.assign "query.a.row" (.var "query.row")) (RamCertificateLoad.vector "source.b"))
  (.ite (.lt (.var "query.row") (.add (.var "source.m") (.var "source.n")))
    (.seq (.assign "query.a.row" (.sub (.var "query.row") (.var "source.m")))
      (.seq (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult))
    (RamPadSelector.constantFraction 0))

set_option maxHeartbeats 1000000 in
theorem selectBound_spec (B M m n : ℕ) (P : Program ℤ m n) (i : Fin (m + (n + 2)))
    (hM : 1 ≤ M) (hMB : M < B) (hB : m + n + 4 < B)
    (hb : ∀ r, (P.b r).natAbs ≤ M) (hc : ∀ s, (P.c s).natAbs ≤ M) :
    Spec B (fun σ => Data P σ ∧ σ.vars "query.row" = i.val) selectBound
      (fun _ τ => Data P τ ∧ FractionOutput (CertificateFamilyEntries.pairRhs P i : ℚ) τ) 40 := by
  have h1 : 1 < B := by omega
  have hm : m < B := by omega
  have hn : n < B := by omega
  have hmn : m + n < B := by omega
  have hiB : i.val < B := i.isLt.trans (by omega)
  have hisub : i.val - m < B := (Nat.sub_le _ _).trans_lt hiB
  have hz := RamPadSelector.constantFraction_spec B 0 h1 (by omega)
  have hbase : Spec B (fun σ => Data P σ ∧ σ.vars "query.row" = i.val) selectBound
      (fun _ τ => FractionOutput (CertificateFamilyEntries.pairRhs P i : ℚ) τ) 40 := by
    rintro σ ⟨⟨hσA, hσb, hσc, hσm, hσn⟩, hσrow⟩
    by_cases hi : i.val < m
    · let ii : Fin m := ⟨i.val, hi⟩
      have hload := RamCertificateLoad.bound_spec B m n P ii h1 (ii.isLt.trans hm) ((hb ii).trans_lt hMB)
      run_vcg [hload, hz]
      all_goals clear hload hz
      all_goals simp_all [CertificateFamilyEntries.pairRhs, ii, Data, Represents, arrs_setVar]
      all_goals (try split_ifs) <;> (try simp_all) <;> omega
    · by_cases hir : i.val < m + n
      · let ii : Fin n := ⟨i.val - m, by omega⟩
        have hload := RamCertificateLoad.objective_spec B m n P ii h1 (ii.isLt.trans hn) ((hc ii).trans_lt hMB)
        have hneg := RamResultNegation.negateResult_spec B (P.c ii : ℚ) h1
        run_vcg [hload, hneg, hz]
        all_goals clear hload hneg hz
        all_goals simp_all [CertificateFamilyEntries.pairRhs, ii, Data, Represents, arrs_setVar]
        all_goals (try split_ifs) <;> (try simp_all) <;> omega
      · run_vcg [hz]
        all_goals clear hz
        all_goals simp_all [CertificateFamilyEntries.pairRhs]
        all_goals (try split_ifs) <;> (try simp_all) <;> omega
  intro σ hσ
  obtain ⟨τ, hr, hτ⟩ := hbase σ hσ
  refine ⟨τ, hr, data_frame hr P hσ.1 ?_ ?_, hτ⟩
  · intro a ha; simp [RamCertificateSource.fields] at ha; rcases ha with rfl | rfl <;> decide
  · intro a ha s hs; change a ++ s ∉ ([] : List String); simp

end Lax109476Proofs.RamPairSelector

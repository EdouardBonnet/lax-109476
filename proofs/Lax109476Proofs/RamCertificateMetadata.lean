import Lax109476Proofs.RamCertificateContext

namespace Lax109476Proofs.RamCertificateMetadata

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamFrame RamCertificateSource RamCertificateContext

def optimal : Com := .seq
  (.assign "system.m" (.add (.var "source.m") (.add (.var "source.n") (.lit 2))))
  (.assign "system.n" (.add (.var "source.n") (.var "source.m")))

def infeasible : Com := .seq (.assign "system.m" (.add (.var "source.n") (.lit 1)))
  (.assign "system.n" (.var "source.m"))

def unbounded : Com := .seq
  (.assign "system.m" (.add (.var "source.m") (.add (.var "source.m") (.lit 1))))
  (.assign "system.n" (.add (.var "source.n") (.var "source.n")))

theorem optimal_spec (B m n : ℕ) (P : Program ℤ m n) (hB : 2 * m + 2 * n + 4 < B) :
    Spec B (Data P) optimal (fun _ τ => Context P (m + (n + 2)) (n + m) τ) 10 := by
  have h1 : 1 < B := by omega
  have h2 : 2 < B := by omega
  have hm : m < B := by omega
  have hn : n < B := by omega
  have hsum : m + n < B := by omega
  have hn2 : n + 2 < B := by omega
  have hr : m + (n + 2) < B := by omega
  have hbase : Spec B (fun σ => σ.vars "source.m" = m ∧ σ.vars "source.n" = n) optimal
      (fun _ τ => τ.vars "system.m" = m + (n + 2) ∧ τ.vars "system.n" = n + m) 10 := by
    rintro σ ⟨hσm, hσn⟩
    run_vcg
    all_goals simp_all
  intro σ hσ
  obtain ⟨τ, hr, hτ⟩ := hbase σ ⟨hσ.2.2.2.1, hσ.2.2.2.2⟩
  refine ⟨τ, hr, data_frame hr P hσ ?_ ?_, hτ⟩
  · intro a ha; simp [RamCertificateSource.fields] at ha; rcases ha with rfl | rfl <;> decide
  · intro a ha t ht; change a ++ t ∉ ([] : List String); simp

theorem infeasible_spec (B m n : ℕ) (P : Program ℤ m n) (hB : m + n + 2 < B) :
    Spec B (Data P) infeasible (fun _ τ => Context P (n + 1) m τ) 6 := by
  have h1 : 1 < B := by omega
  have hm : m < B := by omega
  have hn : n < B := by omega
  have hr : n + 1 < B := by omega
  have hbase : Spec B (fun σ => σ.vars "source.m" = m ∧ σ.vars "source.n" = n) infeasible
      (fun _ τ => τ.vars "system.m" = n + 1 ∧ τ.vars "system.n" = m) 6 := by
    rintro σ ⟨hσm, hσn⟩
    run_vcg
    all_goals simp_all
  intro σ hσ
  obtain ⟨τ, hr, hτ⟩ := hbase σ ⟨hσ.2.2.2.1, hσ.2.2.2.2⟩
  refine ⟨τ, hr, data_frame hr P hσ ?_ ?_, hτ⟩
  · intro a ha; simp [RamCertificateSource.fields] at ha; rcases ha with rfl | rfl <;> decide
  · intro a ha t ht; change a ++ t ∉ ([] : List String); simp

theorem unbounded_spec (B m n : ℕ) (P : Program ℤ m n) (hB : 2 * m + 2 * n + 4 < B) :
    Spec B (Data P) unbounded (fun _ τ => Context P (m + (m + 1)) (n + n) τ) 12 := by
  have h1 : 1 < B := by omega
  have hm : m < B := by omega
  have hn : n < B := by omega
  have hm1 : m + 1 < B := by omega
  have hr : m + (m + 1) < B := by omega
  have hs : n + n < B := by omega
  have hbase : Spec B (fun σ => σ.vars "source.m" = m ∧ σ.vars "source.n" = n) unbounded
      (fun _ τ => τ.vars "system.m" = m + (m + 1) ∧ τ.vars "system.n" = n + n) 12 := by
    rintro σ ⟨hσm, hσn⟩
    run_vcg
    all_goals simp_all
  intro σ hσ
  obtain ⟨τ, hr, hτ⟩ := hbase σ ⟨hσ.2.2.2.1, hσ.2.2.2.2⟩
  refine ⟨τ, hr, data_frame hr P hσ ?_ ?_, hτ⟩
  · intro a ha; simp [RamCertificateSource.fields] at ha; rcases ha with rfl | rfl <;> decide
  · intro a ha t ht; change a ++ t ∉ ([] : List String); simp

end Lax109476Proofs.RamCertificateMetadata

import Lax109476Proofs.CertificateSearch

namespace Lax109476Proofs.CertificateFamilyPrograms

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding IntegerCertificates CertificateSystems IndexedPointRecovery CertificateSearch

def optimal {m n : ℕ} (P : Program ℤ m n) : Program ℤ (m + (n + 2)) (n + m) :=
  reindexProgram (pairMatrix P) (pairBound P) (pairRows m n) finSumFinEquiv

def infeasible {m n : ℕ} (P : Program ℤ m n) : Program ℤ (n + 1) m :=
  reindexProgram (farkasMatrix P) farkasBound (farkasRows n) (Equiv.refl _)

def unbounded {m n : ℕ} (P : Program ℤ m n) : Program ℤ (m + (m + 1)) (n + n) :=
  reindexProgram (rayMatrix P) (rayBound P) (rayRows m) finSumFinEquiv

theorem reindex_feasible {κ ι : Type*} [Fintype ι] {r s : ℕ} (A : κ → ι → ℤ) (b : κ → ℤ)
    (er : κ ≃ Fin r) (ec : ι ≃ Fin s) (x : Fin s → ℚ)
    (hx : PrimalFeasible (rationalProgram (reindexProgram A b er ec)) x) :
    NonnegativeFeasible A b (fun j => x (ec j)) := by
  refine ⟨fun j => hx.1 _, fun i => ?_⟩
  have hr := hx.2 (er i)
  rw [reindex_row] at hr
  simpa [rationalProgram, reindexProgram] using hr

theorem reindex_exists {κ ι : Type*} [Fintype ι] {r s : ℕ} (A : κ → ι → ℤ) (b : κ → ℤ)
    (er : κ ≃ Fin r) (ec : ι ≃ Fin s) (hf : ∃ x, NonnegativeFeasible A b x) :
    IsFeasible (toReal (rationalProgram (reindexProgram A b er ec))) := by
  obtain ⟨x, hx⟩ := hf
  let z : Fin s → ℚ := fun j => x (ec.symm j)
  have hz : PrimalFeasible (rationalProgram (reindexProgram A b er ec)) z := by
    refine ⟨fun j => hx.1 _, fun i => ?_⟩
    have hr := hx.2 (er.symm i)
    have he := reindex_row A b er ec z (er.symm i)
    rw [Equiv.apply_symm_apply] at he
    rw [he]
    simpa [z, rationalProgram, reindexProgram] using hr
  exact ⟨realVector z, RationalFeasibility.cast_feasible _ _ hz⟩

theorem optimal_valid {m n : ℕ} (P : Program ℤ m n) (x : Fin (n + m) → ℚ)
    (hx : PrimalFeasible (rationalProgram (optimal P)) x) :
    IsValidCertificate (rationalProgram P)
      (.optimal (fun j => x (Fin.castAdd m j)) (fun i => x (Fin.natAdd n i))) := by
  have h := pair_valid P (fun j => x (finSumFinEquiv j))
    (reindex_feasible (pairMatrix P) (pairBound P) (pairRows m n) finSumFinEquiv x hx)
  simpa [finSumFinEquiv] using h

theorem infeasible_valid {m n : ℕ} (P : Program ℤ m n) (x : Fin m → ℚ)
    (hx : PrimalFeasible (rationalProgram (infeasible P)) x) :
    IsValidCertificate (rationalProgram P) (.infeasible x) :=
  farkas_valid P x (reindex_feasible (farkasMatrix P) farkasBound (farkasRows n) (Equiv.refl _) x hx)

theorem unbounded_valid {m n : ℕ} (P : Program ℤ m n) (x : Fin (n + n) → ℚ)
    (hx : PrimalFeasible (rationalProgram (unbounded P)) x) :
    IsValidCertificate (rationalProgram P)
      (.unbounded (fun j => x (Fin.castAdd n j)) (fun j => x (Fin.natAdd n j))) := by
  have h := ray_valid P (fun j => x (finSumFinEquiv j))
    (reindex_feasible (rayMatrix P) (rayBound P) (rayRows m) finSumFinEquiv x hx)
  simpa [finSumFinEquiv] using h

theorem some_family_feasible {m n : ℕ} (P : Program ℤ m n) (H : ℕ) (hH : 1 ≤ H)
    (hA : ∀ i j, (P.A i j).natAbs ≤ H) (hb : ∀ i, (P.b i).natAbs ≤ H) :
    IsFeasible (toReal (rationalProgram (optimal P))) ∨
      IsFeasible (toReal (rationalProgram (infeasible P))) ∨
        IsFeasible (toReal (rationalProgram (unbounded P))) := by
  obtain ⟨cert, hv⟩ := Lax109476.CertificateExistence.exists_valid_certificate m n (rationalProgram P)
  cases cert with
  | optimal x y => exact Or.inl (reindex_exists _ _ _ _ (pair_feasible P x y hv))
  | infeasible y => exact Or.inr (Or.inl (reindex_exists _ _ _ _ (farkas_feasible P H hH hA hb y hv)))
  | unbounded x d => exact Or.inr (Or.inr (reindex_exists _ _ _ _ (ray_feasible P x d hv)))

end Lax109476Proofs.CertificateFamilyPrograms

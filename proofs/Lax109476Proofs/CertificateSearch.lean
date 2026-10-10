import Lax109476Proofs.CertificateSystems

open scoped BigOperators

namespace Lax109476Proofs.CertificateSearch

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.FarkasCertificate Lax109476.RecessionDirection
open IntegerEncoding IntegerCertificates CertificateSystems

def unitFin : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv _ := rfl
  right_inv _ := Subsingleton.elim _ _

def pairRows (m n : ℕ) : (Fin m ⊕ (Fin n ⊕ Bool)) ≃ Fin (m + (n + 2)) :=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.sumCongr (Equiv.refl _) finTwoEquiv.symm).trans
    finSumFinEquiv)).trans finSumFinEquiv

def rayRows (m : ℕ) : (Fin m ⊕ (Fin m ⊕ Unit)) ≃ Fin (m + (m + 1)) :=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.sumCongr (Equiv.refl _) unitFin).trans
    finSumFinEquiv)).trans finSumFinEquiv

def farkasRows (n : ℕ) : (Fin n ⊕ Unit) ≃ Fin (n + 1) :=
  (Equiv.sumCongr (Equiv.refl _) unitFin).trans finSumFinEquiv

instance valid_decidable {m n : ℕ} (P : Program ℚ m n) (cert : Certificate m n) :
    Decidable (IsValidCertificate P cert) := by
  cases cert <;> unfold IsValidCertificate PrimalFeasible DualFeasible
    IsInfeasibilityCertificate IsImprovingDirection <;> infer_instance

def optimalCandidate {m n : ℕ} (P : Program ℤ m n) (H : ℕ) : Option (Certificate m n) :=
  (IndexedPointRecovery.point (pairMatrix P) (pairBound P) (pairRows m n) finSumFinEquiv H).map
    (fun z => .optimal (fun j => z (.inl j)) (fun i => z (.inr i)))

def infeasibleCandidate {m n : ℕ} (P : Program ℤ m n) (H : ℕ) : Option (Certificate m n) :=
  (IndexedPointRecovery.point (farkasMatrix P) farkasBound (farkasRows n) (Equiv.refl _) H).map
    Certificate.infeasible

def unboundedCandidate {m n : ℕ} (P : Program ℤ m n) (H : ℕ) : Option (Certificate m n) :=
  (IndexedPointRecovery.point (rayMatrix P) (rayBound P) (rayRows m) finSumFinEquiv H).map
    (fun z => .unbounded (fun j => z (.inl j)) (fun j => z (.inr j)))

def candidates {m n : ℕ} (P : Program ℤ m n) (H : ℕ) : List (Certificate m n) :=
  (optimalCandidate P H).toList ++ (infeasibleCandidate P H).toList ++ (unboundedCandidate P H).toList

def pickValid {m n : ℕ} (P : Program ℚ m n) (candidate : Option (Certificate m n))
    (fallback : Unit → Option (Certificate m n)) : Option (Certificate m n) :=
  match candidate with
  | none => fallback ()
  | some cert =>
    match decide (IsValidCertificate P cert) with
    | true => some cert
    | false => fallback ()

/-- Try certificate systems in order and stop at the first exact valid
certificate. Later auxiliary systems are computed only if needed. -/
def solveInteger {m n : ℕ} (P : Program ℤ m n) (H : ℕ) : Option (Certificate m n) :=
  pickValid (rationalProgram P) (optimalCandidate P H) (fun _ =>
    pickValid (rationalProgram P) (infeasibleCandidate P H) (fun _ =>
      pickValid (rationalProgram P) (unboundedCandidate P H) (fun _ => none)))

theorem solveInteger_eq_find {m n : ℕ} (P : Program ℤ m n) (H : ℕ) :
    solveInteger P H =
      (candidates P H).find? (fun cert => decide (IsValidCertificate (rationalProgram P) cert)) := by
  unfold solveInteger candidates
  cases optimalCandidate P H <;> cases infeasibleCandidate P H <;>
    cases unboundedCandidate P H <;> simp [pickValid, List.find?_cons]
  all_goals split <;> simp_all
  all_goals rfl

theorem solveInteger_valid {m n : ℕ} (P : Program ℤ m n) (H : ℕ) (cert : Certificate m n)
    (h : solveInteger P H = some cert) : IsValidCertificate (rationalProgram P) cert := by
  rw [solveInteger_eq_find] at h
  have hp : decide (IsValidCertificate (rationalProgram P) cert) = true :=
    List.find?_some (p := fun cert => decide (IsValidCertificate (rationalProgram P) cert)) h
  exact of_decide_eq_true hp

theorem pair_bounds {m n : ℕ} (P : Program ℤ m n) (H : ℕ)
    (hA : ∀ i j, (P.A i j).natAbs ≤ H) (hb : ∀ i, (P.b i).natAbs ≤ H)
    (hc : ∀ j, (P.c j).natAbs ≤ H) :
    (∀ i j, (pairMatrix P i j).natAbs ≤ H) ∧ ∀ i, (pairBound P i).natAbs ≤ H := by
  constructor
  · intro i j
    cases i with
    | inl i => cases j <;> simp [pairMatrix, hA]
    | inr i =>
      cases i with
      | inl k => cases j <;> simp [pairMatrix, hA]
      | inr v => cases v <;> cases j <;> simp [pairMatrix, hb, hc]
  · intro i
    cases i with
    | inl i => exact hb i
    | inr i => cases i <;> simp [pairBound, hc]

theorem optimalCandidate_complete {m n : ℕ} (P : Program ℤ m n) (H : ℕ) (hH : 1 ≤ H)
    (hA : ∀ i j, (P.A i j).natAbs ≤ H) (hb : ∀ i, (P.b i).natAbs ≤ H)
    (hc : ∀ j, (P.c j).natAbs ≤ H) (x : Fin n → ℚ) (y : Fin m → ℚ)
    (hv : IsValidCertificate (rationalProgram P) (.optimal x y)) :
    ∃ cert, optimalCandidate P H = some cert ∧ IsValidCertificate (rationalProgram P) cert := by
  obtain ⟨hmat, hbound⟩ := pair_bounds P H hA hb hc
  obtain ⟨w, he, hwp, hwr⟩ := IndexedPointRecovery.point_correct (pairMatrix P) (pairBound P)
    (pairRows m n) finSumFinEquiv H hH hmat hbound (pair_feasible P x y hv)
  refine ⟨.optimal (fun j => w (.inl j)) (fun i => w (.inr i)), ?_, pair_valid P w ⟨hwp, hwr⟩⟩
  simp [optimalCandidate, he]

theorem infeasibleCandidate_complete {m n : ℕ} (P : Program ℤ m n) (H : ℕ) (hH : 1 ≤ H)
    (hA : ∀ i j, (P.A i j).natAbs ≤ H) (hb : ∀ i, (P.b i).natAbs ≤ H)
    (y : Fin m → ℚ) (hv : IsValidCertificate (rationalProgram P) (.infeasible y)) :
    ∃ cert, infeasibleCandidate P H = some cert ∧ IsValidCertificate (rationalProgram P) cert := by
  have hmat : ∀ i j, (farkasMatrix P i j).natAbs ≤ H := by
    intro i j
    cases i <;> simp [farkasMatrix, hA, hb]
  have hbound : ∀ i : Fin n ⊕ Unit, (farkasBound i).natAbs ≤ H := by
    intro i
    cases i <;> simp [farkasBound, hH]
  obtain ⟨w, he, hwp, hwr⟩ := IndexedPointRecovery.point_correct (farkasMatrix P) farkasBound
    (farkasRows n) (Equiv.refl _) H hH hmat hbound (farkas_feasible P H hH hA hb y hv)
  refine ⟨.infeasible w, ?_, farkas_valid P w ⟨hwp, hwr⟩⟩
  simp [infeasibleCandidate, he]

theorem unboundedCandidate_complete {m n : ℕ} (P : Program ℤ m n) (H : ℕ) (hH : 1 ≤ H)
    (hA : ∀ i j, (P.A i j).natAbs ≤ H) (hb : ∀ i, (P.b i).natAbs ≤ H)
    (hc : ∀ j, (P.c j).natAbs ≤ H) (x d : Fin n → ℚ)
    (hv : IsValidCertificate (rationalProgram P) (.unbounded x d)) :
    ∃ cert, unboundedCandidate P H = some cert ∧ IsValidCertificate (rationalProgram P) cert := by
  have hmat : ∀ i j, (rayMatrix P i j).natAbs ≤ H := by
    intro i j
    cases i with
    | inl i => cases j <;> simp [rayMatrix, hA]
    | inr i =>
      cases i with
      | inl i => cases j <;> simp [rayMatrix, hA]
      | inr _ => cases j <;> simp [rayMatrix, hc]
  have hbound : ∀ i, (rayBound P i).natAbs ≤ H := by
    intro i
    cases i with
    | inl i => exact hb i
    | inr i => cases i <;> simp [rayBound, hH]
  obtain ⟨w, he, hwp, hwr⟩ := IndexedPointRecovery.point_correct (rayMatrix P) (rayBound P)
    (rayRows m) finSumFinEquiv H hH hmat hbound (ray_feasible P x d hv)
  refine ⟨.unbounded (fun j => w (.inl j)) (fun j => w (.inr j)), ?_, ray_valid P w ⟨hwp, hwr⟩⟩
  simp [unboundedCandidate, he]

theorem solveInteger_exists {m n : ℕ} (P : Program ℤ m n) (H : ℕ) (hH : 1 ≤ H)
    (hA : ∀ i j, (P.A i j).natAbs ≤ H) (hb : ∀ i, (P.b i).natAbs ≤ H)
    (hc : ∀ j, (P.c j).natAbs ≤ H) :
    ∃ cert, solveInteger P H = some cert ∧ IsValidCertificate (rationalProgram P) cert := by
  obtain ⟨cert₀, hv₀⟩ := Lax109476.CertificateExistence.exists_valid_certificate m n (rationalProgram P)
  have hex : ∃ cert ∈ candidates P H, IsValidCertificate (rationalProgram P) cert := by
    cases cert₀ with
    | optimal x y =>
      obtain ⟨cert, he, hv⟩ := optimalCandidate_complete P H hH hA hb hc x y hv₀
      exact ⟨cert, by simp [candidates, he], hv⟩
    | infeasible y =>
      obtain ⟨cert, he, hv⟩ := infeasibleCandidate_complete P H hH hA hb y hv₀
      exact ⟨cert, by simp [candidates, he], hv⟩
    | unbounded x d =>
      obtain ⟨cert, he, hv⟩ := unboundedCandidate_complete P H hH hA hb hc x d hv₀
      exact ⟨cert, by simp [candidates, he], hv⟩
  have hne : solveInteger P H ≠ none := by
    intro hn
    rw [solveInteger_eq_find] at hn
    obtain ⟨cert, hm, hv⟩ := hex
    have hbad := List.find?_eq_none.mp hn cert hm
    exact hbad (by simpa using hv)
  obtain ⟨cert, he⟩ := Option.ne_none_iff_exists'.mp hne
  exact ⟨cert, he, solveInteger_valid P H cert he⟩

def solve {m n : ℕ} (P : Program ℚ m n) : Option (Certificate m n) :=
  solveInteger (integerProgram P) (2 ^ (2 * Lax759944.BinaryWordEncoding.bitSize
    (Lax109476.RationalEncoding.encodeProgram P)))

/-- The computable rational solver always returns an exact valid certificate.
This is functional correctness; RAM execution and runtime are separate obligations. -/
theorem solve_exists {m n : ℕ} (P : Program ℚ m n) :
    ∃ cert, solve P = some cert ∧ IsValidCertificate P cert := by
  let H := 2 ^ (2 * Lax759944.BinaryWordEncoding.bitSize (Lax109476.RationalEncoding.encodeProgram P))
  have hH : 1 ≤ H := by
    have hp : 0 < H := by dsimp [H]; positivity
    omega
  obtain ⟨hA, hb, hc⟩ := integerProgram_bounds P
  obtain ⟨cert, he, hv⟩ := solveInteger_exists (integerProgram P) H hH hA hb hc
  refine ⟨cert, he, ?_⟩
  rw [integerProgram_eq_scaled] at hv
  have hs : 0 < (programDenominator P : ℚ) := by
    exact_mod_cast RationalSizeBounds.commonDenominator_pos (EncodingSize.programData P)
  exact (certificate_scaled P _ hs cert).mp hv

end Lax109476Proofs.CertificateSearch

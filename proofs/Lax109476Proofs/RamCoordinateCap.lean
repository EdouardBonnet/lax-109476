import Lax109476Proofs.RamNaturalPower
import Lax109476Proofs.RamFrame
import Lax109476Proofs.IntegerCertificates

namespace Lax109476Proofs.RamCoordinateCap

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamNaturalPower RamFrame IntegerCertificates

def magnitude (m n H : ℕ) : ℕ :=
  let K := 2 * (m + n) + 2
  let a := K * H * H + 1
  m + n + H + K + K * H * H + a + K.factorial + a ^ K + coordinateCap m n H + 10

def prepareCap : Com := .seq
  (.assign "cap.k" (.add (.mul (.lit 2) (.add (.var "query.m") (.var "query.n"))) (.lit 2)))
  (.seq (.assign "factorial.n" (.var "cap.k"))
    (.seq factorial (.seq (.assign "cap.factorial" (.var "factorial.value"))
      (.seq (.assign "power.base" (.add (.mul (.mul (.var "cap.k") (.var "cap.H"))
        (.var "cap.H")) (.lit 1)))
        (.seq (.assign "power.exponent" (.var "cap.k"))
          (.seq power (.assign "cap.value" (.mul (.var "cap.factorial") (.var "power.value")))))))))

set_option maxHeartbeats 600000 in
theorem prepareCap_spec (B m n H : ℕ) (hB : magnitude m n H < B) :
    Spec B (fun σ => σ.vars "query.m" = m ∧ σ.vars "query.n" = n ∧ σ.vars "cap.H" = H)
      prepareCap
      (fun _ τ => τ.vars "cap.value" = coordinateCap m n H ∧ τ.vars "cap.H" = H ∧
        τ.vars "query.m" = m ∧ τ.vars "query.n" = n)
      (24 * (2 * (m + n) + 2) + 42) := by
  let K := 2 * (m + n) + 2
  let a := K * H * H + 1
  have hmB : m < B := by dsimp [magnitude] at hB; omega
  have hnB : n < B := by dsimp [magnitude] at hB; omega
  have hHB : H < B := by dsimp [magnitude] at hB; omega
  have hKB : K < B := by dsimp [magnitude, K] at hB ⊢; omega
  have haB : a < B := by dsimp [magnitude, K, a] at hB ⊢; omega
  have hfB : K.factorial < B := by dsimp [magnitude, K] at hB ⊢; omega
  have hpB : a ^ K < B := by dsimp [magnitude, K, a] at hB ⊢; omega
  have hcB : coordinateCap m n H < B := by dsimp [magnitude] at hB; omega
  have h1 : 1 < B := by dsimp [magnitude] at hB; omega
  have h2 : 2 < B := by dsimp [magnitude] at hB; omega
  have hsum : m + n < B := by dsimp [K] at hKB; omega
  have hdouble : 2 * (m + n) < B := by dsimp [K] at hKB; omega
  have hkhh : K * H * H < B := by dsimp [a] at haB; omega
  have hkh : K * H < B := by
    by_cases hH : H = 0
    · simp [hH]; omega
    · have hm := Nat.le_mul_of_pos_right (K * H) (by omega : 0 < H)
      exact hm.trans_lt hkhh
  have hfactorial := spec_with_fields ["cap.k", "cap.H", "query.m", "query.n"]
    (factorial_spec B K hKB hfB)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> decide) (by rfl)
  have hpower := spec_with_fields ["cap.k", "cap.H", "cap.factorial", "query.m", "query.n"]
    (power_spec B a K (by dsimp [a]; omega) haB hKB hpB)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide) (by rfl)
  have hc : coordinateCap m n H = K.factorial * a ^ K := by
    simp only [coordinateCap, K, a, pow_two, Nat.mul_assoc]
  rintro σ ⟨hσm, hσn, hσH⟩
  dsimp only [K] at hfactorial hpower hfB hpB
  run_vcg [hfactorial, hpower]
  all_goals clear hfactorial hpower
  all_goals simp_all [FieldsAgree, K, a, hc, Nat.mul_assoc]

end Lax109476Proofs.RamCoordinateCap

import Lax109476Proofs.RamCoordinateCap

namespace Lax109476Proofs.RamCoordinateCapBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open IntegerCertificates RationalSizeBounds RamCoordinateCap

theorem magnitude_bound (m n H : ℕ) (hH : 1 ≤ H) :
    magnitude m n H ≤ m + n + 7 * coordinateCap m n H + 10 := by
  let K := 2 * (m + n) + 2
  let a := K * H * H + 1
  let F := K.factorial
  let V := a ^ K
  let C := coordinateCap m n H
  have hK : 0 < K := by dsimp [K]; omega
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hV : 0 < V := pow_pos (by omega : 0 < a) K
  have hF : 0 < F := Nat.factorial_pos K
  have hC : C = F * V := by simp only [C, coordinateCap, K, F, V, a, pow_two, Nat.mul_assoc]
  have hFC : F ≤ C := by rw [hC]; exact Nat.le_mul_of_pos_right _ hV
  have hVC : V ≤ C := by rw [hC]; exact Nat.le_mul_of_pos_left _ hF
  have haV : a ≤ V := le_self_pow ha (by omega : K ≠ 0)
  have haC := haV.trans hVC
  have hKC : K ≤ C := (Nat.self_le_factorial K).trans hFC
  have hprod : K * H * H ≤ C := (by dsimp [a] at haC; omega)
  have hHC : H ≤ C := (Nat.le_mul_of_pos_left H (Nat.mul_pos hK (by omega))).trans hprod
  change m + n + H + K + K * H * H + a + F + V + C + 10 ≤ m + n + 7 * C + 10
  omega

def wordWidth (S : ℕ) : ℕ := 32 * (S + 1) ^ 2 + S + 16

theorem magnitude_fits (m n S w : ℕ) (hdim : m + n ≤ S) (hw : wordWidth S ≤ w) :
    magnitude m n (2 ^ (2 * S)) < 2 ^ w := by
  let Q := 32 * (S + 1) ^ 2
  have hCsize : (coordinateCap m n (2 ^ (2 * S))).size ≤ Q :=
    certificate_cap_size (2 * (m + n) + 2) S (by omega)
  have hC : coordinateCap m n (2 ^ (2 * S)) < 2 ^ Q :=
    (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) hCsize)
  have hSQ : S + 10 ≤ Q := by dsimp [Q]; nlinarith
  have hS : S + 10 < 2 ^ Q := (Nat.lt_two_pow_self (n := S + 10)).trans_le
    (Nat.pow_le_pow_right (by decide) hSQ)
  have hmag := magnitude_bound m n (2 ^ (2 * S)) (Nat.one_le_pow _ _ (by decide))
  have hlarge : magnitude m n (2 ^ (2 * S)) < 2 ^ (Q + 3) := by
    rw [pow_add]
    norm_num
    omega
  have hQw : Q + 3 ≤ w := by dsimp [wordWidth, Q] at hw ⊢; omega
  exact hlarge.trans_le (Nat.pow_le_pow_right (by decide) hQw)

theorem prepareCap_bounded_spec (m n S w : ℕ) (hdim : m + n ≤ S) (hw : wordWidth S ≤ w) :
    Spec (2 ^ w) (fun σ => σ.vars "query.m" = m ∧ σ.vars "query.n" = n ∧
        σ.vars "cap.H" = 2 ^ (2 * S)) prepareCap
      (fun _ τ => τ.vars "cap.value" = coordinateCap m n (2 ^ (2 * S)) ∧
        τ.vars "cap.H" = 2 ^ (2 * S) ∧ τ.vars "query.m" = m ∧ τ.vars "query.n" = n)
      (48 * S + 90) := by
  exact (prepareCap_spec (2 ^ w) m n (2 ^ (2 * S)) (magnitude_fits m n S w hdim hw)).mono (by omega)

end Lax109476Proofs.RamCoordinateCapBounds

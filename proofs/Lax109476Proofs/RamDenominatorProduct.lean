import Lax109476Proofs.RamReadBlock

namespace Lax109476Proofs.RamDenominatorProduct

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays

def prefixProduct {n : ℕ} (v : Fin n → ℚ) (k : ℕ) : ℕ :=
  ((List.ofFn fun j => (v j).den).take k).prod

def product {n : ℕ} (v : Fin n → ℚ) : ℕ := (List.ofFn fun j => (v j).den).prod

theorem prefix_zero {n : ℕ} (v : Fin n → ℚ) : prefixProduct v 0 = 1 := rfl

theorem prefix_done {n : ℕ} (v : Fin n → ℚ) : prefixProduct v n = product v := by
  unfold prefixProduct product
  rw [show (List.ofFn fun j => (v j).den).take n = List.ofFn (fun j => (v j).den) from
    by simpa only [List.length_ofFn] using List.take_length (l := List.ofFn fun j => (v j).den)]

theorem prefix_step {n : ℕ} (v : Fin n → ℚ) (i : Fin n) :
    prefixProduct v (i.val + 1) = prefixProduct v i.val * (v i).den := by
  have hi : i.val < (List.ofFn fun j => (v j).den).length := by simp
  unfold prefixProduct
  rw [← List.take_concat_get hi]
  simp [List.concat_eq_append, List.prod_append]

theorem positive_list_product (xs : List ℕ) (hx : ∀ a ∈ xs, 0 < a) : 0 < xs.prod := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.prod_cons]
    exact Nat.mul_pos (hx a (by simp)) (ih (fun b hb => hx b (by simp [hb])))

theorem prefix_pos {n : ℕ} (v : Fin n → ℚ) (k : ℕ) : 0 < prefixProduct v k := by
  apply positive_list_product
  intro a ha
  have hh := List.mem_of_mem_take ha
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hh
  rw [← hi]
  exact (v i).den_pos

theorem prefix_le {n : ℕ} (v : Fin n → ℚ) (k : ℕ) : prefixProduct v k ≤ product v := by
  have hp : 0 < ((List.ofFn fun j => (v j).den).drop k).prod := by
    apply positive_list_product
    intro a ha
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp (List.mem_of_mem_drop ha)
    rw [← hi]
    exact (v i).den_pos
  have he : prefixProduct v k * ((List.ofFn fun j => (v j).den).drop k).prod = product v := by
    rw [prefixProduct, ← List.prod_append, List.take_append_drop]
    rfl
  rw [← he]
  exact Nat.le_mul_of_pos_right _ hp

def Invariant (a : String) {n : ℕ} (v : Fin n → ℚ) (D : ℕ) (σ : Env) : Prop :=
  Represents a (List.ofFn v) σ ∧ σ.vars "den.value" = D * prefixProduct v (σ.vars "den.i") ∧
    σ.vars "den.i" ≤ n ∧ σ.vars "vec.n" = n

def productStep (a : String) : Com := .seq
  (.assign "den.value" (.mul (.var "den.value") (.get (a ++ ".d") (.var "den.i"))))
  (.assign "den.i" (.add (.var "den.i") (.lit 1)))

theorem productStep_spec (B D n : ℕ) (a : String) (v : Fin n → ℚ)
    (hD : 0 < D) (hnB : n < B) (hprod : D * product v < B) :
    Spec B (fun σ => Invariant a v D σ ∧ σ.vars "den.i" < n) (productStep a)
      (fun σ τ => Invariant a v D τ ∧ τ.vars "den.i" = σ.vars "den.i" + 1) 9 := by
  rintro σ ⟨⟨hσa, hσp, hσiN, hσn⟩, hσi⟩
  let i : Fin n := ⟨σ.vars "den.i", hσi⟩
  have h1 : 1 < B := by
    have hp : 0 < product v := by simpa only [prefix_done] using prefix_pos v n
    have hm := Nat.mul_pos hD hp
    have hn : 0 < n := by omega
    omega
  have hiB : i.val < B := i.isLt.trans hnB
  have hcurB : D * prefixProduct v i.val < B :=
    (Nat.mul_le_mul_left D (prefix_le v i.val)).trans_lt hprod
  have hnextB : D * prefixProduct v (i.val + 1) < B :=
    (Nat.mul_le_mul_left D (prefix_le v (i.val + 1))).trans_lt hprod
  have hqle : (v i).den ≤ prefixProduct v (i.val + 1) := by
    rw [prefix_step]
    exact Nat.le_mul_of_pos_left _ (prefix_pos v i.val)
  have hqB : (v i).den < B := (hqle.trans ((prefix_le v (i.val + 1)).trans
    (Nat.le_mul_of_pos_left _ hD))).trans_lt hprod
  have hlen : i.val < (σ.arrs (a ++ ".d")).length := by rw [hσa.2.2]; simp
  have hget : (σ.arrs (a ++ ".d")).getD i.val 0 = (v i).den := by
    rw [hσa.2.2, map_getD _ _ _ (by simp)]
    simp
  have hvalB : σ.vars "den.value" < B := hσp ▸ hcurB
  have hmulB : σ.vars "den.value" * (σ.arrs (a ++ ".d")).getD i.val 0 < B := by
    rw [hσp, hget]
    change D * prefixProduct v i.val * (v i).den < B
    rw [Nat.mul_assoc, ← prefix_step v i]
    exact hnextB
  have hmul : σ.vars "den.value" * (σ.arrs (a ++ ".d")).getD i.val 0 =
      D * prefixProduct v (i.val + 1) := by
    rw [hσp, hget]
    change D * prefixProduct v i.val * (v i).den = D * prefixProduct v (i.val + 1)
    rw [Nat.mul_assoc, ← prefix_step v i]
  have hi1B : i.val + 1 < B := lt_of_le_of_lt i.isLt hnB
  run_vcg
  all_goals simp_all [Invariant, Represents, Env.setVar, i]

def productArray (a : String) : Com := .seq (.assign "den.i" (.lit 0))
  (.while (.lt (.var "den.i") (.var "vec.n")) (productStep a))

theorem productArray_spec (B D n : ℕ) (a : String) (v : Fin n → ℚ)
    (hD : 0 < D) (hnB : n < B) (hprod : D * product v < B) :
    Spec B (fun σ => Represents a (List.ofFn v) σ ∧ σ.vars "den.value" = D ∧ σ.vars "vec.n" = n)
      (productArray a)
      (fun _ τ => Represents a (List.ofFn v) τ ∧
        τ.vars "den.value" = D * product v ∧ τ.vars "vec.n" = n) (13 * n + 6) := by
  have hlo := Spec.forRangeZero "den.i" "vec.n" (Invariant a v D) n 9 hnB
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2) (productStep_spec B D n a v hD hnB hprod)
  refine (hlo.pre ?_).post ?_
  · rintro σ ⟨hσa, hσD, hσn⟩
    clear hlo
    simp_all [Invariant, prefix_zero, Represents, Env.setVar]
  · rintro σ τ _ ⟨hτ, hcounter⟩
    exact ⟨hτ.1, by simpa only [hcounter, prefix_done] using hτ.2.1, hτ.2.2.2⟩

end Lax109476Proofs.RamDenominatorProduct

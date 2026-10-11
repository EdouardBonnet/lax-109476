import Lax109476Proofs.RamEquationSelector

namespace Lax109476Proofs.RamEquationBoundSelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds RamEquationData EquationQueryEntries IntegerEncoding

def selectBound : Com := .seq RamEquationSelector.prepareRow
  (.seq (.assign "vec.i" (.var "query.baseRow"))
    (.seq (RamArrayResult.load "system.b") RamEquationSelector.applyRowSign))

set_option maxHeartbeats 1000000 in
theorem selectBound_spec (B M m n : ℕ) (P : Program ℤ m n) (i : Fin (m + m))
    (hM : 1 ≤ M) (hMB : M < B) (hB : m + m + n + 4 < B)
    (hb : ∀ r, (P.b r).natAbs ≤ M) :
    Spec B (fun σ => Data P σ ∧ σ.vars "query.row" = i.val)
      selectBound (fun _ τ => Data P τ ∧ FractionOutput (bound P i) τ) 33 := by
  have h1 : 1 < B := by omega
  have hm : m < B := by omega
  have hiB : i.val < B := i.isLt.trans (by omega)
  let r : Fin m := if hi : i.val < m then ⟨i.val, hi⟩ else ⟨i.val - m, by omega⟩
  have hrB : r.val < B := r.isLt.trans hm
  have hq : Height (P.b r : ℚ) M := ⟨by simpa using hb r, by simpa using hM⟩
  have hprepare : Spec B (fun σ => σ.vars "system.m" = m ∧ σ.vars "query.row" = i.val)
      RamEquationSelector.prepareRow (fun _ τ => τ.vars "query.baseRow" = r.val) 8 := by
    rintro σ ⟨hσm, hσrow⟩
    have hsub : i.val - m < B := (Nat.sub_le _ _).trans_lt hiB
    run_vcg
    all_goals simp_all [r]
    all_goals (try split_ifs) <;> (try simp_all) <;> omega
  rintro σ ⟨hσData, hσrow⟩
  obtain ⟨τ, hr₁, hτr⟩ := hprepare σ ⟨hσData.2.2.1, hσrow⟩
  have hτData := data_frame hr₁ P hσData
    (by intro a ha; simp [RamEquationData.fields] at ha; rcases ha with rfl | rfl <;> decide)
    (by intro a ha s hs; change a ++ s ∉ ([] : List String); simp)
  have hr₂ : Run B (.assign "vec.i" (.var "query.baseRow")) τ (τ.setVar "vec.i" r.val) 2 :=
    Run.assign (by simpa only [hτr] using (evalB_var (B := B) (σ := τ) (x := "query.baseRow") (hτr ▸ hrB)))
  have he : (List.ofFn (rationalProgram P).b)[r.val] = (P.b r : ℚ) := by simp [rationalProgram]
  obtain ⟨υ, hr₃, hυq⟩ := RamArrayResult.load_spec B "system.b" (List.ofFn (rationalProgram P).b) r.val
    (by simpa using r.isLt) h1 hrB (by rw [he]; exact hq.1.trans_lt hMB) (by rw [he]; exact hq.2.trans_lt hMB)
    (τ.setVar "vec.i" r.val) ⟨hτData.2.1, by simp⟩
  rw [he] at hυq
  have hυm := ((hr₂.seq hr₃).frame_var "system.m" (by decide)).trans hτData.2.2.1
  have hυrow := ((hr₁.seq (hr₂.seq hr₃)).frame_var "query.row" (by decide)).trans hσrow
  obtain ⟨ρ, hr₄, hρq⟩ := RamEquationSelector.applyRowSign_spec B m i.val (P.b r : ℚ) h1 hm hiB υ ⟨hυq, hυm, hυrow⟩
  have hr := hr₁.seq (hr₂.seq (hr₃.seq hr₄))
  refine ⟨ρ, hr, data_frame hr P hσData ?_ ?_, ?_⟩
  · intro a ha; simp [RamEquationData.fields] at ha; rcases ha with rfl | rfl <;> decide
  · intro a ha s hs; change a ++ s ∉ ([] : List String); simp
  · by_cases hi : i.val < m <;> simpa [bound, r, hi] using hρq

end Lax109476Proofs.RamEquationBoundSelector

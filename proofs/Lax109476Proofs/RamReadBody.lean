import Lax109476Proofs.RamReadBlock
import Lax109476Proofs.RamAdvanceState

namespace Lax109476Proofs.RamReadBody

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamReadArray RamReadBlock RamRationalArrays RamFrame RamEllipsoidStep RamAdvanceState

/-- Unconsumed words make the input malformed; a prior failure stays recorded. -/
def finishInput : Com := .ite (.eq (.var "input.remaining") (.lit 0)) .skip
  (.assign "input.valid" (.lit 0))

theorem finishInput_spec (B r v : ℕ) (hrB : r < B) :
    Spec B (fun σ => σ.vars "input.remaining" = r ∧ σ.vars "input.valid" = v)
      finishInput (fun _ τ => τ.vars "input.remaining" = r ∧
        τ.vars "input.valid" = if r = 0 then v else 0) 6 := by
  have h0 : 0 < B := by omega
  rintro σ ⟨hσr, hσv⟩
  run_vcg
  all_goals simp_all [Env.setVar]

def readBody : Com := .seq (readBlock "lp.A" "decode.count")
  (.seq (readBlock "lp.b" "lp.m") (.seq (readBlock "lp.c" "lp.n") finishInput))

def afterA (xs : List ℕ) (m n : ℕ) : List ℕ := xs.drop (3 * (m * n))
def flagA (xs : List ℕ) (v m n : ℕ) : ℕ := flag xs v (m * n)
def afterB (xs : List ℕ) (m n : ℕ) : List ℕ := (afterA xs m n).drop (3 * m)
def flagB (xs : List ℕ) (v m n : ℕ) : ℕ := flag (afterA xs m n) (flagA xs v m n) m
def afterC (xs : List ℕ) (m n : ℕ) : List ℕ := (afterB xs m n).drop (3 * n)
def flagC (xs : List ℕ) (v m n : ℕ) : ℕ := flag (afterB xs m n) (flagB xs v m n) n

def Result (B : ℕ) (xs : List ℕ) (v m n : ℕ) (σ : Env) : Prop :=
  Represents "lp.A" (List.ofFn (values xs v (m * n))) σ ∧
    Represents "lp.b" (List.ofFn (values (afterA xs m n) (flagA xs v m n) m)) σ ∧
    Represents "lp.c" (List.ofFn (values (afterB xs m n) (flagB xs v m n) n)) σ ∧
    σ.inp = afterC xs m n ∧ σ.vars "input.remaining" = (afterC xs m n).length ∧
    σ.vars "input.valid" = (if (afterC xs m n).length = 0 then flagC xs v m n else 0) ∧
    σ.InpBounded B ∧ σ.vars "lp.m" = m ∧ σ.vars "lp.n" = n ∧ σ.vars "decode.count" = m * n

theorem represents_frame {B K : ℕ} {c : Com} {σ τ : Env} (a : String) (qs : List ℚ)
    (hσ : Represents a qs σ) (hr : Run B c σ τ K)
    (ha : ∀ s ∈ [".s", ".n", ".d"], a ++ s ∉ c.warrs) : Represents a qs τ := by
  simpa only [Represents, hr.frame_arr (a ++ ".s") (ha ".s" (by simp)),
    hr.frame_arr (a ++ ".n") (ha ".n" (by simp)),
    hr.frame_arr (a ++ ".d") (ha ".d" (by simp))] using hσ

theorem readBody_spec (B M m n v : ℕ) (xs : List ℕ)
    (h2 : 2 < B) (hMB : M < B) (hM : 1 ≤ M) (hmB : m < B) (hnB : n < B)
    (hmnB : m * n < B) (hxB : xs.length < B) (hv : v ≤ 1)
    (hwords : ∀ z ∈ xs, z ≤ M) :
    Spec B (fun σ => Extents "lp.A" (m * n) σ ∧ Extents "lp.b" m σ ∧ Extents "lp.c" n σ ∧
        σ.inp = xs ∧ σ.vars "input.remaining" = xs.length ∧ σ.vars "input.valid" = v ∧
        σ.InpBounded B ∧ σ.vars "lp.m" = m ∧ σ.vars "lp.n" = n ∧ σ.vars "decode.count" = m * n)
      readBody (fun _ τ => Result B xs v m n τ)
      ((36 * M.size + 115) * (m * n + m + n) + 84) := by
  rintro σ ⟨hσA, hσb, hσc, hσinp, hσrem, hσvalid, hσbound, hσm, hσn, hσcount⟩
  obtain ⟨τ, hr₁, hτA, hτinp, hτrem, hτvalid, hτbound, hτfields, _⟩ :=
    readBlock_spec B M (m * n) v "lp.A" "decode.count" xs h2 hMB hM hmnB hxB hv hwords
      (by simp [fields]) σ
      ⟨hσA ".s" (by simp), hσA ".n" (by simp),
        hσA ".d" (by simp), hσinp, hσrem, hσvalid, hσbound, hσcount⟩
  have hτb := extents_of_run hr₁ "lp.b" m hσb
  have hτc := extents_of_run hr₁ "lp.c" n hσc
  have hxAB : (afterA xs m n).length < B := by dsimp [afterA]; simp only [List.length_drop]; omega
  have hwordsA : ∀ z ∈ afterA xs m n, z ≤ M :=
    fun z hz => hwords z (List.mem_of_mem_drop hz)
  have hvA : flagA xs v m n ≤ 1 := flag_le_one xs v (m * n) hv
  obtain ⟨υ, hr₂, hυb, hυinp, hυrem, hυvalid, hυbound, hυfields, harr₂⟩ :=
    readBlock_spec B M m (flagA xs v m n) "lp.b" "lp.m" (afterA xs m n)
      h2 hMB hM hmB hxAB hvA hwordsA (by simp [fields]) τ
      ⟨hτb ".s" (by simp), hτb ".n" (by simp),
        hτb ".d" (by simp), hτinp, hτrem, hτvalid, hτbound,
        (hτfields _ (by simp [fields])).trans hσm⟩
  have hυA : Represents "lp.A" (List.ofFn (values xs v (m * n))) υ := by
    simpa [Represents, harr₂ "lp.A.s" (by decide), harr₂ "lp.A.n" (by decide),
      harr₂ "lp.A.d" (by decide)] using hτA
  have hυc := extents_of_run hr₂ "lp.c" n hτc
  have hxBB : (afterB xs m n).length < B := by dsimp [afterB]; simp only [List.length_drop]; omega
  have hwordsB : ∀ z ∈ afterB xs m n, z ≤ M :=
    fun z hz => hwordsA z (List.mem_of_mem_drop hz)
  have hvB : flagB xs v m n ≤ 1 := flag_le_one _ _ m hvA
  obtain ⟨ξ, hr₃, hξc, hξinp, hξrem, hξvalid, hξbound, hξfields, harr₃⟩ :=
    readBlock_spec B M n (flagB xs v m n) "lp.c" "lp.n" (afterB xs m n)
      h2 hMB hM hnB hxBB hvB hwordsB (by simp [fields]) υ
      ⟨hυc ".s" (by simp), hυc ".n" (by simp),
        hυc ".d" (by simp), hυinp, hυrem, hυvalid, hυbound,
        (hυfields _ (by simp [fields])).trans ((hτfields _ (by simp [fields])).trans hσn)⟩
  have hξA : Represents "lp.A" (List.ofFn (values xs v (m * n))) ξ := by
    simpa [Represents, harr₃ "lp.A.s" (by decide), harr₃ "lp.A.n" (by decide),
      harr₃ "lp.A.d" (by decide)] using hυA
  have hξb : Represents "lp.b" (List.ofFn (values (afterA xs m n) (flagA xs v m n) m)) ξ := by
    simpa [Represents, harr₃ "lp.b.s" (by decide), harr₃ "lp.b.n" (by decide),
      harr₃ "lp.b.d" (by decide)] using hυb
  have hxCB : (afterC xs m n).length < B := by dsimp [afterC]; simp only [List.length_drop]; omega
  obtain ⟨ρ, hr₄, hρrem, hρvalid⟩ := finishInput_spec B (afterC xs m n).length (flagC xs v m n)
    hxCB ξ ⟨hξrem, hξvalid⟩
  have hrun := hr₁.seq (hr₂.seq (hr₃.seq hr₄))
  have hfields := fieldsAgree_trans fields σ τ ξ hτfields
    (fieldsAgree_trans fields τ υ ξ hυfields hξfields)
  refine ⟨ρ, hrun.mono (by simp only [Nat.mul_add]; omega), ⟨?_, ?_, ?_, ?_, hρrem,
    hρvalid, hrun.inpBounded hσbound, ?_, ?_, ?_⟩⟩
  · exact represents_frame _ _ hξA hr₄ (by decide)
  · exact represents_frame _ _ hξb hr₄ (by decide)
  · exact represents_frame _ _ hξc hr₄ (by decide)
  · exact (hr₄.frame_inp (by decide)).trans hξinp
  · exact (hr₄.frame_var "lp.m" (by decide)).trans ((hfields _ (by simp [fields])).trans hσm)
  · exact (hr₄.frame_var "lp.n" (by decide)).trans ((hfields _ (by simp [fields])).trans hσn)
  · exact (hr₄.frame_var "decode.count" (by decide)).trans ((hfields _ (by simp [fields])).trans hσcount)

theorem encodedResult_correct (B m n : ℕ) (P : Lax109476.LinearProgram.Program ℚ m n) (τ : Env)
    (hτ : Result B (WordDecoding.encodeRows P.A ++ Lax109476.RationalEncoding.encodeVector P.b ++
      Lax109476.RationalEncoding.encodeVector P.c) 1 m n τ) :
    Represents "lp.A" (RamMatrixStorage.flatten P.A) τ ∧
      Represents "lp.b" (List.ofFn P.b) τ ∧ Represents "lp.c" (List.ofFn P.c) τ ∧
      τ.inp = [] ∧ τ.vars "input.remaining" = 0 ∧ τ.vars "input.valid" = 1 ∧
      τ.InpBounded B ∧ τ.vars "lp.m" = m ∧ τ.vars "lp.n" = n ∧ τ.vars "decode.count" = m * n := by
  let xs := WordDecoding.encodeRows P.A ++ Lax109476.RationalEncoding.encodeVector P.b ++
    Lax109476.RationalEncoding.encodeVector P.c
  have ha : WordDecoding.readVector (m * n) xs =
      some ((fun k : Fin (m * n) => P.A k.divNat k.modNat),
        Lax109476.RationalEncoding.encodeVector P.b ++ Lax109476.RationalEncoding.encodeVector P.c) := by
    dsimp [xs]
    rw [List.append_assoc, RamReadMatrix.encodeRows_flat]
    exact WordDecoding.readVector_encode _ _ _
  have hb := WordDecoding.readVector_encode m P.b (Lax109476.RationalEncoding.encodeVector P.c)
  have hc := WordDecoding.readVector_encode n P.c []
  simp only [List.append_nil] at hc
  have hA := readVector_correct _ _ _ _ ha
  have hb' := readVector_correct _ _ _ _ hb
  have hc' := readVector_correct _ _ _ _ hc
  change Result B xs 1 m n τ at hτ
  dsimp only [Result, afterA, afterB, afterC, flagA, flagB, flagC] at hτ
  simp only [hA.1, hA.2.1, hA.2.2, hb'.1, hb'.2.1, hb'.2.2,
    hc'.1, hc'.2.1, hc'.2.2] at hτ
  simpa only [RamMatrixStorage.flatten, List.length_nil, if_true] using hτ

theorem readBody_valid_spec (B M m n : ℕ) (P : Lax109476.LinearProgram.Program ℚ m n)
    (h2 : 2 < B) (hMB : M < B) (hM : 1 ≤ M) (hmB : m < B) (hnB : n < B)
    (hmnB : m * n < B)
    (hxB : (WordDecoding.encodeRows P.A ++ Lax109476.RationalEncoding.encodeVector P.b ++
      Lax109476.RationalEncoding.encodeVector P.c).length < B)
    (hwords : ∀ z ∈ WordDecoding.encodeRows P.A ++ Lax109476.RationalEncoding.encodeVector P.b ++
      Lax109476.RationalEncoding.encodeVector P.c, z ≤ M) :
    Spec B (fun σ => Extents "lp.A" (m * n) σ ∧ Extents "lp.b" m σ ∧ Extents "lp.c" n σ ∧
        σ.inp = WordDecoding.encodeRows P.A ++ Lax109476.RationalEncoding.encodeVector P.b ++
          Lax109476.RationalEncoding.encodeVector P.c ∧
        σ.vars "input.remaining" = (WordDecoding.encodeRows P.A ++
          Lax109476.RationalEncoding.encodeVector P.b ++ Lax109476.RationalEncoding.encodeVector P.c).length ∧
        σ.vars "input.valid" = 1 ∧ σ.InpBounded B ∧
        σ.vars "lp.m" = m ∧ σ.vars "lp.n" = n ∧ σ.vars "decode.count" = m * n)
      readBody
      (fun _ τ => Represents "lp.A" (RamMatrixStorage.flatten P.A) τ ∧
        Represents "lp.b" (List.ofFn P.b) τ ∧ Represents "lp.c" (List.ofFn P.c) τ ∧
        τ.inp = [] ∧ τ.vars "input.remaining" = 0 ∧ τ.vars "input.valid" = 1 ∧
        τ.InpBounded B ∧ τ.vars "lp.m" = m ∧ τ.vars "lp.n" = n ∧ τ.vars "decode.count" = m * n)
      ((36 * M.size + 115) * (m * n + m + n) + 84) := by
  apply (readBody_spec B M m n 1 _ h2 hMB hM hmB hnB hmnB hxB (by decide) hwords).post
  intro σ τ hσ hτ
  exact encodedResult_correct B m n P τ hτ

end Lax109476Proofs.RamReadBody

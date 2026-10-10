import Lax109476Proofs.RamInput
import Lax109476Proofs.RamRational
import Lax109476Proofs.RamFrame
import Lax109476Proofs.WordDecoding

namespace Lax109476Proofs.RamReadFraction

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamInput RamRational RamArithmetic RamFrame

def validateFraction : Com := .ite (.lt (.var "rat.s") (.lit 2))
  (.ite (.lt (.lit 0) (.var "rat.d")) normalizeFraction (.assign "input.valid" (.lit 0)))
  (.assign "input.valid" (.lit 0))

def readRawFraction : Com := .seq (safeRead "rat.s") (.seq (safeRead "rat.n") (safeRead "rat.d"))

def readFraction : Com := .seq readRawFraction validateFraction

theorem readRawFraction_spec (B : ℕ) (xs : List ℕ) (v : ℕ)
    (h1 : 1 < B) (hxsB : xs.length < B) (hv : v ≤ 1) :
    Spec B (fun σ => σ.inp = xs ∧ σ.vars "input.remaining" = xs.length ∧
        σ.vars "input.valid" = v ∧ σ.InpBounded B)
      readRawFraction
      (fun _ τ => τ.vars "rat.s" = xs.headD 0 ∧ τ.vars "rat.n" = xs.tail.headD 0 ∧
        τ.vars "rat.d" = xs.tail.tail.headD 0 ∧ τ.inp = xs.drop 3 ∧
        τ.vars "input.remaining" = xs.length - 3 ∧
        τ.vars "input.valid" = (if xs.length < 3 then 0 else v) ∧ τ.InpBounded B) 27 := by
  rintro σ ⟨hσinp, hσrem, hσvalid, hσbound⟩
  obtain ⟨τ, hr₁, hτs, hτinp, hτrem, hτvalid⟩ :=
    safeRead_spec B "rat.s" xs v h1 hxsB hv (by decide) (by decide)
      σ ⟨hσinp, hσrem, hσvalid, hσbound⟩
  have hτvle : (if xs = [] then 0 else v) ≤ 1 := by split_ifs <;> omega
  have htailB : xs.tail.length < B := by simp only [List.length_tail]; omega
  obtain ⟨υ, hr₂, hυn, hυinp, hυrem, hυvalid⟩ :=
    safeRead_spec B "rat.n" xs.tail (if xs = [] then 0 else v) h1 htailB hτvle (by decide) (by decide)
      τ ⟨hτinp, by simpa using hτrem, hτvalid, hr₁.inpBounded hσbound⟩
  have hυs : υ.vars "rat.s" = xs.headD 0 := (hr₂.frame_var _ (by decide)).trans hτs
  have hυvle : (if xs.tail = [] then 0 else if xs = [] then 0 else v) ≤ 1 := by split_ifs <;> omega
  have htailtailB : xs.tail.tail.length < B := by simp only [List.length_tail]; omega
  obtain ⟨ξ, hr₃, hξd, hξinp, hξrem, hξvalid⟩ :=
    safeRead_spec B "rat.d" xs.tail.tail (if xs.tail = [] then 0 else if xs = [] then 0 else v)
      h1 htailtailB hυvle (by decide) (by decide) υ
      ⟨hυinp, by simpa using hυrem, hυvalid, (hr₁.seq hr₂).inpBounded hσbound⟩
  have hξs := (hr₃.frame_var "rat.s" (by decide)).trans hυs
  have hξn := (hr₃.frame_var "rat.n" (by decide)).trans hυn
  have hrun := hr₁.seq (hr₂.seq hr₃)
  refine ⟨ξ, hrun, hξs, hξn, hξd, ?_, ?_, ?_, hrun.inpBounded hσbound⟩
  · simpa only [← List.drop_one, List.drop_drop] using hξinp
  · simp only [List.length_tail] at hξrem
    omega
  · cases xs with
    | nil => simpa using hξvalid
    | cons s ys => cases ys with
      | nil => simpa using hξvalid
      | cons n zs => cases zs with
        | nil => simpa using hξvalid
        | cons d rest =>
          have hn : ¬rest.length + 1 + 1 + 1 < 3 := by omega
          simpa [hn] using hξvalid

theorem decoded_fractionValue (s n d : ℕ) :
    (WordDecoding.signedNumerator s n : ℚ) / d = fractionValue s n d := by
  simp only [WordDecoding.signedNumerator, fractionValue, Int.cast_ite, Int.cast_neg, Int.cast_natCast]
  split_ifs <;> rfl

theorem validateFraction_valid_spec (B s n d remaining v : ℕ) (h2 : 2 < B) (hs : s ≤ 1)
    (hn : n < B) (hd : d < B) (hdpos : 0 < d) :
    Spec B (fun σ => σ.vars "rat.s" = s ∧ σ.vars "rat.n" = n ∧ σ.vars "rat.d" = d ∧
        σ.vars "input.remaining" = remaining ∧ σ.vars "input.valid" = v)
      validateFraction
      (fun _ τ => FractionOutput (fractionValue s n d) τ ∧
        τ.vars "input.remaining" = remaining ∧ τ.vars "input.valid" = v)
      (36 * d.size + 24) := by
  have hsB : s < B := by omega
  have hnrm := spec_with_fields ["input.remaining", "input.valid"]
    (normalizeFraction_output_spec B s n d hs hn hd hdpos)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> decide)
    (by decide)
  rintro σ ⟨hσs, hσn, hσd, hσr, hσv⟩
  run_vcg [hnrm]
  all_goals clear hnrm
  all_goals simp_all [FieldsAgree]
  all_goals first | omega | (exfalso; omega)

theorem readFraction_valid_spec (B s n d : ℕ) (rest : List ℕ)
    (h2 : 2 < B) (hs : s ≤ 1) (hdpos : 0 < d) (hlen : 3 + rest.length < B) :
    Spec B (fun σ => σ.inp = s :: n :: d :: rest ∧
        σ.vars "input.remaining" = 3 + rest.length ∧ σ.vars "input.valid" = 1 ∧ σ.InpBounded B)
      readFraction
      (fun _ τ => FractionOutput (fractionValue s n d) τ ∧ τ.inp = rest ∧
        τ.vars "input.remaining" = rest.length ∧ τ.vars "input.valid" = 1 ∧ τ.InpBounded B)
      (36 * d.size + 51) := by
  rintro σ ⟨hinp, hrem, hvalid, hbound⟩
  have h1 : 1 < B := by omega
  have hnB : n < B := hbound _ (by rw [hinp]; simp)
  have hdB : d < B := hbound _ (by rw [hinp]; simp)
  obtain ⟨τ, hr₁, hτs, hτn, hτd, hτinp, hτrem, hτvalid, hτbound⟩ :=
    readRawFraction_spec B (s :: n :: d :: rest) 1 h1 (by simp only [List.length_cons]; omega)
      (by decide) σ ⟨hinp, by simp only [List.length_cons]; omega, hvalid, hbound⟩
  obtain ⟨υ, hr₂, hυq, hυrem, hυvalid⟩ := validateFraction_valid_spec B s n d rest.length 1
    h2 hs hnB hdB hdpos τ
    ⟨by simpa using hτs, by simpa using hτn, by simpa using hτd,
      by simp only [List.length_cons] at hτrem; omega,
      by simp only [List.length_cons] at hτvalid; split_ifs at hτvalid <;> omega⟩
  have hυinp : υ.inp = rest := (hr₂.frame_inp (by decide)).trans (by simpa using hτinp)
  exact ⟨υ, (hr₁.seq hr₂).mono (by omega), hυq, hυinp, hυrem, hυvalid, hr₂.inpBounded hτbound⟩

theorem validateFraction_spec (B s n d remaining v : ℕ) (h2 : 2 < B)
    (hsB : s < B) (hnB : n < B) (hdB : d < B) :
    Spec B (fun σ => σ.vars "rat.s" = s ∧ σ.vars "rat.n" = n ∧ σ.vars "rat.d" = d ∧
        σ.vars "input.remaining" = remaining ∧ σ.vars "input.valid" = v)
      validateFraction
      (fun _ τ => (s ≤ 1 ∧ 0 < d → FractionOutput (fractionValue s n d) τ) ∧
        τ.vars "input.remaining" = remaining ∧
        τ.vars "input.valid" = if s ≤ 1 ∧ 0 < d then v else 0)
      (36 * d.size + 24) := by
  by_cases hgood : s ≤ 1 ∧ 0 < d
  · apply (validateFraction_valid_spec B s n d remaining v h2 hgood.1 hnB hdB hgood.2).post
    intro σ τ hσ hτ
    exact ⟨fun _ => hτ.1, hτ.2.1, by simpa only [if_pos hgood] using hτ.2.2⟩
  · rintro σ ⟨hσs, hσn, hσd, hσr, hσv⟩
    have h0 : 0 < B := by omega
    have hz : Run B (.assign "input.valid" (.lit 0)) σ (σ.setVar "input.valid" 0) 2 :=
      Run.assign (evalB_lit h0)
    by_cases hs : s ≤ 1
    · have hd : d = 0 := by omega
      have ho : (Cond.lt (.var "rat.s") (.lit 2)).evalB B σ = some true := by
        simpa [hσs, hs] using evalB_condLt
          (evalB_var (B := B) (σ := σ) (x := "rat.s") (by rw [hσs]; exact hsB)) (evalB_lit h2)
      have hi : (Cond.lt (.lit 0) (.var "rat.d")).evalB B σ = some false := by
        simpa [hσd, hd] using evalB_condLt (evalB_lit h0)
          (evalB_var (B := B) (σ := σ) (x := "rat.d") (by rw [hσd]; exact hdB))
      have hr := Run.ite_true (d := Com.assign "input.valid" (.lit 0)) ho
        (Run.ite_false (c := normalizeFraction) hi hz)
      refine ⟨_, hr.mono (by simp only [Cond.size, Expr.size]; omega), ?_⟩
      simp [hgood, Env.setVar, hσr]
    · have ho : (Cond.lt (.var "rat.s") (.lit 2)).evalB B σ = some false := by
        simpa [hσs, show ¬s < 2 by omega] using evalB_condLt
          (evalB_var (B := B) (σ := σ) (x := "rat.s") (by rw [hσs]; exact hsB)) (evalB_lit h2)
      have hr := Run.ite_false (c := .ite (.lt (.lit 0) (.var "rat.d"))
        normalizeFraction (.assign "input.valid" (.lit 0))) ho hz
      refine ⟨_, hr.mono (by simp only [Cond.size, Expr.size]; omega), ?_⟩
      simp [hgood, Env.setVar, hσr]

theorem readRational_raw (xs : List ℕ) :
    WordDecoding.readRational xs =
      if xs.headD 0 ≤ 1 ∧ 0 < xs.tail.tail.headD 0 then
        some (fractionValue (xs.headD 0) (xs.tail.headD 0) (xs.tail.tail.headD 0), xs.drop 3)
      else none := by
  cases xs with
  | nil => simp [WordDecoding.readRational]
  | cons s ys => cases ys with
    | nil => simp [WordDecoding.readRational]
    | cons n zs => cases zs with
      | nil => simp [WordDecoding.readRational]
      | cons d rest => simp [WordDecoding.readRational, decoded_fractionValue]

theorem raw_den_positive_length (xs : List ℕ) (hd : 0 < xs.tail.tail.headD 0) :
    3 ≤ xs.length := by
  cases xs with
  | nil => simp at hd
  | cons s ys => cases ys with
    | nil => simp at hd
    | cons n zs => cases zs with
      | nil => simp at hd
      | cons d rest => simp only [List.length_cons]; omega

theorem headD_le (xs : List ℕ) (M : ℕ) (h : ∀ a ∈ xs, a ≤ M) : xs.headD 0 ≤ M := by
  cases xs with
  | nil => simp
  | cons a rest => exact h a (by simp)

/-- Validation is total, including truncated triples and noncanonical but
valid rational encodings. An earlier invalidity flag is never reset. -/
theorem readFraction_spec (B M : ℕ) (xs : List ℕ) (v : ℕ)
    (h2 : 2 < B) (hlen : xs.length < B) (hv : v ≤ 1)
    (hM : M < B) (hwords : ∀ a ∈ xs, a ≤ M) :
    Spec B (fun σ => σ.inp = xs ∧ σ.vars "input.remaining" = xs.length ∧
        σ.vars "input.valid" = v ∧ σ.InpBounded B)
      readFraction
      (fun _ τ => τ.inp = xs.drop 3 ∧ τ.vars "input.remaining" = xs.length - 3 ∧
        τ.vars "input.valid" = (if WordDecoding.readRational xs = none then 0 else v) ∧
        (∀ q rest, WordDecoding.readRational xs = some (q, rest) →
          FractionOutput q τ ∧ τ.inp = rest) ∧ τ.InpBounded B)
      (36 * M.size + 51) := by
  have hsM := headD_le xs M hwords
  have hnM := headD_le xs.tail M (fun a ha => hwords a (List.mem_of_mem_tail ha))
  have hdM := headD_le xs.tail.tail M
    (fun a ha => hwords a (List.mem_of_mem_tail (List.mem_of_mem_tail ha)))
  rintro σ ⟨hinp, hrem, hvalid, hbound⟩
  obtain ⟨τ, hr₁, hτs, hτn, hτd, hτinp, hτrem, hτvalid, hτbound⟩ :=
    readRawFraction_spec B xs v (by omega) hlen hv σ ⟨hinp, hrem, hvalid, hbound⟩
  obtain ⟨υ, hr₂, hυq, hυrem, hυvalid⟩ := validateFraction_spec B (xs.headD 0)
    (xs.tail.headD 0) (xs.tail.tail.headD 0) (xs.length - 3) (if xs.length < 3 then 0 else v)
    h2 (hsM.trans_lt hM) (hnM.trans_lt hM) (hdM.trans_lt hM)
    τ ⟨hτs, hτn, hτd, hτrem, hτvalid⟩
  have hυinp := (hr₂.frame_inp (by decide)).trans hτinp
  have hrun := hr₁.seq hr₂
  have hds : (xs.tail.tail.headD 0).size ≤ M.size := Nat.size_le_size hdM
  refine ⟨υ, hrun.mono (by omega), hυinp, hυrem, ?_, ?_, hr₂.inpBounded hτbound⟩
  · rw [readRational_raw]
    by_cases hg : xs.headD 0 ≤ 1 ∧ 0 < xs.tail.tail.headD 0
    · have hlong : ¬xs.length < 3 := by have := raw_den_positive_length xs hg.2; omega
      simpa only [if_pos hg, if_neg hlong, reduceCtorEq, if_false] using hυvalid
    · simpa only [if_neg hg, if_true] using hυvalid
  · intro q rest hdecode
    rw [readRational_raw] at hdecode
    split_ifs at hdecode with hg
    · have he := Option.some.inj hdecode
      have heq := Prod.mk.inj he
      exact ⟨by rw [← heq.1]; exact hυq hg, hυinp.trans heq.2⟩

def zeroResult : Com := .seq (.assign "rat.s" (.lit 0))
  (.seq (.assign "rat.n" (.lit 0)) (.assign "rat.d" (.lit 1)))

theorem zeroResult_spec (B : ℕ) (h1 : 1 < B) :
    Spec B (fun _ => True) zeroResult (fun _ τ => FractionOutput 0 τ) 6 := by
  run_vcg
  all_goals simp [FractionOutput, fractionValue]

def safeFraction : Com := .seq readFraction
  (.ite (.eq (.var "input.valid") (.lit 1)) .skip zeroResult)

def safeValue (xs : List ℕ) (v : ℕ) : ℚ :=
  if v = 1 then (WordDecoding.readRational xs).map Prod.fst |>.getD 0 else 0

/-- Failed reads still produce a canonical, bounded placeholder, so array
stores remain safe while the invalidity flag records the parse failure. -/
theorem safeFraction_spec (B M : ℕ) (xs : List ℕ) (v : ℕ)
    (h2 : 2 < B) (hlen : xs.length < B) (hv : v ≤ 1)
    (hM : M < B) (hwords : ∀ a ∈ xs, a ≤ M) :
    Spec B (fun σ => σ.inp = xs ∧ σ.vars "input.remaining" = xs.length ∧
        σ.vars "input.valid" = v ∧ σ.InpBounded B)
      safeFraction
      (fun _ τ => FractionOutput (safeValue xs v) τ ∧ τ.inp = xs.drop 3 ∧
        τ.vars "input.remaining" = xs.length - 3 ∧
        τ.vars "input.valid" = (if WordDecoding.readRational xs = none then 0 else v) ∧
        τ.InpBounded B)
      (36 * M.size + 61) := by
  intro σ hσ
  obtain ⟨τ, hr₁, hτinp, hτrem, hτvalid, hτq, hτbound⟩ :=
    readFraction_spec B M xs v h2 hlen hv hM hwords σ hσ
  have hflag : τ.vars "input.valid" ≤ 1 := by rw [hτvalid]; split_ifs <;> omega
  have h1 : 1 < B := by omega
  have hflagB := hflag.trans_lt h1
  by_cases hgood : τ.vars "input.valid" = 1
  · have hv1 : v = 1 := by rw [hτvalid] at hgood; split_ifs at hgood <;> omega
    have hdecode : WordDecoding.readRational xs ≠ none := by
      intro hh; simp [hh] at hτvalid; omega
    obtain ⟨⟨q, rest⟩, hsome⟩ := Option.ne_none_iff_exists'.mp hdecode
    have hq : FractionOutput (safeValue xs v) τ := by
      simpa [safeValue, hv1, hsome] using (hτq q rest hsome).1
    have hb : (Cond.eq (.var "input.valid") (.lit 1)).evalB B τ = some true := by
      simpa [hgood] using evalB_condEq
        (evalB_var (B := B) (σ := τ) (x := "input.valid") hflagB) (evalB_lit h1)
    exact ⟨τ, (hr₁.seq (Run.ite_true (d := zeroResult) hb Run.skip)).mono
      (by simp only [Cond.size, Expr.size]; omega), hq, hτinp, hτrem, hτvalid, hτbound⟩
  · have hzero : safeValue xs v = 0 := by
      by_cases hv1 : v = 1
      · have hnone : WordDecoding.readRational xs = none := by
          by_contra hh; simp only [if_neg hh, hv1] at hτvalid; exact hgood hτvalid
        simp [safeValue, hv1, hnone]
      · simp [safeValue, hv1]
    have hb : (Cond.eq (.var "input.valid") (.lit 1)).evalB B τ = some false := by
      simpa [hgood] using evalB_condEq
        (evalB_var (B := B) (σ := τ) (x := "input.valid") hflagB) (evalB_lit h1)
    obtain ⟨υ, hr₂, hυq⟩ := zeroResult_spec B h1 τ True.intro
    have hυinp := (hr₂.frame_inp (by decide)).trans hτinp
    have hυrem := (hr₂.frame_var "input.remaining" (by decide)).trans hτrem
    have hυvalid := (hr₂.frame_var "input.valid" (by decide)).trans hτvalid
    exact ⟨υ, (hr₁.seq (Run.ite_false (c := .skip) hb hr₂)).mono
      (by simp only [Cond.size, Expr.size]; omega), hzero.symm ▸ hυq,
      hυinp, hυrem, hυvalid, hr₂.inpBounded hτbound⟩

end Lax109476Proofs.RamReadFraction

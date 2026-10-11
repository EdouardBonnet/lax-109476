import Lax109476Proofs.RamCopyBlock
import Lax109476Proofs.RamStoredProgram
import Lax109476Proofs.RamReadBody

namespace Lax109476Proofs.RamFamilyQueryCopy

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamFrame RamEllipsoidStep RationalArithmeticBounds RamCopy

def metadata : Com := .seq (.assign "lp.m" (.var "system.m")) (.assign "lp.n" (.var "system.n"))
def count : Com := .assign "decode.count" (.mul (.var "system.m") (.var "system.n"))
def zeroObjective (a : String) : Com := .seq (.assign "vec.n" (.var "system.n")) (RamZeroArray.zeroRationalArray a)

def copy (sourceA sourceB targetA targetB targetC : String) : Com := .seq count
  (.seq (RamCopyBlock.copyBlock sourceA targetA "decode.count")
  (.seq (RamCopyBlock.copyBlock sourceB targetB "system.m")
  (.seq (zeroObjective targetC) metadata)))

def Input {r s : ℕ} (F : Program ℚ r s) (sourceA sourceB targetA targetB targetC : String) (σ : Env) : Prop :=
  Represents sourceA (RamMatrixStorage.flatten F.A) σ ∧ Represents sourceB (List.ofFn F.b) σ ∧
    σ.vars "system.m" = r ∧ σ.vars "system.n" = s ∧
    Extents targetA (r * s) σ ∧ Extents targetB r σ ∧ Extents targetC s σ

def Output {r s : ℕ} (F : Program ℚ r s) (targetA targetB targetC : String) (σ : Env) : Prop :=
  Represents targetA (RamMatrixStorage.flatten F.A) σ ∧ Represents targetB (List.ofFn F.b) σ ∧
    Represents targetC (List.ofFn F.c) σ ∧ σ.vars "lp.m" = r ∧ σ.vars "lp.n" = s ∧
    σ.vars "decode.count" = r * s

theorem zeroObjective_spec (B s : ℕ) (a : String) (h1 : 1 < B) (hs : s < B) :
    Spec B (fun σ => Extents a s σ ∧ σ.vars "system.n" = s) (zeroObjective a)
      (fun _ τ => Represents a (List.replicate s 0) τ) (33 * s + 20) := by
  rintro σ ⟨hσa, hσs⟩
  have hr₁ : Run B (.assign "vec.n" (.var "system.n")) σ (σ.setVar "vec.n" s) 2 :=
    Run.assign (by simpa only [hσs] using evalB_var (B := B) (σ := σ) (x := "system.n") (hσs ▸ hs))
  obtain ⟨τ, hr₂, hτa, _⟩ := RamZeroArray.zeroRationalArray_spec B s a hs h1 (σ.setVar "vec.n" s)
    ⟨hσa ".s" (by simp), hσa ".n" (by simp), hσa ".d" (by simp), by simp⟩
  exact ⟨τ, (hr₁.seq hr₂).mono (by omega), hτa⟩

theorem metadata_spec (B r s : ℕ) (hr : r < B) (hs : s < B) :
    Spec B (fun σ => σ.vars "system.m" = r ∧ σ.vars "system.n" = s) metadata
      (fun _ τ => τ.vars "lp.m" = r ∧ τ.vars "lp.n" = s) 4 := by
  rintro σ ⟨hσr, hσs⟩
  run_vcg
  all_goals simp_all

theorem count_spec (B r s : ℕ) (hr : r < B) (hs : s < B) (hcount : r * s < B) :
    Spec B (fun σ => σ.vars "system.m" = r ∧ σ.vars "system.n" = s) count
      (fun _ τ => τ.vars "decode.count" = r * s) 4 := by
  rintro σ ⟨hσr, hσs⟩
  run_vcg
  all_goals simp_all

theorem copy_wvars (sourceA sourceB targetA targetB targetC : String) :
    (copy sourceA sourceB targetA targetB targetC).wvars = (copy "" "" "" "" "").wvars := by rfl

set_option maxHeartbeats 1000000 in
theorem copy_spec (B M r s : ℕ) (F : Program ℚ r s) (sourceA sourceB targetA targetB targetC : String)
    (h1 : 1 < B) (hMB : M < B) (hB : r * s + r + s + 4 < B)
    (hA : ∀ i j, Height (F.A i j) M) (hb : ∀ i, Height (F.b i) M) (hc : ∀ j, F.c j = 0)
    (hAA : Disjoint sourceA targetA) (hBA : Disjoint sourceB targetA) (hBB : Disjoint sourceB targetB)
    (hAB : Disjoint targetA targetB) (hAC : Disjoint targetA targetC) (hBC : Disjoint targetB targetC) :
    Spec B (Input F sourceA sourceB targetA targetB targetC) (copy sourceA sourceB targetA targetB targetC)
      (fun _ τ => Output F targetA targetB targetC τ)
      (71 * (r * s + r) + 33 * s + 80) := by
  have hrB : r < B := by omega
  have hsB : s < B := by omega
  have hcountB : r * s < B := by omega
  have hAcopy := RamCopyBlock.copyBlock_spec B M (r * s) sourceA targetA "decode.count"
    (fun i => F.A i.divNat i.modNat) h1 hcountB hMB (fun i => hA i.divNat i.modNat) hAA
  have hbcopy := RamCopyBlock.copyBlock_spec B M r sourceB targetB "system.m" F.b h1 hrB hMB hb hBB
  rintro σ ⟨hσA, hσb, hσr, hσs, hσtargetA, hσtargetB, hσtargetC⟩
  obtain ⟨τ, hr₀, hτcount⟩ := count_spec B r s hrB hsB hcountB σ ⟨hσr, hσs⟩
  have hτA : Represents sourceA (RamMatrixStorage.flatten F.A) τ :=
    RamReadBody.represents_frame _ _ hσA hr₀ (by intro t ht; simp [count, Com.warrs])
  obtain ⟨υ, hr₁, hυA, _⟩ := hAcopy τ
    ⟨hτA, RamAdvanceState.extents_of_run hr₀ targetA (r * s) hσtargetA, hτcount⟩
  have hυb := RamReadBody.represents_frame _ _ hσb (hr₀.seq hr₁)
    (by
      intro t ht
      simp only [Com.warrs, count, RamCopyBlock.copyBlock_warrs, List.mem_append, List.not_mem_nil, false_or]
      simp only [List.mem_cons, List.mem_singleton]
      have h₁ := hBA t (by simpa [suffixes] using ht) ".s" (by simp [suffixes])
      have h₂ := hBA t (by simpa [suffixes] using ht) ".n" (by simp [suffixes])
      have h₃ := hBA t (by simpa [suffixes] using ht) ".d" (by simp [suffixes])
      simp_all [Ne.symm])
  have hυr := ((hr₀.seq hr₁).frame_var "system.m" (by
    simp only [Com.wvars, count, RamCopyBlock.copyBlock_wvars]; decide)).trans hσr
  obtain ⟨ξ, hr₂, hξb, _⟩ := hbcopy υ
    ⟨hυb, RamAdvanceState.extents_of_run (hr₀.seq hr₁) targetB r hσtargetB, hυr⟩
  have hrCopy := hr₀.seq (hr₁.seq hr₂)
  have hξs := (hrCopy.frame_var "system.n" (by
    simp only [Com.wvars, count, RamCopyBlock.copyBlock_wvars]; decide)).trans hσs
  obtain ⟨ρ, hr₃, hρc⟩ := zeroObjective_spec B s targetC h1 hsB ξ
    ⟨RamAdvanceState.extents_of_run hrCopy targetC s hσtargetC, hξs⟩
  have hrBuild := hr₀.seq (hr₁.seq (hr₂.seq hr₃))
  have hρr := (hrBuild.frame_var "system.m" (by
    change "system.m" ∉ (Com.seq count (Com.seq (RamCopyBlock.copyBlock "" "" "")
      (Com.seq (RamCopyBlock.copyBlock "" "" "") (zeroObjective "")))).wvars
    decide)).trans hσr
  have hρs := (hrBuild.frame_var "system.n" (by
    change "system.n" ∉ (Com.seq count (Com.seq (RamCopyBlock.copyBlock "" "" "")
      (Com.seq (RamCopyBlock.copyBlock "" "" "") (zeroObjective "")))).wvars
    decide)).trans hσs
  obtain ⟨ω, hr₄, hωr, hωs⟩ := metadata_spec B r s hrB hsB ρ ⟨hρr, hρs⟩
  have hωcount := ((hr₁.seq (hr₂.seq (hr₃.seq hr₄))).frame_var "decode.count" (by
    change "decode.count" ∉ (Com.seq (RamCopyBlock.copyBlock "" "" "")
      (Com.seq (RamCopyBlock.copyBlock "" "" "") (Com.seq (zeroObjective "") metadata))).wvars
    decide)).trans hτcount
  have hωA := RamReadBody.represents_frame _ _ hυA (hr₂.seq (hr₃.seq hr₄))
    (by
      intro t ht
      simp [suffixes] at ht
      rcases ht with rfl | rfl | rfl
      all_goals simp [RamCopyBlock.copyBlock_warrs, zeroObjective, metadata, Com.warrs,
        RamZeroArray.zeroRationalArray, RamZeroArray.fillConstant, Lib.Fill.put]
      all_goals simp_all [RamCopy.Disjoint, suffixes])
  have hωb := RamReadBody.represents_frame _ _ hξb (hr₃.seq hr₄)
    (by
      intro t ht
      simp [suffixes] at ht
      rcases ht with rfl | rfl | rfl
      all_goals simp [zeroObjective, metadata, Com.warrs, RamZeroArray.zeroRationalArray,
        RamZeroArray.fillConstant, Lib.Fill.put]
      all_goals simp_all [RamCopy.Disjoint, suffixes])
  have hωc := RamReadBody.represents_frame _ _ hρc hr₄ (by intro t ht; simp [metadata, Com.warrs])
  have hcList : List.ofFn F.c = List.replicate s 0 := by simp [funext hc]
  refine ⟨ω, (hr₀.seq (hr₁.seq (hr₂.seq (hr₃.seq hr₄)))).mono ?_, hωA, hωb, ?_, hωr, hωs, hωcount⟩
  · simp only [Nat.mul_add]; omega
  · simpa only [hcList] using hωc

end Lax109476Proofs.RamFamilyQueryCopy

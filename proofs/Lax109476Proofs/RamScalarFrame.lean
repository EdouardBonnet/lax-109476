import Lax109476Proofs.RamRationalScalars

namespace Lax109476Proofs.RamScalarFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RamRationalScalars

theorem value_frame {B k : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ k)
    (name : String) (q : ℚ) (h : Value name q σ)
    (hs : name ++ ".s" ∉ c.wvars) (hn : name ++ ".n" ∉ c.wvars)
    (hd : name ++ ".d" ∉ c.wvars) : Value name q τ := by
  simpa only [Value, hr.frame_var _ hs, hr.frame_var _ hn, hr.frame_var _ hd] using h

theorem fraction_frame {B k : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ k)
    (q : ℚ) (h : FractionOutput q σ)
    (hs : "rat.s" ∉ c.wvars) (hn : "rat.n" ∉ c.wvars)
    (hd : "rat.d" ∉ c.wvars) : FractionOutput q τ := by
  simpa only [FractionOutput, hr.frame_var _ hs, hr.frame_var _ hn, hr.frame_var _ hd] using h

theorem left_frame {B k : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ k)
    (q : ℚ) (h : LeftValue q σ)
    (hs : "left.s" ∉ c.wvars) (hn : "left.n" ∉ c.wvars)
    (hd : "left.d" ∉ c.wvars) : LeftValue q τ := by
  simpa only [LeftValue, hr.frame_var _ hs, hr.frame_var _ hn, hr.frame_var _ hd] using h

theorem right_frame {B k : ℕ} {c : Com} {σ τ : Env} (hr : Run B c σ τ k)
    (q : ℚ) (h : RightValue q σ)
    (hs : "right.s" ∉ c.wvars) (hn : "right.n" ∉ c.wvars)
    (hd : "right.d" ∉ c.wvars) : RightValue q τ := by
  simpa only [RightValue, hr.frame_var _ hs, hr.frame_var _ hn, hr.frame_var _ hd] using h

end Lax109476Proofs.RamScalarFrame

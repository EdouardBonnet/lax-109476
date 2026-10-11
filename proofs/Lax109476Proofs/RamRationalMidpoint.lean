import Lax109476Proofs.RamRationalHalf

namespace Lax109476Proofs.RamRationalMidpoint

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RamRationalScalars RamScalarFrame

def midpoint : Com := .seq (readLeft "bisect.lo") (.seq (readRight "bisect.hi")
  (.seq addFraction (.seq resultToLeft (.seq RamRationalHalf.half (save "bisect.mid")))))

theorem midpoint_spec (B M : ℕ) (l u : ℚ) (hB : 4 * M ^ 2 + 3 < B)
    (hl : Height l M) (hu : Height u M) :
    Spec B (fun σ => Value "bisect.lo" l σ ∧ Value "bisect.hi" u σ) midpoint
      (fun _ τ => Value "bisect.mid" ((l + u) / 2) τ) (144 * M.size + 324) := by
  have hM : 1 ≤ M := le_trans l.den_pos hl.2
  have hMB : M < B := by nlinarith
  have h1 : 1 < B := by omega
  have hsum : Height (l + u) (2 * M ^ 2) := by
    simpa only [pow_two, Nat.mul_assoc] using height_add l u M M hl hu
  have hsumB : 2 * M ^ 2 < B := by omega
  have hhalf : Height ((l + u) / 2) (4 * M ^ 2) := by
    have h := height_div (l + u) 2 (2 * M ^ 2) 2 hsum (by norm_num [Height])
    convert h using 1 <;> ring
  have hhalfB : 4 * M ^ 2 < B := by omega
  rintro σ ⟨hσl, hσu⟩
  obtain ⟨τ, hr₁, hτl⟩ := readLeft_spec B "bisect.lo" l h1 (hl.1.trans_lt hMB) (hl.2.trans_lt hMB)
    (by simp [RamCopy.Disjoint, RamCopy.suffixes]) σ hσl
  have hτu := value_frame hr₁ "bisect.hi" u hσu (by decide) (by decide) (by decide)
  obtain ⟨υ, hr₂, hυu⟩ := readRight_spec B "bisect.hi" u h1 (hu.1.trans_lt hMB) (hu.2.trans_lt hMB)
    (by simp [RamCopy.Disjoint, RamCopy.suffixes]) τ hτu
  have hυl := left_frame hr₂ l hτl (by decide) (by decide) (by decide)
  obtain ⟨ρ, hr₃, hρsum⟩ := add_spec B M l u (by omega) hl hu υ ⟨hυl, hυu⟩
  obtain ⟨ξ, hr₄, hξsum⟩ := resultToLeft_spec B (l + u) h1 (hsum.1.trans_lt hsumB)
    (hsum.2.trans_lt hsumB) ρ hρsum
  obtain ⟨ζ, hr₅, hζhalf⟩ := RamRationalHalf.half_spec B (2 * M ^ 2) (l + u) (by omega) hsum ξ hξsum
  obtain ⟨η, hr₆, hη⟩ := save_spec B "bisect.mid" ((l + u) / 2) h1 (hhalf.1.trans_lt hhalfB)
    (hhalf.2.trans_lt hhalfB) (by simp) ζ hζhalf
  have hp := RationalSizeBounds.size_pow_le M 2
  have hm := RationalSizeBounds.size_mul_le 2 (M ^ 2)
  have h2size : (2 : ℕ).size = 2 := by decide
  rw [h2size] at hm
  exact ⟨η, (hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq (hr₅.seq hr₆))))).mono (by omega), hη⟩

end Lax109476Proofs.RamRationalMidpoint

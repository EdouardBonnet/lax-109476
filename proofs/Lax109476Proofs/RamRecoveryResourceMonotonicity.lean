import Lax109476Proofs.RamRecoverFeasibleSystem
import Lax109476Proofs.RamStoredFeasibilityBounds

namespace Lax109476Proofs.RamRecoveryResourceMonotonicity

attribute [gcongr] RamStoredFeasibilityBounds.wordWidth_monotone
attribute [gcongr] RamStoredFeasibilityBounds.instructionBound_monotone

@[gcongr] theorem reconstruction_width {S T : ℕ} (h : S ≤ T) :
    RamRationalReconstruction.wordWidth S ≤ RamRationalReconstruction.wordWidth T := by
  unfold RamRationalReconstruction.wordWidth RamRationalReconstruction.depthBound
    RamConvergentBounds.wordWidth RamConvergentBounds.exponent RamDecoder.wordWidth
  gcongr

@[gcongr] theorem reconstruction_cost {S T : ℕ} (h : S ≤ T) :
    RamRationalReconstruction.instructionBound S ≤ RamRationalReconstruction.instructionBound T := by
  unfold RamRationalReconstruction.instructionBound RamRationalReconstruction.depthBound
    RamConvergentBounds.instructionBound RamConvergentBounds.exponent
  gcongr

@[gcongr] theorem point_query_size {m n S r s T : ℕ} (hm : m ≤ r) (hn : n ≤ s) (hS : S ≤ T) :
    RamPointRecoveryBounds.querySize m n S ≤ RamPointRecoveryBounds.querySize r s T := by
  unfold RamPointRecoveryBounds.querySize
  gcongr

@[gcongr] theorem point_query_cost {m n S r s T : ℕ} (hm : m ≤ r) (hn : n ≤ s) (hS : S ≤ T) :
    RamPointRecoveryBounds.queryCost m n S ≤ RamPointRecoveryBounds.queryCost r s T := by
  unfold RamPointRecoveryBounds.queryCost
  gcongr

@[gcongr] theorem point_width {m n S r s T : ℕ} (hm : m ≤ r) (hn : n ≤ s) (hS : S ≤ T) :
    RamPointRecoveryBounds.wordWidth m n S ≤ RamPointRecoveryBounds.wordWidth r s T := by
  unfold RamPointRecoveryBounds.wordWidth RamDecoder.wordWidth
  gcongr

@[gcongr] theorem point_cost {m n S C r s T D : ℕ}
    (hm : m ≤ r) (hn : n ≤ s) (hS : S ≤ T) (hC : C ≤ D) :
    RamPointRecoveryBounds.instructionBound m n S C ≤ RamPointRecoveryBounds.instructionBound r s T D := by
  unfold RamPointRecoveryBounds.instructionBound
  gcongr

@[gcongr] theorem cap_bits {S T : ℕ} (h : S ≤ T) :
    RamRecoverFeasibleSystem.capBits S ≤ RamRecoverFeasibleSystem.capBits T := by
  unfold RamRecoverFeasibleSystem.capBits
  gcongr

@[gcongr] theorem recovery_bits {S T : ℕ} (h : S ≤ T) :
    RamRecoverFeasibleSystem.recoveryBits S ≤ RamRecoverFeasibleSystem.recoveryBits T := by
  unfold RamRecoverFeasibleSystem.recoveryBits
  gcongr

@[gcongr] theorem recovery_width {m n S r s T : ℕ} (hm : m ≤ r) (hn : n ≤ s) (hS : S ≤ T) :
    RamRecoverFeasibleSystem.wordWidth m n S ≤ RamRecoverFeasibleSystem.wordWidth r s T := by
  unfold RamRecoverFeasibleSystem.wordWidth RamCoordinateCapBounds.wordWidth
  gcongr

@[gcongr] theorem recovery_cost {m n S r s T : ℕ} (hm : m ≤ r) (hn : n ≤ s) (hS : S ≤ T) :
    RamRecoverFeasibleSystem.instructionBound m n S ≤ RamRecoverFeasibleSystem.instructionBound r s T := by
  unfold RamRecoverFeasibleSystem.instructionBound
  gcongr

end Lax109476Proofs.RamRecoveryResourceMonotonicity

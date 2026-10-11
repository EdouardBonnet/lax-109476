import Lax109476Proofs.RamContinuedFractionConvergent
import Lax109476Proofs.RamReconstructionCandidate
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax109476Proofs

namespace Checks.Convergents
open Checks

def cfCommand : Com := .seq (.assign "left.s" (.lit 0))
  (.seq (.read "left.n") (.seq (.read "left.d") (.seq (.read "cf.depth")
    (.seq RamContinuedFractionConvergent.convergent
      (.seq (.write (.var "rat.s")) (.seq (.write (.var "rat.n")) (.write (.var "rat.d"))))))))

def cfLayout : Layout := let names := commandNames cfCommand
  ⟨names.1.eraseDups, names.2.eraseDups, 8⟩

def execute (xs : List ℕ) : Option (List ℕ) :=
  executeCompiled cfLayout 128 100000 cfCommand xs

#guard execute [13,8,0] == some ([0,1,1])

#guard execute [13,8,1] == some ([0,2,1])

#guard execute [13,8,2] == some ([0,3,2])

#guard execute [13,8,4] == some ([0,13,8])

#guard execute [13,8,8] == some ([0,13,8])

#guard execute [0,1,4] == some ([0,0,1])

#guard execute [17,1,3] == some ([0,17,1])

end Checks.Convergents

import Lax109476Proofs.RamRationalReconstruction
import Lax109476Proofs.RamReconstructionCandidate
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax109476Proofs

namespace Checks.Reconstruction
open Checks

def reconstructionCommand : Com :=
  .seq (.read "recon.lo.s") (.seq (.read "recon.lo.n") (.seq (.read "recon.lo.d")
    (.seq (.read "recon.hi.s") (.seq (.read "recon.hi.n") (.seq (.read "recon.hi.d")
      (.seq (.read "recon.bound") (.seq RamRationalReconstruction.reconstruct
        (.seq (.write (.var "recon.found"))
          (.ite (.eq (.var "recon.found") (.lit 1))
            (.seq (.write (.var "recon.result.s"))
              (.seq (.write (.var "recon.result.n")) (.write (.var "recon.result.d")))) .skip)))))))))

def reconstructionLayout : Layout := let names := commandNames reconstructionCommand
  ⟨names.1.eraseDups, names.2.eraseDups, 8⟩

def execute (xs : List ℕ) : Option (List ℕ) :=
  executeCompiled reconstructionLayout 128 500000 reconstructionCommand xs

#guard execute [0,81,50,0,13,8,10] == some ([1,0,13,8])

#guard execute [0,81,50,0,13,8,7] == some ([0])

#guard execute [0,1,1,0,13,8,1] == some ([1,0,1,1])

#guard execute [0,0,1,0,0,1,1] == some ([1,0,0,1])

#guard execute [0,17,1,0,17,1,1] == some ([1,0,17,1])

#guard execute [0,0,1,0,13,8,0] == some ([0])

end Checks.Reconstruction

import Lax109476Proofs.RamContinuedFractionStep
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile
open Lax109476Proofs

namespace Checks.ContinuedFractionStep
open Checks

def cfCommand : Com := .seq (.read "left.n") (.seq (.read "left.d")
  (.seq RamContinuedFractionStep.step
    (.seq (.write (.var "cf.a"))
      (.seq (.write (.var "rat.s")) (.seq (.write (.var "rat.n")) (.write (.var "rat.d")))))))

def cfLayout : Layout := ⟨["left.n", "left.d", "cf.a", "cf.r", "rat.s", "rat.n", "rat.d", "gcd.a", "gcd.b", "gcd.t"], [], 5⟩

def execute (xs : List ℕ) : Option (List ℕ) :=
  executeCompiled cfLayout 64 10000 cfCommand xs

#guard execute [13,8] == some ([1,0,8,5])

#guard execute [0,1] == some ([0,0,0,1])

#guard execute [12,4] == some ([3,0,0,1])

#guard execute [100,7] == some ([14,0,7,2])

#guard execute [14,8] == some ([1,0,4,3])

end Checks.ContinuedFractionStep

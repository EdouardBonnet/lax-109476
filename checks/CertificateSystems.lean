import Lax109476Proofs.RamCertificateFamilies
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax109476Proofs

namespace Checks.CertificateSystems
open Checks

def queryCommand : Com := .seq (.read "test.kind") (.seq (.read "source.m") (.seq (.read "source.n")
  (.seq (.assign "test.count" (.mul (.var "source.m") (.var "source.n")))
  (.seq (readArray "source.A" "test.count") (.seq (readArray "source.b" "source.m")
  (.seq (readArray "source.c" "source.n")
  (.seq (.ite (.eq (.var "test.kind") (.lit 0)) RamCertificateFamilies.optimal
    (.ite (.eq (.var "test.kind") (.lit 1)) RamCertificateFamilies.infeasible RamCertificateFamilies.unbounded))
  (.seq (.write (.var "system.m")) (.seq (.write (.var "system.n"))
  (.seq (.assign "test.count" (.mul (.var "system.m") (.var "system.n")))
  (.seq (.write (.var "test.count")) (.seq (emitArray "system.A" "test.count") (emitArray "system.b" "system.m")))))))))))))

def queryLayout : Layout := let names := commandNames queryCommand
  ⟨names.1.eraseDups, names.2.eraseDups, 128⟩

def execute (xs : List ℕ) : Option (List ℕ) :=
  executeCompiled queryLayout 128 200000 queryCommand xs

def triples (xs : List ℚ) : List ℕ := xs.flatMap fun q =>
  [RamRationalArrays.rationalSign q, q.num.natAbs, q.den]

#guard execute ([0,1,2] ++ triples [2,-1] ++ triples [3] ++ triples [4,-5]) ==
  some ([5,3,15] ++ triples [2,-1,0,0,0,-2,0,0,1,4,-5,-3,-4,5,3] ++ triples [3,-4,5,0,0])

#guard execute ([1,1,2] ++ triples [2,-1] ++ triples [3] ++ triples [4,-5]) ==
  some ([3,1,3] ++ triples [-2,1,3] ++ triples [0,0,-1])

#guard execute ([2,1,2] ++ triples [2,-1] ++ triples [3] ++ triples [4,-5]) ==
  some ([3,4,12] ++ triples [2,-1,0,0,0,0,2,-1,0,0,-4,5] ++ triples [3,0,-1])

#guard execute [0,0,0] == some ([2,0,0] ++ triples [0,0])

#guard execute [1,0,0] == some ([1,0,0] ++ triples [-1])

#guard execute [2,0,0] == some ([1,0,0] ++ triples [-1])

#guard execute ([0,1,0] ++ triples [3]) == some ([3,1,3] ++ triples [0,-3,3] ++ triples [3,0,0])

#guard execute ([1,1,0] ++ triples [3]) == some ([1,1,1] ++ triples [3] ++ triples [-1])

#guard execute ([2,1,0] ++ triples [3]) == some ([3,0,0] ++ triples [3,0,-1])

end Checks.CertificateSystems

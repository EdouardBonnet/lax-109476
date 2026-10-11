import Lax109476Proofs.RamWriteCertificate
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax109476Proofs

namespace Checks.CertificateOutput
open Checks

def queryCommand : Com := .seq (.read "test.kind") (.seq (.read "system.n")
  (.seq (.read "test.count") (.seq (readArray "point.x" "test.count")
  (.ite (.eq (.var "test.kind") (.lit 0)) (RamWriteCertificate.emit 0)
    (.ite (.eq (.var "test.kind") (.lit 1)) (RamWriteCertificate.emit 1) (RamWriteCertificate.emit 2))))))

def queryLayout : Layout := let names := commandNames queryCommand
  ⟨names.1.eraseDups, names.2.eraseDups, 128⟩

def execute (xs : List ℕ) : Option (List ℕ) :=
  executeCompiled queryLayout 128 100000 queryCommand xs

def triples (xs : List ℚ) : List ℕ := xs.flatMap fun q =>
  [RamRationalArrays.rationalSign q, q.num.natAbs, q.den]

#guard execute ([0,2,4] ++ triples [13/8,-1/3,7,0]) == some ([0] ++ triples [13/8,-1/3])

#guard execute ([1,0,2] ++ triples [7,11]) == some ([1])

#guard execute ([2,2,3] ++ triples [0,2/3,11]) == some ([2] ++ triples [0,2/3])

#guard execute [2,1,2,1,0,1,0,7,1] == some ([2,0,0,1])

end Checks.CertificateOutput

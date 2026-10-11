import Lax109476Proofs.RamRecoveryQuery
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax109476Proofs

namespace Checks.CoordinateQuery
open Checks

def queryCommand : Com := .seq (.read "point.m") (.seq (.read "point.n")
  (.seq (.read "point.k") (.seq (.read "bisect.mid.s") (.seq (.read "bisect.mid.n")
  (.seq (.read "bisect.mid.d") (.seq (.assign "test.count" (.mul (.var "point.m") (.var "point.n")))
  (.seq (readArray "point.A" "test.count") (.seq (readArray "point.b" "point.m")
  (.seq (readArray "point.x" "point.n") (.seq RamRecoveryQuery.buildQuery
  (.seq (.write (.var "lp.m")) (.seq (.write (.var "lp.n")) (.seq (.write (.var "decode.count"))
  (.seq (emitArray "lp.A" "decode.count") (.seq (emitArray "lp.b" "lp.m") (emitArray "lp.c" "lp.n"))))))))))))))))

def queryLayout : Layout := let names := commandNames queryCommand
  ⟨names.1.eraseDups, names.2.eraseDups, 128⟩

def execute (xs : List ℕ) : Option (List ℕ) :=
  executeCompiled queryLayout 128 100000 queryCommand xs

def triples (xs : List ℚ) : List ℕ := xs.flatMap fun q =>
  [RamRationalArrays.rationalSign q, q.num.natAbs, q.den]

#guard execute ([1,2,1,0,7,4] ++ triples [-1,2] ++ triples [3] ++ triples [5/2,0]) ==
  some ([6,2,12] ++ triples [-1,2,1,0,0,0,-1,0,0,0,0,1] ++ triples [3,5/2,0,-5/2,0,7/4] ++ triples [0,0])

#guard execute ([0,1,0,0,0,1] ++ triples [0]) ==
  some ([3,1,3] ++ triples [0,0,1] ++ triples [0,0,0] ++ triples [0])

end Checks.CoordinateQuery

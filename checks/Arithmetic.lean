import Lax109476Proofs.RamSquareRoot
import Checks.Common
import Lax109476Proofs.RamRational
import Lax109476Proofs.RamComparison
import Lax109476Proofs.RamBitLength
import Lax109476Proofs.RamRounding
import Lax109476Proofs.RamEncoding
import Lax109476Proofs.RamRationalArrays

open Lax808846Proofs.Imp Lax808846Proofs.Compile
open Lax109476Proofs.RamArithmetic Lax109476Proofs.RamSquareRoot
open Lax109476Proofs.RamRational
open Lax109476Proofs.RamComparison Lax109476Proofs.RamBitLength
open Lax109476Proofs.RamRounding
open Lax109476Proofs.RamEncoding
open Lax109476Proofs.RamRationalArrays

namespace Checks.Arithmetic
open Checks

def arithmeticLayout : Layout :=
  ⟨["gcd.a", "gcd.b", "gcd.t", "rat.n", "rat.d", "rat.s", "sqrt.n", "sqrt.lo", "sqrt.hi", "sqrt.mid",
    "left.s", "left.n", "left.d", "right.s", "right.n", "right.d", "sum.u", "sum.v",
    "cmp.u", "cmp.v", "cmp.le", "bits.v", "bits.k", "round.a", "round.q", "round.r", "grid.D",
    "vec.i"], ["test.s", "test.n", "test.d"], 10⟩

def execute (c : Com) (input : List ℕ) : Option (List ℕ) :=
  executeCompiled arithmeticLayout 64 10000 c input

def gcdCommand : Com := .seq (.read "gcd.a")
  (.seq (.read "gcd.b") (.seq gcdLoop (.write (.var "gcd.a"))))
def normalizeCommand : Com := .seq (.read "rat.n")
  (.seq (.read "rat.d") (.seq normalizeFraction
    (.seq (.write (.var "rat.n")) (.write (.var "rat.d")))))
def sqrtCommand : Com := .seq (.read "sqrt.n") (.seq squareRoot (.write (.var "sqrt.lo")))

#guard execute gcdCommand [1071, 462] == some ([21])

#guard execute gcdCommand [0, 123456789] == some ([123456789])

#guard execute normalizeCommand [333, 999] == some ([1, 3])

#guard execute normalizeCommand [0, 999] == some ([0, 1])

#guard ([0, 1, 2, 144, 145, 10000].map fun n => execute sqrtCommand [n]) == ([[0], [1], [1], [12], [12], [100]]).map some

def readFractionPair : Com := .seq (.read "left.s") (.seq (.read "left.n")
  (.seq (.read "left.d") (.seq (.read "right.s") (.seq (.read "right.n") (.read "right.d")))))
def writeFraction : Com := .seq (.write (.var "rat.s"))
  (.seq (.write (.var "rat.n")) (.write (.var "rat.d")))
def addCommand : Com := .seq readFractionPair (.seq addFraction writeFraction)
def mulCommand : Com := .seq readFractionPair (.seq multiplyFraction writeFraction)
def invCommand : Com := .seq (.read "left.s") (.seq (.read "left.n")
  (.seq (.read "left.d") (.seq invertFraction writeFraction)))

#guard execute addCommand [0, 1, 3, 1, 1, 2] == some ([1, 1, 6])

#guard execute addCommand [1, 2, 3, 0, 1, 3] == some ([1, 1, 3])

#guard execute addCommand [1, 1, 3, 0, 2, 3] == some ([0, 1, 3])

#guard execute addCommand [0, 5, 7, 1, 5, 7] == some ([0, 0, 1])

#guard execute addCommand [1, 5, 7, 0, 5, 7] == some ([1, 0, 1])

#guard execute mulCommand [1, 2, 3, 1, 3, 5] == some ([0, 2, 5])

#guard execute mulCommand [1, 1, 3, 0, 2, 5] == some ([1, 2, 15])

#guard execute invCommand [1, 2, 3] == some ([1, 3, 2])

#guard execute invCommand [0, 0, 17] == some ([0, 0, 1])

def compareCommand : Com := .seq readFractionPair (.seq compareFraction (.write (.var "cmp.le")))
def bitsCommand : Com := .seq (.read "bits.v") (.seq bitLength (.write (.var "bits.k")))

#guard execute compareCommand [0, 1, 3, 0, 1, 2] == some ([1])

#guard execute compareCommand [0, 1, 2, 0, 1, 3] == some ([0])

#guard execute compareCommand [1, 1, 3, 1, 1, 2] == some ([0])

#guard execute compareCommand [1, 1, 2, 1, 1, 3] == some ([1])

#guard execute compareCommand [1, 1, 3, 0, 1, 2] == some ([1])

#guard execute compareCommand [0, 1, 3, 1, 1, 2] == some ([0])

#guard execute compareCommand [0, 0, 3, 1, 0, 2] == some ([1])

#guard execute compareCommand [1, 0, 3, 0, 0, 2] == some ([1])

#guard ([0, 1, 2, 3, 7, 8, 255, 256, 1073741824].map fun n => execute bitsCommand [n]) == ([[0], [1], [2], [2], [3], [4], [8], [9], [31]]).map some

def readGridFraction : Com := .seq (.read "left.s") (.seq (.read "left.n")
  (.seq (.read "left.d") (.read "grid.D")))
def roundCommand : Com := .seq readGridFraction (.seq roundFraction writeFraction)
def upperRootCommand : Com := .seq readGridFraction (.seq upperRootFraction writeFraction)

#guard execute roundCommand [0, 1, 3, 10] == some ([0, 3, 10])

#guard execute roundCommand [1, 1, 3, 10] == some ([1, 2, 5])

#guard execute roundCommand [1, 1, 2, 10] == some ([1, 1, 2])

#guard execute roundCommand [1, 0, 17, 10] == some ([1, 0, 1])

#guard execute upperRootCommand [0, 2, 1, 10] == some ([0, 3, 2])

#guard execute upperRootCommand [0, 1, 3, 10] == some ([0, 3, 5])

#guard execute upperRootCommand [1, 1, 3, 10] == some ([0, 1, 10])

def canonicalWriteCommand : Com := .seq (.read "rat.s") (.seq (.read "rat.n")
  (.seq (.read "rat.d") writeReducedFraction))

#guard execute canonicalWriteCommand [1, 0, 1] == some ([0, 0, 1])

#guard execute canonicalWriteCommand [1, 1, 3] == some ([1, 1, 3])

def arrayRoundtrip : Com := .seq (.read "rat.s") (.seq (.read "rat.n")
  (.seq (.read "rat.d") (.seq (.assign "vec.i" (.lit 2))
    (.seq (storeReduced "test") (.seq (loadLeft "test")
      (.seq (.write (.var "left.s")) (.seq (.write (.var "left.n")) (.write (.var "left.d")))))))))

#guard execute arrayRoundtrip [1, 0, 1] == some ([0, 0, 1])

#guard execute arrayRoundtrip [1, 2, 5] == some ([1, 2, 5])

end Checks.Arithmetic

import Lax109476Proofs.WordDecoding
import Lax109476Proofs.CertificateSearch

namespace Lax109476Proofs.WordSolver

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding

/-- A total word-list function. Invalid encodings return the empty list;
valid rational programs are solved by the proved certificate-recovery search. -/
def solve (input : List ℕ) : List ℕ :=
  match WordDecoding.decode input with
  | none => []
  | some P => ((CertificateSearch.solve P.program).map encodeCertificate).getD []

theorem solve_correct (m n : ℕ) (P : Program ℚ m n) :
    ∃ cert : Certificate m n, solve (encodeProgram P) = encodeCertificate cert ∧
      IsValidCertificate P cert := by
  obtain ⟨cert, he, hv⟩ := CertificateSearch.solve_exists P
  refine ⟨cert, ?_, hv⟩
  simp [solve, WordDecoding.decode_encode, he]

end Lax109476Proofs.WordSolver

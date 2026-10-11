import Lax109476Proofs.RamSolverTotalExecution

set_option maxHeartbeats 0
set_option maxRecDepth 12000

namespace Lax109476Proofs.RamSolverAllocation

open Lax808846Proofs.Imp
open RamSolverWorkspace RamUniformSolverBounds

def splitChars : List Char → List (List Char)
  | [] => [[]]
  | c :: cs => if c = '.' then [] :: splitChars cs else
    match splitChars cs with
    | [] => [[c]]
    | part :: parts => (c :: part) :: parts

def feasibilityLength (m n : ℕ) (group entry : List Char) : ℕ :=
  match group, entry with
  | ['q', 'u', 'e', 'r', 'y'], ['A'] => m * n
  | ['q', 'u', 'e', 'r', 'y'], ['b'] => m
  | ['p', 'a', 'd'], ['A'] => (m + 2) * (n + 2)
  | ['p', 'a', 'd'], ['b'] => m + 2
  | ['s', 'e', 'a', 'r', 'c', 'h'], ['r', 'o', 'w', 's'] => ((m + 2) + (n + 2)) * (n + 2)
  | ['s', 'e', 'a', 'r', 'c', 'h'], ['r', 'h', 's'] => (m + 2) + (n + 2)
  | ['e', 'l', 'l'], ['c', 'e', 'n', 't', 'e', 'r'] | ['e', 'l', 'l'], ['u'] | ['e', 'l', 'l'], ['n', 'e', 'x', 't', 'c', 'e', 'n', 't', 'e', 'r'] | ['e', 'l', 'l'], ['n', 'o', 'r', 'm', 'a', 'l'] => n + 2
  | ['e', 'l', 'l'], ['s', 'h', 'a', 'p', 'e'] | ['e', 'l', 'l'], ['n', 'e', 'x', 't', 's', 'h', 'a', 'p', 'e'] => (n + 2) * (n + 2)
  | ['e', 'l', 'l'], ['c', 'o', 'e', 'f', 'f'] => 5
  | _, _ => 0

def decisionLength (m n : ℕ) (group entry : List Char) : ℕ :=
  match group, entry with
  | ['l', 'p'], ['A'] | ['i', 'n', 't'], ['A'] => m * n
  | ['l', 'p'], ['b'] | ['i', 'n', 't'], ['b'] => m
  | ['l', 'p'], ['c'] | ['i', 'n', 't'], ['c'] => n
  | _, _ => feasibilityLength m n group entry

def recoveryLength (r s N : ℕ) (group entry : List Char) : ℕ :=
  match group, entry with
  | ['c', 'f'], ['s', 't', 'a', 'c', 'k'] => N
  | ['s', 'y', 's', 't', 'e', 'm'], ['A'] => r * s
  | ['s', 'y', 's', 't', 'e', 'm'], ['b'] => r
  | ['p', 'o', 'i', 'n', 't'], ['A'] => (r + r) * (s + r)
  | ['p', 'o', 'i', 'n', 't'], ['b'] => r + r
  | ['p', 'o', 'i', 'n', 't'], ['x'] => s + r
  | _, _ => decisionLength ((r + r) + ((s + r) + (s + r)) + 1) (s + r) group entry

def extent (m n N r s : ℕ) (a : String) : ℕ :=
  match splitChars a.toList with
  | [['l', 'p'], ['A'], _] | [['i', 'n', 't'], ['A'], _] => r * s
  | [['l', 'p'], ['b'], _] | [['i', 'n', 't'], ['b'], _] => r
  | [['l', 'p'], ['c'], _] | [['i', 'n', 't'], ['c'], _] => s
  | [['s', 'o', 'u', 'r', 'c', 'e'], ['A'], _] => m * n
  | [['s', 'o', 'u', 'r', 'c', 'e'], ['b'], _] => m
  | [['s', 'o', 'u', 'r', 'c', 'e'], ['c'], _] => n
  | [['o', 'p', 't', 'i', 'm', 'a', 'l'], ['r', 'e', 'c', 'o', 'v', 'e', 'r', 'y'], group, entry, _] | [['o', 'p', 't', 'i', 'm', 'a', 'l'], ['r', 'e', 'c', 'o', 'v', 'e', 'r', 'y'], group, entry] =>
    recoveryLength (m + (n + 2)) (n + m) N group entry
  | [['o', 'p', 't', 'i', 'm', 'a', 'l'], ['d', 'e', 'c', 'i', 's', 'i', 'o', 'n'], group, entry, _] => decisionLength (m + (n + 2)) (n + m) group entry
  | [['i', 'n', 'f', 'e', 'a', 's', 'i', 'b', 'l', 'e'], ['r', 'e', 'c', 'o', 'v', 'e', 'r', 'y'], group, entry, _] | [['i', 'n', 'f', 'e', 'a', 's', 'i', 'b', 'l', 'e'], ['r', 'e', 'c', 'o', 'v', 'e', 'r', 'y'], group, entry] =>
    recoveryLength (n + 1) m N group entry
  | [['i', 'n', 'f', 'e', 'a', 's', 'i', 'b', 'l', 'e'], ['d', 'e', 'c', 'i', 's', 'i', 'o', 'n'], group, entry, _] => decisionLength (n + 1) m group entry
  | [['u', 'n', 'b', 'o', 'u', 'n', 'd', 'e', 'd'], ['r', 'e', 'c', 'o', 'v', 'e', 'r', 'y'], group, entry, _] | [['u', 'n', 'b', 'o', 'u', 'n', 'd', 'e', 'd'], ['r', 'e', 'c', 'o', 'v', 'e', 'r', 'y'], group, entry] =>
    recoveryLength (m + (m + 1)) (n + n) N group entry
  | _ => 0

def ext (xs : List ℕ) : String → ℕ := extent (xs.headD 0) (xs.tail.headD 0)
  (stackLength (Lax759944.BinaryWordEncoding.bitSize xs))
  (if RamReadHeader.ValidDimensions xs then xs.headD 0 else 0)
  (if RamReadHeader.ValidDimensions xs then xs.tail.headD 0 else 0)

theorem allocated (m n N r s : ℕ) (tape : List ℕ) :
    RamEllipsoidStep.Extents "lp.A" (r * s) (initEnv (extent m n N r s) tape) ∧
    RamEllipsoidStep.Extents "lp.b" r (initEnv (extent m n N r s) tape) ∧
    RamEllipsoidStep.Extents "lp.c" s (initEnv (extent m n N r s) tape) ∧
    RamEllipsoidStep.Extents "int.A" (r * s) (initEnv (extent m n N r s) tape) ∧
    RamEllipsoidStep.Extents "int.b" r (initEnv (extent m n N r s) tape) ∧
    RamEllipsoidStep.Extents "int.c" s (initEnv (extent m n N r s) tape) ∧
    RamEllipsoidStep.Extents "source.A" (m * n) (initEnv (extent m n N r s) tape) ∧
    RamEllipsoidStep.Extents "source.b" m (initEnv (extent m n N r s) tape) ∧
    RamEllipsoidStep.Extents "source.c" n (initEnv (extent m n N r s) tape) ∧
    All m n N (initEnv (extent m n N r s) tape) := by
  simp only [All, Recovery, Decision, RamRecoveryThreshold.Workspace, RamRecoveryQuery.Extent,
    RamFeasibilityQuery.Workspace, RamEllipsoidStep.Workspace, recoveryView,
    RamCertificateDecision.prefixedView, RamArrayRelabel.view]
  repeat' apply And.intro
  all_goals try intro t ht
  all_goals try (simp only [List.mem_cons, List.not_mem_nil, or_false] at ht)
  all_goals try (rcases ht with rfl | rfl | rfl)
  all_goals simp only [initEnv, List.length_replicate]
  all_goals try simp [RamCertificateArrayRelabel.relabel, RamCertificateArrayRelabel.sourceNames]
  all_goals rfl

theorem initialized (xs : List ℕ) (B : ℕ) (hB : ∀ v ∈ xs.length :: xs, v < B) :
    RamSolverTotalExecution.Input B xs (initEnv (ext xs) (xs.length :: xs)) := by
  have h := allocated (xs.headD 0) (xs.tail.headD 0) (stackLength (Lax759944.BinaryWordEncoding.bitSize xs))
    (if RamReadHeader.ValidDimensions xs then xs.headD 0 else 0)
    (if RamReadHeader.ValidDimensions xs then xs.tail.headD 0 else 0) (xs.length :: xs)
  by_cases hd : RamReadHeader.ValidDimensions xs
  all_goals simp only [hd, ↓reduceIte] at h
  all_goals rcases h with ⟨hA, hb, hc, hIA, hIb, hIc, hSA, hSb, hSc, hAll⟩
  all_goals refine ⟨⟨⟨rfl, hB, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  all_goals simp only [ext, hd, ↓reduceIte]
  all_goals assumption

end Lax109476Proofs.RamSolverAllocation

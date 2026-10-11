# Executable component checks

From the submission root, run:

```sh
bash scripts/check-ram.sh
```

The script builds the required modules using the revisions pinned in the Lake files and
Lean toolchain in `proofs/`, then runs every suite. No dependency is updated.
A fresh checkout needs the usual Lean installation and network access to
fetch its pinned dependencies. Success prints `PASS` for each suite; any
failed check makes the command exit unsuccessfully. Temporary test artifacts
are removed on exit.

Each RAM suite gives the exact structured command, layout, input list, and
expected output list in executable `#guard` expressions. The shared
[`Checks/Common.lean`](Checks/Common.lean) compiles each command using
`Lax808846Proofs.Compile.compileProgram` and repeatedly applies
`Lax808846.Ram.step` to `Ram.initState input`. A check requires the exact
output and the compiler's explicit `halt` instruction before fuel runs out.
Exhausted input and an out-of-range program counter are rejected. These are
executions of the compiled registered RAM, including its word truncation,
not evaluations of the mathematical LP functions or an interpreter for the
structured language.

| Suite | Coverage | Word width | Instruction allowance per run |
| --- | --- | ---: | ---: |
| [Arithmetic](Arithmetic.lean) | GCD, reduction, integer square roots, signed rational arithmetic and comparison, bit length, grid rounding, upper square roots, canonical zero, array storage | 64 | 10,000 |
| [ContinuedFractionStep](ContinuedFractionStep.lean) | One Euclidean continued-fraction step, integral and zero cases, reduction | 64 | 10,000 |
| [Convergents](Convergents.lean) | Convergents of 13/8 at several depths, zero and integer inputs | 128 | 100,000 |
| [Reconstruction](Reconstruction.lean) | Interval reconstruction, denominator bounds, no candidate, exact endpoints and zero | 128 | 500,000 |
| [CoordinateQuery](CoordinateQuery.lean) | Coordinate-query matrix, bound and objective arrays; fixed earlier coordinate; zero source rows | 128 | 100,000 |
| [CertificateSystems](CertificateSystems.lean) | Optimal, infeasible and unbounded certificate systems, including zero rows and zero columns | 128 | 200,000 |
| [CertificateOutput](CertificateOutput.lean) | All three outcome tags, rational output vectors, zero-dimensional output and negative zero normalization | 128 | 100,000 |

For example, `Arithmetic.lean` compiles `addCommand` and checks that input
`[0,1,3,1,1,2]` produces `[1,1,6]`, representing 1/3 + (-1/2) = -1/6.
`CertificateSystems.lean` gives all entries of each expected constructed
matrix and right-hand side explicitly. Its `triples` helper merely converts
the displayed rational lists to input/output words: each rational becomes
`[sign, absolute numerator, denominator]`, with sign 1 for a negative value.
Expected systems are not computed by the builders under test.

The commands and cases preserve the checks originally run locally for the
README's component-validation claim. The shared runner additionally rejects
fuel exhaustion and premature termination. The suites supplement the formal
execution and resource proofs; they do not benchmark the complete solver.

The same script runs [FourierMotzkinProjection](FourierMotzkinProjection.lean),
a kernel-checked regression for u+t ≤ 0, -t ≤ 0. It applies the registered
proof to show that the reduced system holds exactly for u ≤ 0 and proves
that the zero row-combination matrix fails the strengthened specification.

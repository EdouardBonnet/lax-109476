#!/usr/bin/env bash
set -euo pipefail
submission_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd -- "$submission_dir/proofs"
# Lake resolves the immutable revisions pinned in lakefile.toml.
lake build Lax109476Proofs.Farkas Lax109476Proofs.RamSquareRoot \
  Lax109476Proofs.RamEncoding Lax109476Proofs.RamRounding Lax109476Proofs.RamBitLength \
  Lax109476Proofs.RamRationalArrays Lax109476Proofs.RamContinuedFractionStep \
  Lax109476Proofs.RamContinuedFractionConvergent \
  Lax109476Proofs.RamRationalReconstruction Lax109476Proofs.RamRecoveryQuery \
  Lax109476Proofs.RamCertificateFamilies Lax109476Proofs.RamWriteCertificate
checks_build=$(mktemp -d "${TMPDIR:-/tmp}/lp-ram-checks.XXXXXX")
trap 'rm -rf -- "$checks_build"' EXIT
mkdir -p -- "$checks_build/Checks"
export LEAN_PATH="$checks_build${LEAN_PATH:+:$LEAN_PATH}"
lake env lean --root="$submission_dir/checks" -o "$checks_build/Checks/Common.olean" "$submission_dir/checks/Checks/Common.lean"
for suite in Arithmetic ContinuedFractionStep Convergents Reconstruction CoordinateQuery CertificateSystems CertificateOutput; do
  lake env lean "$submission_dir/checks/$suite.lean"
  printf 'PASS %s\n' "$suite"
done
lake env lean "$submission_dir/checks/FourierMotzkinProjection.lean"
printf 'PASS FourierMotzkinProjection\n'

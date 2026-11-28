#!/usr/bin/env bash
# Usage: bash check-lean.sh /path/to/LongGapsBetweenPrimes
# Run after installing the pinned Lean toolchain and fetching the project's Mathlib cache.
set -euo pipefail
source_dir="$(cd -- "$(dirname -- "$0")" && pwd)"
upstream_dir="$(cd -- "${1:?pass the upstream project directory}" && pwd)"
cd -- "$upstream_dir"
sha256sum --check <<'HASHES'
c0061db0f6b6c8e379d002a56eec14425368e959d3d3641a4e7aad481f069625  LongGapsBetweenPrimes.lean
ffce80ac30b25f4dea863637c55be1b580e991941d2b17c6bee527a9879b0834  lake-manifest.json
302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b  lean-toolchain
HASHES
out_dir="$(mktemp -d)"
trap 'rm -rf -- "$out_dir"' EXIT
lake env lean -o "$out_dir/LongGapsBetweenPrimes.olean" LongGapsBetweenPrimes.lean
for module in SeedAverage TranslatedDivisorCover LcmSeed FactorialGain PrimeGapTranslatedCover CertifiedFactorialWindow; do
  cp -- "$source_dir/$module.lean" "$out_dir"
  lake env bash -c 'cd "$1" && LEAN_PATH="$PWD:$LEAN_PATH" lean -o "$2.olean" "$2.lean"' bash "$out_dir" "$module"
done
cat > "$out_dir/Audit.lean" <<'LEAN'
import CertifiedFactorialWindow
#print axioms CertifiedFactorialWindow.eventually_window_of_budget
LEAN
lake env bash -c 'cd "$1" && export LEAN_PATH="$PWD:$LEAN_PATH" && lean Audit.lean && leanchecker CertifiedFactorialWindow' bash "$out_dir"

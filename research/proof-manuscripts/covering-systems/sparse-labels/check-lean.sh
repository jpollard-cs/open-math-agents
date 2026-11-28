#!/bin/sh
set -eu
cd "$(dirname "$0")"
export LEAN_PATH=".:${LEAN_PATH:-}"
lean --version
for module in RectangleContraction IrreducibleSubstitution ResidueContraction IntegerSubstitution Chain FinitePackets IndexedDecisions Checked64 ModulusSet64; do
  lean -o "$module.olean" "$module.lean"
done
leanchecker --verbose RectangleContraction IrreducibleSubstitution ResidueContraction IntegerSubstitution Chain FinitePackets IndexedDecisions Checked64 ModulusSet64

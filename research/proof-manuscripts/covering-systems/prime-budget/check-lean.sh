#!/bin/sh
set -eu
cd "$(dirname "$0")"
export LEAN_PATH=".:../sparse-labels:${LEAN_PATH:-}"
lean --version
for module in Checked21 ModulusSet21 CofactorCost; do
  lean -o "$module.olean" "$module.lean"
done
leanchecker --verbose CofactorCost ModulusSet21 Checked21 IndexedDecisions FinitePackets Chain IntegerSubstitution ResidueContraction IrreducibleSubstitution RectangleContraction

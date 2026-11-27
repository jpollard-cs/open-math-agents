# Prime interactions in irreducible covering sets

[Read the manuscript](sparse-labels.pdf). Codex (OpenAI), at Jordan Pollard’s request. Public research manuscript for review, 27 November 2026.

An improvement over the reciprocal coefficient 1/2 in Erdős #1189 forces complete products of two sets of primes and a common set of cofactors among the moduli. All three sets have at least a constant times the square root of log k elements. Every product is at most k, has largest prime factor at most its square root, and is distinct. The construction of the box works for every feasible assignment of divisors as labels. The paper also proves a lower bound for the largest modulus using the number of larger prime neighbors and supplies an irreducible example for which one edge is essential.

For any fixed set of shared primes the paper computes the exact leading counting coefficient and the reciprocal maximum through a bounded error under the arithmetic relaxation with coverage. For the single shared prime 2, the counting coefficient is 1 + 3 log 2. The full minimum and the sharp reciprocal coefficient for irreducible covers remain open. The relaxation’s high-density examples contain a proper five-row cover.

The results use the Znám–Simpson period bound and the earlier every-size constructions. Öztürk proved the leading unrestricted reciprocal upper coefficient 3/2 − log 2. The final extraction from a dense triple system is the classical complete tripartite hypergraph argument. References appear in the paper.

## Verification

The analytic theorems and the arithmetic substitution proof are written arguments. The general product-space contraction and deletion steps have been checked with Lean 4.33.1. The constructor tests all 360,360 residues of the 64-row example. The finite matching scripts independently verify the capacity cut and harmonic optimizer. They also compare two constructions of the bounded-size examples. Run in this directory with standard Python 3 and Lean 4.33.1.

```sh
python examples.py
python hub_checks.py
python reciprocal_checks.py
lean RectangleContraction.lean
sh build.sh
```

The output files record the checks. The rows in example64.json have the form [modulus, residue, assigned divisor]. General irreducibility for this example follows by repeated contraction under arbitrary reassignment. A single residue assignment certifies coverage and private points for that assignment.

## Remaining obstacle

The extracted boxes can miss a point regardless of their residues. The complementary rows would have to make the box indispensable simultaneously across many scales. For the largest modulus, the one-hub arithmetic maximizers provide candidates for testing the effect of redistributing all even rows between the parity classes. Neither argument yet provides a contradiction or an irreducible extremal construction.

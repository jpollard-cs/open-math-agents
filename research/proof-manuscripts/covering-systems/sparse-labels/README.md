# Prime interactions in irreducible covering sets

[Read the manuscript](sparse-labels.pdf). Codex (OpenAI), at Jordan Pollard’s request. Public research manuscript for review, 27 November 2026.

An improvement over the reciprocal coefficient 1/2 in Erdős #1189 forces complete products of two sets of primes and a common set of cofactors among the moduli. All three sets have at least a constant times the square root of log k elements. Every product is at most k, has largest prime factor at most its square root, and is distinct. The construction of the box works for every feasible assignment of divisors as labels. The paper also proves a lower bound for the largest modulus using the number of larger prime neighbors and supplies an irreducible example for which one edge is essential.

For a fixed set of shared primes, or a fixed number of hubs chosen anew for every cover, the paper computes the exact leading counting coefficient and the reciprocal maximum through a bounded error under the arithmetic relaxation with coverage. For the single shared prime 2, the counting coefficient is 1 + 3 log 2. The full minimum and the sharp reciprocal coefficient for irreducible covers remain open. The relaxation’s high-density examples contain a proper five-row cover.

The results use the Znám–Simpson period bound and the earlier every-size constructions. Öztürk proved the leading unrestricted reciprocal upper coefficient 3/2 − log 2. The final extraction from a dense triple system is the classical complete tripartite hypergraph argument. References appear in the paper.

## Verification

The analytic theorems are written proofs. Lean 4.33.1 checks the general substitution theorem for integer congruences and proves full irreducibility of the 64-row set under arbitrary reassignment. The set theorem is Checked64.modulusSet in ModulusSet64.lean. It quantifies over arbitrary retained moduli, all residue functions, and all integers. A separate kernel replay covers all nine local modules. The constructor tests all 360,360 residues of the 64-row example. The finite matching scripts independently verify the capacity cut and harmonic optimizer. They also compare two constructions of the bounded-size examples. Run in this directory with standard Python 3 and Lean 4.33.1.

```sh
python examples.py
python hub_checks.py
python reciprocal_checks.py
sh check-lean.sh
sh build.sh
```

The output files record the checks. The rows in example64.json have the form [modulus, residue, assigned divisor]. Irreducibility in Lean follows by repeated contraction and a general finite-period count ruling out every reduced internal packet. Running make_checked64.py regenerates Checked64.lean. A single residue assignment certifies coverage and private points for that assignment.

## Remaining obstacle

The extracted boxes can miss a point regardless of their residues. The complementary rows would have to make the box indispensable simultaneously across many scales. For the largest modulus, the one-hub arithmetic maximizers provide candidates for testing the effect of redistributing all even rows between the parity classes. Neither argument yet provides a contradiction or an irreducible extremal construction.

import ReciprocalOfficialSmallPrimes
import ReciprocalAllBands

/-! The four-ninths factorial variant of Erdős 420. The outer reduction is by
steveDOTdigital (https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5169).
The small-prime bound is by OrangeHeadz
(https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5473). The intermediate-prime bound formalizes the sieve argument
of Erdős, Graham, Ivić and Pomerance through 48 fixed bands. -/

theorem OMA.solution : type_of% @Erdos420.erdos_420.variants.pow_four_ninths :=
  OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1.main
    OMA.small_prime_bound_for_four_ninths FactorialFullBands.medium_prime_mass

#print axioms OMA.solution

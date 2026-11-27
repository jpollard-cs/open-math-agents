import ReciprocalLowerBandRates
import ReciprocalLowerBandCertificate

/-! Transfer the two lower exponent pairs to the exact sets and tolerances
of the first 31 entries in the four-ninths reduction. -/
noncomputable section
open Finset Filter
namespace FactorialLowerBands
open FactorialUpperBands PrimeBlockMesh ReciprocalBandRates

/-- The first 31 intervals of the catalog's 48-band statement, from the two
full-band estimates on prime hits. All 31 rational parameter comparisons are
discharged in the finite certificate. -/
theorem lower_thirty_one (first : BandBound (1/15) (2/3) (11/15))
    (middle : BandBound (1/7) (3/7) (4/7)) :
    ∀ᶠ n : ℕ in atTop, ∀ j ∈ range 31,
      ((bandSet n j).card:ℝ) ≤ (allowance j:ℝ)*⌊(n:ℝ)^(4/9:ℝ)⌋₊ := by
  apply (eventually_all_finset _).mpr
  intro j hj
  have hj' := mem_range.mp hj
  obtain ⟨hg,hgu,ha,hab,hb,hp,hp1,hq,hs,e₁,e₂,e₃,margin⟩ := lower_band_parameters j hj'
  have bnd : BandBound (ampPower j) (endpointPower j) (modulusPower j) := by
    by_cases small : j<16
    · simpa [ampPower,endpointPower,modulusPower,small] using first
    · simpa [ampPower,endpointPower,modulusPower,small] using middle
  have out := prime_hits_of_band_bound (edge j:ℝ) (edge (j+1):ℝ) (levelPower j)
    (ampPower j) (endpointPower j) (modulusPower j) (allowance j:ℝ)
    bnd hg hgu ha hab hb hp hp1 hq hs e₁ e₂ e₃ margin
  filter_upwards [out] with n high
  have card := FactorialFourier.hit_card_le n ⌊(n:ℝ)^(4/9:ℝ)⌋₊ ((n:ℝ)^(edge j:ℝ)) ((n:ℝ)^(edge (j+1):ℝ))
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) (bandSet n j) (by
      intro z hz
      obtain ⟨hi,hband⟩ := mem_filter.mp hz
      obtain ⟨ht,hp⟩ := mem_sigma.mp hi
      have inPrime := (mem_filter.mp hp).1
      exact ⟨mem_range.mp ht,Nat.prime_of_mem_primeFactors inPrime,Nat.dvd_of_mem_primeFactors inPrime,hband⟩)
  exact card.trans high

end FactorialLowerBands
#print axioms FactorialLowerBands.lower_thirty_one

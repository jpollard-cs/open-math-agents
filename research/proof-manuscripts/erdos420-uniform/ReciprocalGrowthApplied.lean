import ReciprocalGrowthBands
import ReciprocalOfficialSmallPrimes
import ReciprocalAllBands

/-! Quantitative corollaries for the factorial-divisor ratio in the
four-ninths window, using the small-prime and 48-band bounds. -/
noncomputable section
open Filter
namespace FactorialGrowth

/-- The explicit power saving in the finite 48-band estimate. -/
theorem four_ninths_growth :
    ∀ᶠ n : ℕ in atTop, 1+(1/320000)*(n:ℝ)^(1/10000:ℝ) ≤
      Erdos420.F (fun m => (m:ℝ)^(4/9:ℝ)) n :=
  fixed_gain OMA.small_prime_bound_for_four_ninths FactorialFullBands.all_bands

/-- The ratio of divisor counts tends to infinity. -/
theorem four_ninths_tendsto :
    Tendsto (Erdos420.F (fun m => (m:ℝ)^(4/9:ℝ))) atTop atTop :=
  tendsto_of_mass OMA.small_prime_bound_for_four_ninths FactorialFullBands.medium_prime_mass

end FactorialGrowth
#print axioms FactorialGrowth.four_ninths_growth
#print axioms FactorialGrowth.four_ninths_tendsto

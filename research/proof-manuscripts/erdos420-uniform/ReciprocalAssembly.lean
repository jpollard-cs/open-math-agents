import BlockReduction
import ReciprocalUpperBands

/-! Match the 48 prime-hit inequalities to the exact hypothesis of the
four-ninths reduction, including its open and closed endpoints. -/
noncomputable section
open Finset Filter
open FactorialUpperBands PrimeBlockMesh
namespace FactorialFullBands

theorem of_lower_thirty_one
    (lower : ∀ᶠ n : ℕ in atTop, ∀ j ∈ range 31,
      ((bandSet n j).card : ℝ) ≤ (allowance j : ℝ)*⌊(n:ℝ)^(4/9:ℝ)⌋₊) :
    OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R2.H1 := by
  filter_upwards [lower,upper_seventeen] with n low high
  change ∀ j < 48, ((bandSet n j).card:ℝ) ≤ (allowance j:ℝ)*⌊(n:ℝ)^(4/9:ℝ)⌋₊
  intro j hj
  by_cases h : j<31
  · exact low j (mem_range.mpr h)
  · exact high j (mem_Ico.mpr ⟨by omega,hj⟩)

end FactorialFullBands
#print axioms FactorialFullBands.of_lower_thirty_one

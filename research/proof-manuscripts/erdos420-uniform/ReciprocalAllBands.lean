import ReciprocalAssembly
import ReciprocalProvedBandInputs
import ReciprocalLowerBands

/-! All 48 prime bands, followed by the repeated-prime-power deduction. -/
noncomputable section
namespace FactorialFullBands

theorem all_bands : OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R2.H1 :=
  of_lower_thirty_one (FactorialLowerBands.lower_thirty_one
    FactorialLowerBands.lower_band_bound FactorialLowerBands.middle_band_bound)

theorem medium_prime_mass : OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1.H2 :=
  OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R2.main all_bands
    OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R2.prime_power_removal

end FactorialFullBands
#print axioms FactorialFullBands.all_bands
#print axioms FactorialFullBands.medium_prime_mass

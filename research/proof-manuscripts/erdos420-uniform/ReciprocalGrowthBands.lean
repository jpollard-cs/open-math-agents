import PrimeBlockMesh
import ReciprocalGrowth
import BlockReduction

/-! The explicit 48-band saving and its consequence for the four-ninths ratio. -/
noncomputable section
open Filter Finset Real
open scoped Classical
open OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R2
namespace FactorialGrowth

set_option maxRecDepth 4000 in
/-- Recover the numerical witness from the 48-band count and prime-power estimate. -/
theorem mesh_saving (hcount : OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R2.H1) :
    MediumAt (1/5000) := by
  have hrepeat := prime_power_removal
  filter_upwards [hcount, hrepeat, eventually_ge_atTop (1:ℕ)] with n hc hr hn
  let h := ⌊(n:ℝ)^(4/9:ℝ)⌋₊
  let S := (range h).sigma (fun i => (n+i+1).primeFactors.filter (fun p : ℕ =>
    (n:ℝ)^(4/9:ℝ) < p ∧ (p:ℝ) ≤ (n:ℝ)^(5/9+1/10000:ℝ)))
  have sta := PrimeBlockMesh.first_power_mass S (fun z => z.2) n h hn
    (fun z hz => (mem_filter.mp (mem_sigma.mp hz).2).2) hc
  change (∑ z ∈ S, ((n+z.1+1).factorization z.2 : ℝ)*log z.2) ≤
    (∑ z ∈ S, log z.2) + (1/5000)*(h:ℝ)*log n at hr
  have bound := hr.trans (add_le_add sta le_rfl)
  have total : (∑ z ∈ S, ((n+z.1+1).factorization z.2 : ℝ)*log z.2) ≤
      (5/9-1/5000)*(h:ℝ)*log n := by linarith only [bound]
  simpa only [S, Finset.sum_sigma] using total

/-- A fixed polynomial lower bound from the full band count. -/
theorem fixed_gain (hsmall : OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1.H1)
    (hcount : OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R2.H1) :
    ∀ᶠ n : ℕ in atTop, 1+(1/320000)*(n:ℝ)^(1/10000:ℝ) ≤
      Erdos420.F (fun m => (m:ℝ)^(4/9:ℝ)) n := by
  have h := gain_of_saving hsmall (η:=1/5000) (by norm_num) (mesh_saving hcount)
  norm_num at h ⊢
  exact h

end FactorialGrowth
#print axioms FactorialGrowth.mesh_saving
#print axioms FactorialGrowth.fixed_gain

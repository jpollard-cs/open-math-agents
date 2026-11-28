import ReciprocalGeneralDyadic
import ReciprocalALocal

/-! Whole-band prime-count estimates obtained from the first and second
van der Corput A-process reciprocal estimates. -/
noncomputable section
open Real
namespace FactorialLowerBands

private theorem uniform_of_explicit (p q s C D : ℝ) (hC : 0 < C) (hD : D ≤ C)
    (block : ∀ {x t : ℕ} {u v : ℝ}, 0 < x → 0 < t → (t:ℝ) ≤ u → u ≤ v → v ≤ 3*u →
      |FactorialSieve.remainder u v x t| ≤ 
        C*(x:ℝ)^p*u^q*(t:ℝ)^(-s) + D*u^2/((x:ℝ)*t)) : FactorialDyadic.UniformSaw p q s := by
  refine ⟨C,hC,?_⟩
  intro x t hx ht u v htu huv hv
  have tp : 0 < (t:ℝ) := by exact_mod_cast ht
  have up := tp.trans_le htu
  apply (block hx ht htu huv (by linarith)).trans
  have bound := mul_le_mul_of_nonneg_right hD (show 0 ≤ u^2/((x:ℝ)*t) by positivity)
  linarith only [bound,show C*((x:ℝ)^p*u^q*(t:ℝ)^(-s)+u^2/((x:ℝ)*t)) =
    C*(x:ℝ)^p*u^q*(t:ℝ)^(-s) + C*(u^2/((x:ℝ)*t)) by ring,
    show D*u^2/((x:ℝ)*t) = D*(u^2/((x:ℝ)*t)) by ring]

/-- Whole-band estimate using the exponent pair (1/6, 2/3). -/
theorem middle_band_bound : BandBound (1/7) (3/7) (4/7) :=
  FactorialDyadic.prime_band_from_saw _ _ _ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (uniform_of_explicit _ _ _ 15000000 2073600 (by norm_num) (by norm_num)
      @FactorialFourier.reciprocal_middle_local)

/-- Whole-band estimate using the exponent pair (1/14, 11/14). -/
theorem lower_band_bound : BandBound (1/15) (2/3) (11/15) :=
  FactorialDyadic.prime_band_from_saw _ _ _ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (uniform_of_explicit _ _ _ 5000000000 320000000 (by norm_num) (by norm_num)
      @FactorialFourier.reciprocal_lower_local)

#print axioms middle_band_bound
#print axioms lower_band_bound
end FactorialLowerBands

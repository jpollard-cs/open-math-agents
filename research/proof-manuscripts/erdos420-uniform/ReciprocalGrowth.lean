import OMAReductions.R_Erdos420_erdos_420_variants_pow_four_ninths_R1

/-! Quantitative growth of the factorial-divisor ratio in the four-ninths
window. This keeps the power saving in the large-prime count rather than
converting it to the fixed doubling threshold. -/
noncomputable section
open Filter Finset Real
open scoped ArithmeticFunction.sigma Classical
open OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1

namespace FactorialGrowth

/-- The intermediate prime-mass estimate for a specified saving. -/
def MediumAt (η : ℝ) : Prop := ∀ᶠ n : ℕ in atTop,
  let h := ⌊(n:ℝ)^((4:ℝ)/9)⌋₊
  (∑ i ∈ range h, ∑ p ∈ (n+i+1).primeFactors.filter (fun p : ℕ =>
    (n:ℝ)^((4:ℝ)/9) < p ∧ (p:ℝ) ≤ (n:ℝ)^((5:ℝ)/9+1/10000)),
    ((n+i+1).factorization p : ℝ)*log p) ≤ (5/9-η)*(h:ℝ)*log n

/-- The polynomial gain at any given intermediate-prime mass saving. -/
theorem gain_of_saving (hsmall : H1) {η : ℝ} (hη : 0 < η) (hmiddle : MediumAt η) :
    ∀ᶠ n : ℕ in atTop, 1+(η/64)*(n:ℝ)^(1/10000:ℝ) ≤
      Erdos420.F (fun m => (m:ℝ)^(4/9:ℝ)) n := by
  have growth : Tendsto (fun n : ℕ => (n:ℝ)^(4/9:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hsmall (η/2) (by positivity),hmiddle,eventually_ge_atTop (2:ℕ),
      growth.eventually_ge_atTop 2] with n hs hm hn hpow
  let A := (n:ℝ)^((4:ℝ)/9)
  let B := (n:ℝ)^((5:ℝ)/9+1/10000)
  let h := ⌊A⌋₊
  let G := (range h).filter (fun i => ∃ p ∈ (n+i+1).primeFactors, B < (p:ℝ))
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hB : 0 < B := by dsimp [B]; positivity
  have hA : 2 ≤ A := hpow
  have hfloor : A < (h:ℝ)+1 := Nat.lt_floor_add_one _
  have hh : h ≤ n := by
    have hA' : A ≤ (n:ℝ)^((1:ℝ)) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    rw [Real.rpow_one] at hA'
    exact_mod_cast (Nat.floor_le (show 0 ≤ A by linarith)).trans hA'
  have hc : η*h ≤ 4*(G.card:ℝ) := count_large n h hn hh A B η hs hm
  have hsave : η*A ≤ 8*(G.card:ℝ) := by
    have he : A ≤ 2*(h:ℝ) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left he hη.le]
  have hAB : A*B = (n:ℝ)*(n:ℝ)^((1:ℝ)/10000) := by
    dsimp [A,B]
    rw [← Real.rpow_add hnR,show (4:ℝ)/9 + (5/9+1/10000) = 1+1/10000 by ring,
      Real.rpow_add hnR, Real.rpow_one]
  have hfrac : (η/64)*(n:ℝ)^((1:ℝ)/10000) ≤ (G.card:ℝ)*(B/(8*n)) := by
    have prod := mul_le_mul_of_nonneg_right hsave hB.le
    rw [mul_assoc η A B,hAB] at prod
    rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
    linarith only [prod]
  have ht : (0:ℝ) < σ 0 n.factorial := by
    exact_mod_cast ArithmeticFunction.sigma_pos 0 _ (Nat.factorial_ne_zero n)
  have hgain := gain_window n h (by omega) hh B hB.le
  change (σ 0 n.factorial:ℝ)*(1+(G.card:ℝ)*(B/(8*n))) ≤ σ 0 (n+h).factorial at hgain
  change _ ≤ (σ 0 (n+h).factorial:ℝ)/(σ 0 n.factorial:ℝ)
  apply (le_div_iff₀ ht).mpr
  rw [mul_comm _ (σ 0 n.factorial:ℝ)]
  exact (mul_le_mul_of_nonneg_left (add_le_add le_rfl hfrac) ht.le).trans hgain

/-- The registered pair of hypotheses implies an eventual lower bound
whose growth rate is a positive power of n. -/
theorem polynomial_of_mass (hsmall : H1) (hmiddle : H2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, 1+C*(n:ℝ)^(1/10000:ℝ) ≤
      Erdos420.F (fun m => (m:ℝ)^(4/9:ℝ)) n := by
  obtain ⟨η,hη,hm⟩ := hmiddle
  exact ⟨η/64,by positivity,gain_of_saving hsmall hη hm⟩

/-- The factorial-divisor ratio tends to positive infinity in this window. -/
theorem tendsto_of_mass (hsmall : H1) (hmiddle : H2) :
    Tendsto (Erdos420.F (fun m => (m:ℝ)^(4/9:ℝ))) atTop atTop := by
  obtain ⟨C,hC,ev⟩ := polynomial_of_mass hsmall hmiddle
  have growth : Tendsto (fun n : ℕ => (n:ℝ)^(1/10000:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  refine tendsto_atTop.2 (fun a => ?_)
  filter_upwards [ev,growth.eventually_ge_atTop (a/C)] with n hn hpow
  have h := (div_le_iff₀ hC).mp hpow
  linarith

end FactorialGrowth
#print axioms FactorialGrowth.gain_of_saving
#print axioms FactorialGrowth.polynomial_of_mass
#print axioms FactorialGrowth.tendsto_of_mass

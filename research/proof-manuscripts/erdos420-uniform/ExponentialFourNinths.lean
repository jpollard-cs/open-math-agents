import ReciprocalGrowthBands
import ReciprocalOfficialSmallPrimes
import ReciprocalAllBands

/-! Quantitative four-ninths growth, retaining the multiplicative gain at every
selected row. Codex, at Jordan Pollard's request. The one-row estimate and
count_large are from the project's R1 reduction. -/
noncomputable section
open Real Filter Finset
open scoped ArithmeticFunction.sigma Classical
open OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1

namespace ExponentialFourNinths

theorem log_window (n h : ℕ) (hn : 1≤n) (hh : h≤n) (B : ℝ)
    (hB : 0≤B) (cap : B≤(n:ℝ)) :
    let G := (range h).filter (fun i => ∃ p ∈ (n+i+1).primeFactors, B < (p:ℝ))
    (G.card:ℝ)*(B/(8*n))/2 ≤
      log ((σ 0 (n+h).factorial:ℝ)/(σ 0 n.factorial:ℝ)) := by
  let G := (range h).filter (fun i => ∃ p ∈ (n+i+1).primeFactors, B < (p:ℝ))
  have memG {i : ℕ} : i ∈ G ↔ i ∈ range h ∧ ∃ p ∈ (n+i+1).primeFactors, B < (p:ℝ) := by simp [G]
  let T (i : ℕ) := (σ 0 (n+i).factorial:ℝ)
  let u := B/(8*n)
  have np : 0<(n:ℝ) := by exact_mod_cast hn
  have tp (i : ℕ) : 0 < T i := by
    dsimp [T]
    exact_mod_cast ArithmeticFunction.sigma_pos 0 _ (Nat.factorial_ne_zero _)
  have u0 : 0≤u := by dsimp [u]; positivity
  have u1 : u≤1 := by dsimp [u]; rw [div_le_one (by positivity)]; linarith
  have up : 0<1+u := by linarith
  have lu : u/2 ≤ log (1+u) := by
    have base := Real.one_sub_inv_le_log_of_pos up
    have frac : u/2 ≤ u/(1+u) := by
      apply (le_div_iff₀ up).mpr
      nlinarith [mul_nonneg u0 (sub_nonneg.mpr u1)]
    have eq : u/(1+u)=1-(1+u)⁻¹ := by field_simp; ring
    linarith
  have step (i : ℕ) (hi : i ∈ range h) :
      (if i ∈ G then u/2 else 0) ≤ log (T (i+1))-log (T i) := by
    by_cases seen : i ∈ G
    · rw [if_pos seen]
      obtain ⟨p,hp,hbp⟩ := (memG.mp seen).2
      have hnum : (n:ℝ)+i+1 ≤ 2*n := by
        have := mem_range.mp hi
        exact_mod_cast (show n+i+1≤2*n by omega)
      have frac : u ≤ (p:ℝ)/(4*((n:ℝ)+i+1)) :=
        div_le_div₀ (by positivity) hbp.le (by positivity) (by linarith)
      have one := gain (n+i) p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
      push_cast at one
      change T i * (1+(p:ℝ)/(4*((n:ℝ)+i+1))) ≤ T (i+1) at one
      have prod := (mul_le_mul_of_nonneg_left (add_le_add le_rfl frac) (tp i).le).trans one
      have logs := Real.log_le_log (mul_pos (tp i) up) prod
      rw [Real.log_mul (tp i).ne' up.ne'] at logs
      linarith only [logs,lu]
    · rw [if_neg seen]
      apply sub_nonneg.mpr (Real.log_le_log (tp i) ?_)
      dsimp [T]
      exact_mod_cast (show σ 0 (n+i).factorial ≤ σ 0 (n+(i+1)).factorial by
        simp only [ArithmeticFunction.sigma_zero_apply]
        exact card_le_card (Nat.divisors_subset_of_dvd (Nat.factorial_ne_zero _)
          (Nat.factorial_dvd_factorial (by omega))))
  have total := sum_le_sum step
  have sub : ((range h).filter (· ∈ G))=G := by
    ext i
    exact ⟨fun m => (mem_filter.mp m).2, fun m => mem_filter.mpr ⟨(memG.mp m).1,m⟩⟩
  rw [← Finset.sum_filter,sub,sum_const,nsmul_eq_mul,sum_range_sub (fun i => log (T i))] at total
  have t0 : T 0 = (σ 0 n.factorial:ℝ) := by simp [T]
  change (G.card:ℝ)*u/2 ≤ log (T h/(σ 0 n.factorial:ℝ))
  rw [←t0,Real.log_div (tp h).ne' (tp 0).ne']
  linarith only [total]

theorem log_of_saving (hsmall : H1) {η : ℝ} (hη : 0 < η) (hmiddle : FactorialGrowth.MediumAt η) :
    ∀ᶠ n : ℕ in atTop, (η/128)*(n:ℝ)^(1/10000:ℝ) ≤
      Real.log (Erdos420.F (fun m => (m:ℝ)^(4/9:ℝ)) n) := by
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
  have cap : B ≤ (n:ℝ) := by
    dsimp [B]
    simpa using Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (5/9+1/10000:ℝ)≤1)
  have w := log_window n h (by omega) hh B hB.le cap
  change (G.card:ℝ)*(B/(8*n))/2 ≤ _ at w
  exact le_trans (by linarith only [hfrac] :
    (η/128)*(n:ℝ)^(1/10000:ℝ) ≤ (G.card:ℝ)*(B/(8*n))/2) w

theorem exp_growth :
    ∀ᶠ n : ℕ in atTop,
      Real.exp ((1/640000)*(n:ℝ)^(1/10000:ℝ)) ≤
        Erdos420.F (fun m => (m:ℝ)^(4/9:ℝ)) n := by
  have h := log_of_saving OMA.small_prime_bound_for_four_ninths (η:=1/5000) (by norm_num)
    (FactorialGrowth.mesh_saving FactorialFullBands.all_bands)
  rw [show (1/5000:ℝ)/128=1/640000 by norm_num] at h
  filter_upwards [h] with n bound
  have pos : 0 < Erdos420.F (fun m => (m:ℝ)^(4/9:ℝ)) n := by
    unfold Erdos420.F
    apply div_pos <;> exact_mod_cast ArithmeticFunction.sigma_pos 0 _ (Nat.factorial_ne_zero _)
  exact (Real.exp_le_exp.mpr bound).trans_eq (Real.exp_log pos)

end ExponentialFourNinths
#print axioms ExponentialFourNinths.exp_growth

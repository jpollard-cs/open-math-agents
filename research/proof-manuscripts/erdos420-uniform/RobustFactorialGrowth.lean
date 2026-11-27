import ReciprocalGrowthBands
import ReciprocalOfficialSmallPrimes
import ReciprocalAllBands
import DivisorDiminishingReturns

/-! Four-ninths divisor growth survives arbitrary deletion of at most
one in forty thousand factors in the window. Codex (AI), for Jordan Pollard. -/
noncomputable section
open Real Finset Filter
open scoped ArithmeticFunction.sigma Classical
open OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1

namespace FactorialThinning

/-- Start at n! and omit factors whose zero-based offsets belong to E. -/
def retained (n : ℕ) (E : Finset ℕ) : ℕ → ℕ
  | 0 => n.factorial
  | i+1 => if i ∈ E then retained n E i else retained n E i * (n+i+1)

theorem retained_dvd (n : ℕ) (E : Finset ℕ) (i : ℕ) : retained n E i ∣ (n+i).factorial := by
  induction i with
  | zero => simp [retained]
  | succ i ih =>
    change retained n E (i+1) ∣ (n+i+1).factorial
    rw [Nat.factorial_succ, retained]
    split
    · exact ih.trans (dvd_mul_left _ _)
    · rw [Nat.mul_comm (n+i+1)]
      exact Nat.mul_dvd_mul_right ih _

private theorem tau_pos (m : ℕ) (hm : m ≠ 0) : 0 < (σ 0 m : ℝ) := by
  exact_mod_cast ArithmeticFunction.sigma_pos 0 _ hm

private theorem log_step (a b c : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : a ∣ b) :
    log (σ 0 (b*c):ℝ) - log (σ 0 b:ℝ) ≤ log (σ 0 (a*c):ℝ) - log (σ 0 a:ℝ) := by
  have h : (σ 0 (b*c):ℝ)*(σ 0 a:ℝ) ≤ (σ 0 (a*c):ℝ)*(σ 0 b:ℝ) := by
    exact_mod_cast diminishing a b c ha hb hc hab
  have q := Real.log_le_log (mul_pos (tau_pos _ (Nat.mul_ne_zero hb hc)) (tau_pos a ha)) h
  rw [Real.log_mul (tau_pos _ (Nat.mul_ne_zero hb hc)).ne' (tau_pos _ ha).ne',
    Real.log_mul (tau_pos _ (Nat.mul_ne_zero ha hc)).ne' (tau_pos _ hb).ne'] at q
  linarith only [q]

theorem log_retained (n h : ℕ) (hn : 1 ≤ n) (hh : h ≤ n) (B : ℝ) (hB : 0≤B) (cap : B≤n)
    (E : Finset ℕ) :
    let G := (range h).filter (fun i => ∃ p ∈ (n+i+1).primeFactors, B < (p:ℝ))
    ((G \ E).card:ℝ)*(B/(8*n))/2 ≤
      log ((σ 0 (retained n E h):ℝ)/(σ 0 n.factorial:ℝ)) := by
  let G := (range h).filter (fun i => ∃ p ∈ (n+i+1).primeFactors, B < (p:ℝ))
  have memG {i : ℕ} : i ∈ G ↔ i ∈ range h ∧ ∃ p ∈ (n+i+1).primeFactors, B < (p:ℝ) := by simp [G]
  let D (i : ℕ) := (σ 0 (retained n E i):ℝ)
  let T (i : ℕ) := (σ 0 (n+i).factorial:ℝ)
  let u := B/(8*n)
  have np : 0<(n:ℝ) := by exact_mod_cast hn
  have tp (i : ℕ) : 0<T i := tau_pos _ (Nat.factorial_ne_zero _)
  have nz (i : ℕ) : retained n E i ≠ 0 := ne_zero_of_dvd_ne_zero (Nat.factorial_ne_zero _) (retained_dvd n E i)
  have dp (i : ℕ) : 0<D i := tau_pos _ (nz i)
  have u0 : 0≤u := by dsimp [u]; positivity
  have u1 : u≤1 := by dsimp [u]; rw [div_le_one (by positivity)]; linarith
  have up : 0<1+u := by linarith
  have lu : u/2 ≤ log (1+u) := by
    have base := Real.one_sub_inv_le_log_of_pos up
    have frac : u/2 ≤ u/(1+u) := by
      apply (le_div_iff₀ up).mpr
      nlinarith only [mul_nonneg u0 (sub_nonneg.mpr u1)]
    have eq : u/(1+u)=1-(1+u)⁻¹ := by field_simp; ring
    linarith only [base,frac,eq]
  have step (i : ℕ) (hi : i ∈ range h) :
      (if i ∈ G \ E then u/2 else 0) ≤ log (D (i+1))-log (D i) := by
    by_cases drop : i ∈ E
    · simp [D,retained,drop]
    have comp := log_step (retained n E i) (n+i).factorial (n+i+1) (nz i)
      (Nat.factorial_ne_zero _) (by omega) (retained_dvd n E i)
    have ff : (n+i).factorial * (n+i+1) = (n+(i+1)).factorial := by
      rw [← Nat.add_assoc, Nat.factorial_succ, Nat.mul_comm]
    rw [ff] at comp
    have kept : D (i+1) = (σ 0 ((retained n E i)*(n+i+1)):ℝ) := by simp [D,retained,drop]
    change log (T (i+1)) - log (T i) ≤ _ - log (D i) at comp
    rw [← kept] at comp
    refine le_trans ?_ comp
    by_cases seen : i ∈ G
    · rw [if_pos (Finset.mem_sdiff.mpr ⟨seen,drop⟩)]
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
    · rw [if_neg (fun m => seen (Finset.mem_sdiff.mp m).1)]
      apply sub_nonneg.mpr (Real.log_le_log (tp i) ?_)
      dsimp [T]
      exact_mod_cast (show σ 0 (n+i).factorial ≤ σ 0 (n+(i+1)).factorial by
        simp only [ArithmeticFunction.sigma_zero_apply]
        exact card_le_card (Nat.divisors_subset_of_dvd (Nat.factorial_ne_zero _)
          (Nat.factorial_dvd_factorial (by omega))))
  have total := sum_le_sum step
  have sub : ((range h).filter (· ∈ G \ E))=G \ E := by
    ext i
    exact ⟨fun m => (mem_filter.mp m).2, fun m => mem_filter.mpr ⟨(memG.mp (Finset.mem_sdiff.mp m).1).1,m⟩⟩
  rw [← Finset.sum_filter,sub,sum_const,nsmul_eq_mul,sum_range_sub (fun i => log (D i))] at total
  have d0 : D 0 = (σ 0 n.factorial:ℝ) := rfl
  change ((G \ E).card:ℝ)*u/2 ≤ log (D h/(σ 0 n.factorial:ℝ))
  rw [← d0,Real.log_div (dp h).ne' (dp 0).ne']
  linarith only [total]


/-- Localized, adversarial omissions: the exceptional set may depend on n. -/
theorem exponential_after_deletions :
    ∀ᶠ n : ℕ in atTop,
      let h := ⌊(n:ℝ)^(4/9:ℝ)⌋₊
      ∀ E : Finset ℕ, 40000 * E.card ≤ h →
        Real.exp ((1/1280000)*(n:ℝ)^(1/10000:ℝ)) ≤
          (σ 0 (retained n E h):ℝ)/(σ 0 n.factorial:ℝ) := by
  have growth : Tendsto (fun n : ℕ => (n:ℝ)^(4/9:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [OMA.small_prime_bound_for_four_ninths ((1/5000:ℝ)/2) (by positivity),
      FactorialGrowth.mesh_saving FactorialFullBands.all_bands,eventually_ge_atTop (2:ℕ),
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

  dsimp only
  intro E he
  have hc : (1/5000:ℝ)*h ≤ 4*(G.card:ℝ) := count_large n h hn hh A B (1/5000) hs hm
  have heath : (40000:ℝ)*(E.card:ℝ) ≤ (h:ℝ) := by exact_mod_cast he
  have hec : (G.card:ℝ) ≤ ((G \ E).card:ℝ)+(E.card:ℝ) := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card (s:=G) (t:=E))
  have hsave : A ≤ 80000*((G \ E).card:ℝ) := by linarith only [hc,heath,hec,hfloor,hA]
  have hAB : A*B = (n:ℝ)*(n:ℝ)^((1:ℝ)/10000) := by
    dsimp [A,B]
    rw [← Real.rpow_add hnR,show (4:ℝ)/9 + (5/9+1/10000) = 1+1/10000 by ring,
      Real.rpow_add hnR, Real.rpow_one]
  have hfrac : (1/640000:ℝ)*(n:ℝ)^((1:ℝ)/10000) ≤ ((G \ E).card:ℝ)*(B/(8*n)) := by
    have prod := mul_le_mul_of_nonneg_right hsave hB.le
    rw [hAB] at prod
    rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
    linarith only [prod]
  have cap : B ≤ (n:ℝ) := by
    dsimp [B]
    simpa using Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (5/9+1/10000:ℝ)≤1)
  have w := log_retained n h (by omega) hh B hB.le cap E
  change ((G \ E).card:ℝ)*(B/(8*n))/2 ≤ _ at w
  have bound := le_trans (by linarith only [hfrac] :
    (1/1280000:ℝ)*(n:ℝ)^(1/10000:ℝ) ≤ ((G \ E).card:ℝ)*(B/(8*n))/2) w
  have nz : retained n E h ≠ 0 := ne_zero_of_dvd_ne_zero (Nat.factorial_ne_zero _) (retained_dvd n E h)
  exact (Real.exp_le_exp.mpr bound).trans_eq (Real.exp_log (div_pos (tau_pos _ nz) (tau_pos _ (Nat.factorial_ne_zero _))))

end FactorialThinning
#print axioms FactorialThinning.exponential_after_deletions

import ReciprocalTransfer
import ReciprocalCubeRoot
import ReciprocalScale
import ReciprocalWindowExponential
import ReciprocalSecondDerivative

/-! The unconditional square-root exponent-pair case of the factorial sieve.
The final prime block bound is uniform in every admissible integer and both
real endpoints. The constants are explicit. -/
noncomputable section
open Finset Real
namespace FactorialFourier

/-- Unconditional centered sawtooth estimate on a multiplicative interval.
It gives the (1/2,1/2) case of the local estimate in EGIP's Lemma 3. -/
theorem reciprocal_cube_root {x t : ℕ} {u v : ℝ} (hx : 0 < x) (ht : 0 < t)
    (htu : (t:ℝ) ≤ u) (huv : u ≤ v) (hv : v ≤ 3*u) :
    |FactorialSieve.remainder u v x t| ≤
      280*((x:ℝ)/t)^(1/3:ℝ) + 1340*u^2/((x:ℝ)*t) := by
  let N : ℝ := ((Ioc ⌊u⌋₊ ⌊v⌋₊).filter (t ∣ ·)).card
  let E := 335*Real.sqrt ((x:ℝ)/u)
  let F := 1340*u^2/((x:ℝ)*t)
  have tp : (0:ℝ) < t := by exact_mod_cast ht
  have up := tp.trans_le htu
  have n0 : 0 ≤ N := by dsimp [N]; positivity
  have e0 : 0 ≤ E := by dsimp [E]; positivity
  have f0 : 0 ≤ F := by dsimp [F]; positivity
  have budget (H : ℕ) (hh : 1 ≤ H) :
      |FactorialSieve.remainder u v x t| ≤ N/(2*(H:ℝ)) + 2*E*Real.sqrt H + F := by
    have b := reciprocal_transfer u v x t H hh E F (1/2) e0 f0 (by norm_num) (by norm_num)
      (fun j hj => window_exponential_of_sqrt (@ReciprocalSpacing.reciprocal_sqrt_bound)
        hx ht hj htu huv hv)
    apply b.trans_eq
    rw [← Real.sqrt_eq_rpow]
    dsimp only [N]
    ring
  have opt := optimize_half_power n0 e0 f0 (remainder_le_half_card u v x t) budget
  exact opt.trans (add_le_add (scale_one_third n0 (Nat.cast_nonneg x) tp up
    (multiple_window_card ht htu huv hv)) le_rfl)

/-- A bound for the number of prime-divisor hits in one interval, with no
unproved premise on oscillatory sums. -/
theorem prime_block_sqrt (n h z : ℕ) (u v : ℝ) (hn : 0 < n) (hz : 1 ≤ z)
    (zu : (z:ℝ)^2 ≤ u) (huv : u ≤ v) (hv : v ≤ 3*u) :
    (∑ p ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime, (FactorialSieve.multiplicity n h p:ℝ)) ≤
    (h:ℝ)*log (v/u)/log ((z:ℝ)+1) + 2*h*(z:ℝ)^2/u +
      3150*((n:ℝ)+h)^(1/3:ℝ)*(z:ℝ)^(4/3:ℝ) +
      2680*u^2/(n:ℝ)*(1+log z)^3 := by
  let A := 280*((n:ℝ)+h)^(1/3:ℝ)
  let B := 1340*u^2/(n:ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have bounds (x : ℕ) (hx : x ∈ ({n,n+h} : Finset ℕ)) (t : ℕ) (ht : 1 ≤ t) (tz : t ≤ z^2) :
      |FactorialSieve.remainder u v x t| ≤ A*(t:ℝ)^(-(1/3:ℝ)) + B/t := by
    have nx : n ≤ x ∧ x ≤ n+h := by
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl|rfl <;> omega
    have xp := hn.trans_le nx.1
    have nr : (0:ℝ) < n := by exact_mod_cast hn
    have xr : (0:ℝ) < x := by exact_mod_cast xp
    have tr : (0:ℝ) < t := by exact_mod_cast ht
    have localBound := reciprocal_cube_root xp ht ((show (t:ℝ) ≤ (z:ℝ)^2 by exact_mod_cast tz).trans zu) huv hv
    refine localBound.trans (add_le_add ?_ ?_)
    · have xx : (x:ℝ)^(1/3:ℝ) ≤ ((n:ℝ)+h)^(1/3:ℝ) := by
        apply Real.rpow_le_rpow xr.le (by exact_mod_cast nx.2) (by norm_num)
      rw [Real.div_rpow xr.le tr.le,Real.rpow_neg tr.le]
      dsimp only [A]
      rw [div_eq_mul_inv,← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left xx (by norm_num)) (by positivity)
    · rw [← div_div]; dsimp only [B]
      apply div_le_div_of_nonneg_right _ tr.le
      exact div_le_div_of_nonneg_left (by positivity) nr (by exact_mod_cast nx.1)
  have total := FactorialSieve.short_interval_from_local n h z u v A B (1/3) hz zu huv hA hB
    (by norm_num) (by norm_num) bounds
  apply total.trans_eq
  dsimp only [A,B]
  norm_num
  ring

end FactorialFourier
#print axioms FactorialFourier.reciprocal_cube_root
#print axioms FactorialFourier.prime_block_sqrt

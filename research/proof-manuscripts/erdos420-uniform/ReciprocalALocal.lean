import ReciprocalAWindow
import ReciprocalPowerCutoff
import ReciprocalPowerRescale
import ReciprocalTransfer
import ReciprocalSecondA

/-! Uniform individual-modulus sawtooth bounds for the two exponent pairs
obtained by one and two applications of van der Corput differencing. -/
noncomputable section
open Finset Real
namespace FactorialFourier

private theorem local_of_pair {k l C D u v : ℝ} {x t : ℕ}
    (block : ∀ {B Y : ℝ} (N : ℕ), 1 ≤ B → 0 < Y → (N:ℝ) ≤ 2*B+1 →
      ‖∑ i ∈ range N, ReciprocalFirstDerivative.wave (Y/(B+i))‖ ≤
        C*(B^l*(Y/B^2)^k+B^2/Y))
    (hk : 0 < k) (hk1 : k < 1) (hC : 1 ≤ C) (lo : 0 ≤ l-2*k) (hi : l-2*k ≤ 1)
    (cap : (1+(1/k+1/(1-k))/2)*(3*(2*C)) ≤ D)
    (hx : 0 < x) (ht : 0 < t) (htu : (t:ℝ) ≤ u) (huv : u ≤ v) (hv : v ≤ 3*u) :
    |FactorialSieve.remainder u v x t| ≤ D*(x:ℝ)^(k/(1+k))*u^((l-k)/(1+k))*
      (t:ℝ)^(-l/(1+k)) + (4*C)*u^2/((x:ℝ)*t) := by
  let N : ℝ := ((Ioc ⌊u⌋₊ ⌊v⌋₊).filter (t ∣ ·)).card
  let E := (2*C)*(x:ℝ)^k*u^(l-2*k)*(t:ℝ)^(k-l)
  let F := (4*C)*u^2/((x:ℝ)*t)
  let c := (1/k+1/(1-k))/2
  have cp : 0 ≤ C := zero_le_one.trans hC
  have tp : (0:ℝ) < t := by exact_mod_cast ht
  have xp : (0:ℝ) < x := by exact_mod_cast hx
  have up := tp.trans_le htu
  have cn : 0 ≤ c := by dsimp [c]; have := sub_pos.mpr hk1; positivity
  have n0 : 0 ≤ N := by dsimp [N]; positivity
  have e0 : 0 ≤ E := by dsimp [E]; positivity
  have f0 : 0 ≤ F := by dsimp [F]; positivity
  have budget (H : ℕ) (hh : 1 ≤ H) :
      |FactorialSieve.remainder u v x t| ≤ N/(2*(H:ℝ)) + c*E*(H:ℝ)^k + F := by
    have b := reciprocal_transfer u v x t H hh E F k e0 f0 hk hk1
      (fun j hj => window_exponential_of_pair block cp lo hi hx ht hj htu huv hv)
    apply b.trans_eq
    dsimp only [N,c]; ring
  have opt := optimize_power n0 e0 f0 cn hk (remainder_le_half_card u v x t) budget
  have scale := rescale_local_power (l:=l) n0 e0 (show 1≤2*C by linarith) xp up tp hk.le
    (multiple_window_card ht htu huv hv) (show E ≤ (2*C)*(x:ℝ)^k*u^(l-2*k)*(t:ℝ)^(k-l) from le_rfl)
  have cap' : (1+c)*(3*(2*C)) ≤ D := cap
  calc
    _ ≤ (1+c)*((3*(2*C))*(x:ℝ)^(k/(1+k))*u^((l-k)/(1+k))*(t:ℝ)^(-l/(1+k)))+F :=
      opt.trans (add_le_add (mul_le_mul_of_nonneg_left scale (by linarith)) le_rfl)
    _ = ((1+c)*(3*(2*C)))*(x:ℝ)^(k/(1+k))*u^((l-k)/(1+k))*(t:ℝ)^(-l/(1+k))+F := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right cap' (by positivity)) (by positivity)) (by positivity)) le_rfl

/-- The one-sixth exponent pair yields the middle band estimate. -/
theorem reciprocal_middle_local {x t : ℕ} {u v : ℝ} (hx : 0 < x) (ht : 0 < t)
    (htu : (t:ℝ) ≤ u) (huv : u ≤ v) (hv : v ≤ 3*u) :
    |FactorialSieve.remainder u v x t| ≤
      15000000*(x:ℝ)^(1/7:ℝ)*u^(3/7:ℝ)*(t:ℝ)^(-(4/7:ℝ)) + 2073600*u^2/((x:ℝ)*t) := by
  have h := local_of_pair (k:=1/6) (l:=2/3) (C:=518400) (D:=15000000)
    (@FactorialReciprocal.reciprocal_first_A) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hx ht htu huv hv
  norm_num at h ⊢
  exact h

/-- Two A-process steps yield the estimate for the lowest band. -/
theorem reciprocal_lower_local {x t : ℕ} {u v : ℝ} (hx : 0 < x) (ht : 0 < t)
    (htu : (t:ℝ) ≤ u) (huv : u ≤ v) (hv : v ≤ 3*u) :
    |FactorialSieve.remainder u v x t| ≤
      5000000000*(x:ℝ)^(1/15:ℝ)*u^(2/3:ℝ)*(t:ℝ)^(-(11/15:ℝ)) + 320000000*u^2/((x:ℝ)*t) := by
  have h := local_of_pair (k:=1/14) (l:=11/14) (C:=80000000) (D:=5000000000)
    (@FactorialReciprocal.reciprocal_second_A) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hx ht htu huv hv
  norm_num at h ⊢
  exact h

end FactorialFourier
#print axioms FactorialFourier.reciprocal_middle_local
#print axioms FactorialFourier.reciprocal_lower_local

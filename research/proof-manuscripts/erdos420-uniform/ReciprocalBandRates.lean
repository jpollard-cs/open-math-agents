import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! The power savings and allowance in the upper seventeen four-ninths sieve
bands. The sieve level has exponent just below one twelfth. -/

noncomputable section
open Filter Real
namespace ReciprocalBandRates

def c : ℝ := 4/9
def gamma : ℝ := 1/12-1/1000000

def window (n : ℕ) : ℝ := ⌊(n:ℝ)^c⌋₊

def errors (n : ℕ) (a b : ℝ) : ℝ :=
  (1+log n)^4*((n:ℝ)^(c+2*gamma-a)+(n:ℝ)^(1/3+4*gamma/3)+(n:ℝ)^(2*b-1))

theorem gamma_pos : 0 < gamma := by norm_num [gamma]

/-- A logarithmic factor of degree four is absorbed by any strict gap
in exponents, even after rounding the main scale down to an integer. -/
theorem power_rate {p d ε : ℝ} (hpd : p < d) (hd : 0 < d) (he : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (1+log n)^4*(n:ℝ)^p ≤ ε*(⌊(n:ℝ)^d⌋₊ : ℝ) := by
  have small := (isLittleO_log_rpow_rpow_atTop (4:ℝ) (sub_pos.mpr hpd)).bound
    (show 0 < ε/32 by positivity)
  have hncast : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog := (tendsto_log_atTop.comp hncast).eventually_ge_atTop 1
  have hpwr := ((tendsto_rpow_atTop hd).comp hncast).eventually_ge_atTop 2
  filter_upwards [hncast.eventually small,hlog,hpwr,eventually_ge_atTop 1] with n hs hl hp hn
  change 1 ≤ log (n:ℝ) at hl
  change 2 ≤ (n:ℝ)^d at hp
  have np : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have logbound : (log (n:ℝ))^4 ≤ (ε/32)*(n:ℝ)^(d-p) := by
    simpa only [Real.rpow_ofNat,Real.norm_of_nonneg (show 0 ≤ (log (n:ℝ))^4 by positivity),
      Real.norm_of_nonneg (Real.rpow_nonneg np.le _)] using hs
  have logfour : (1+log n)^4 ≤ 16*(log n)^4 := by
    calc _ ≤ (2*log n)^4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
         _ = _ := by ring
  have floorbound : (n:ℝ)^d ≤ 2*(⌊(n:ℝ)^d⌋₊ : ℝ) := by
    linarith [Nat.lt_floor_add_one ((n:ℝ)^d)]
  calc
    _ ≤ (16*((ε/32)*(n:ℝ)^(d-p)))*(n:ℝ)^p := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg np.le _)
      exact logfour.trans (mul_le_mul_of_nonneg_left logbound (by norm_num))
    _ = (ε/2)*(n:ℝ)^d := by
      have eq : (n:ℝ)^(d-p)*(n:ℝ)^p = (n:ℝ)^d := by
        rw [← Real.rpow_add np, sub_add_cancel]
      linear_combination (ε/2)*eq
    _ ≤ ε*(⌊(n:ℝ)^d⌋₊ : ℝ) := by nlinarith [mul_le_mul_of_nonneg_left floorbound he.le]

/-- Each of the three error exponents is strictly below 4/9 throughout
the upper seventeen-band range. -/
theorem rate_gaps_wide (a b : ℝ) (ha : 1/2 ≤ a) (hb : b ≤ 50009/90000) :
    c+2*gamma-a < c ∧ 1/3+4*gamma/3 < c ∧ 2*b-1 < c := by
  unfold c gamma
  constructor
  · linarith
  constructor
  · norm_num
  · linarith

/-- Multiplying the summed dyadic errors by any fixed constant gives
eventually at most ε times the integer window length. -/
theorem eventual_errors_wide (a b C ε : ℝ) (ha : 1/2 ≤ a) (hb : b ≤ 50009/90000)
    (hC : 0 ≤ C) (he : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, C*errors n a b ≤ ε*window n := by
  have hgap := rate_gaps_wide a b ha hb
  have hc : 0<c := by norm_num [c]
  let η := ε/(3*(C+1))
  have hη : 0<η := by dsimp [η]; positivity
  have cap : 3*C*η ≤ ε := by
    dsimp only [η]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  filter_upwards [power_rate hgap.1 hc hη,power_rate hgap.2.1 hc hη,power_rate hgap.2.2 hc hη]
    with n h₁ h₂ h₃
  have hwindow : 0 ≤ window n := Nat.cast_nonneg _
  change (1+log n)^4*(n:ℝ)^_ ≤ η*window n at h₁ h₂ h₃
  have together : errors n a b ≤ 3*η*window n := by
    dsimp only [errors]
    simp only [mul_add]
    linarith only [h₁,h₂,h₃]
  calc _ ≤ C*(3*η*window n) := mul_le_mul_of_nonneg_left together hC
       _ = (3*C*η)*window n := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_right cap hwindow

theorem rate_gaps (a b : ℝ) (ha : 29/54 ≤ a) (hb : b ≤ 50009/90000) :
    c+2*gamma-a < c ∧ 1/3+4*gamma/3 < c ∧ 2*b-1 < c :=
  rate_gaps_wide a b (by linarith) hb

theorem eventual_errors (a b C ε : ℝ) (ha : 29/54 ≤ a) (hb : b ≤ 50009/90000)
    (hC : 0 ≤ C) (he : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, C*errors n a b ≤ ε*window n :=
  eventual_errors_wide a b C ε (by linarith) hb hC he

/-- The real endpoint and the floor in the sieve level leave the
expected main coefficient for the complete band. -/
theorem floor_sieve_main (n : ℕ) (hn : 2 ≤ n) (a b : ℝ) (hab : a ≤ b) :
    log ((n:ℝ)^b/(n:ℝ)^a) / log ((⌊(n:ℝ)^gamma⌋₊ : ℝ)+1) ≤ (b-a)/gamma := by
  have nr : 1 < (n:ℝ) := by exact_mod_cast (show 1 < n by omega)
  have np : 0 < (n:ℝ) := by linarith
  have lp := Real.log_pos nr
  have flo := Nat.lt_floor_add_one ((n:ℝ)^gamma)
  have logfloor := Real.log_le_log (Real.rpow_pos_of_pos np gamma) flo.le
  rw [Real.log_rpow np] at logfloor
  have gp := gamma_pos
  have prod := mul_pos gp lp
  have pos : 0 < log ((⌊(n:ℝ)^gamma⌋₊ : ℝ)+1) := prod.trans_le logfloor
  rw [log_div (Real.rpow_pos_of_pos np _).ne' (Real.rpow_pos_of_pos np _).ne',
      Real.log_rpow np,Real.log_rpow np,div_le_div_iff₀ pos gp]
  nlinarith [mul_le_mul_of_nonneg_left logfloor (sub_nonneg.mpr hab)]

/-- Exact coefficient surplus from choosing a level with a strict power saving. -/
theorem reciprocal_surplus : 1/gamma-12 = 36/249997 := by norm_num [gamma]

/-- The loss from reducing the level exponent from 1/12 to gamma uses
less than half the project's additive band allowance. -/
theorem allowance_margin (w : ℝ) (hw : w ≤ 1/500) :
    w/gamma + 1/2000000 ≤ 12*w + 1/1000000 := by
  norm_num [gamma]
  linarith

/-- An asymptotic block estimate with the three explicit errors gives the
project's exact band allowance at every sufficiently large integer start. -/
theorem band_from_errors (T : ℕ → ℝ) (a b C : ℝ) (ha : 29/54 ≤ a) (hb : b ≤ 50009/90000)
    (hw : b-a ≤ 1/500) (hC : 0 ≤ C)
    (bound : ∀ᶠ n : ℕ in atTop, T n ≤ ((b-a)/gamma)*window n + C*errors n a b) :
    ∀ᶠ n : ℕ in atTop, T n ≤ ((b-a)*12+1/1000000)*window n := by
  filter_upwards [bound,eventual_errors a b C (1/2000000) ha hb hC (by norm_num)] with n h₁ h₂
  have m := allowance_margin (b-a) hw
  have ww : 0 ≤ window n := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right m ww]

/-- A band in the middle exponent-pair range ends exactly at the breakpoint,
where its allowance is also 12. Its width fits this wider margin. -/
theorem allowance_margin_wide (w : ℝ) (hw : w ≤ 1/250) :
    w/gamma + 1/4000000 ≤ 12*w + 1/1000000 := by
  norm_num [gamma]
  linarith

theorem band_from_errors_wide (T : ℕ → ℝ) (a b C : ℝ) (ha : 1/2 ≤ a) (hb : b ≤ 50009/90000)
    (hw : b-a ≤ 1/250) (hC : 0 ≤ C)
    (bound : ∀ᶠ n : ℕ in atTop, T n ≤ ((b-a)/gamma)*window n + C*errors n a b) :
    ∀ᶠ n : ℕ in atTop, T n ≤ ((b-a)*12+1/1000000)*window n := by
  filter_upwards [bound,eventual_errors_wide a b C (1/4000000) ha hb hC (by norm_num)] with n h₁ h₂
  have m := allowance_margin_wide (b-a) hw
  have ww : 0 ≤ window n := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right m ww]

end ReciprocalBandRates
#print axioms ReciprocalBandRates.band_from_errors
#print axioms ReciprocalBandRates.floor_sieve_main
#print axioms ReciprocalBandRates.band_from_errors_wide

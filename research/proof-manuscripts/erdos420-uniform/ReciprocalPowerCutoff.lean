import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Balancing the integer Fourier cutoff for every exponent 0<k<1.
The coefficient retains its full dependence on k, including the two
exponents 1/6 and 1/14 in the short factorial interval. -/

noncomputable section
namespace FactorialFourier

/-- Passing from an oscillatory bound of size E j^k + F/j to a centered
sawtooth sum trades the frequency power k for k/(1+k). -/
theorem optimize_power {R N E F C k : ℝ} (hN : 0 ≤ N) (hE : 0 ≤ E)
    (hF : 0 ≤ F) (hC : 0 ≤ C) (hk : 0 < k)
    (trivial : R ≤ N/2)
    (budget : ∀ H : ℕ, 1 ≤ H → R ≤ N/(2*(H:ℝ))+C*E*(H:ℝ)^k+F) :
    R ≤ (1+C)*(N^(k/(1+k))*E^(1/(1+k)))+F := by
  let p := 1/(1+k)
  let q := k/(1+k)
  let P := N^q*E^p
  have pp : 0<p := by dsimp [p]; positivity
  have qp : 0<q := by dsimp [q]; positivity
  have ps : q+p=1 := by dsimp [p,q]; field_simp; ring
  have pk : p*k=q := by dsimp [p,q]; ring
  have Pn : 0 ≤ P := by dsimp [P]; positivity
  change R ≤ (1+C)*P+F
  by_cases e : E=0
  · subst E
    have eq : P=0 := by dsimp [P]; rw [Real.zero_rpow pp.ne',mul_zero]
    rw [eq,mul_zero,zero_add]
    by_contra! bad
    have dp := sub_pos.mpr bad
    obtain ⟨H,high⟩ := exists_nat_gt (max 1 (N/(R-F)))
    have one := (le_max_left (1:ℝ) (N/(R-F))).trans_lt high
    have hp : (1:ℝ) ≤ H := one.le
    have h := budget H (by exact_mod_cast hp)
    simp only [mul_zero,zero_mul,add_zero] at h
    have s := (div_lt_iff₀ dp).mp ((le_max_right (1:ℝ) (N/(R-F))).trans_lt high)
    have top : N/(2*(H:ℝ)) < R-F := by
      apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith [mul_pos (show 0<(H:ℝ) by linarith) dp]
    linarith
  have ep : 0<E := lt_of_le_of_ne hE (Ne.symm e)
  by_cases small : N≤E
  · have nle : N≤P := by
      calc N = N^q*N^p := by rw [← Real.rpow_add_of_nonneg hN qp.le pp.le,ps,Real.rpow_one]
           _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hN small pp.le) (by positivity)
    nlinarith only [nle,trivial,hN,hF,mul_nonneg hC Pn]
  have np : 0<N := ep.trans (lt_of_not_ge small)
  let a := (N/E)^p
  have a1 : 1 ≤ a := Real.one_le_rpow ((one_le_div ep).mpr (le_of_not_ge small)) pp.le
  have ea : E*a^k=P := by
    dsimp only [a,P]
    rw [← Real.rpow_mul (div_nonneg hN hE),pk,Real.div_rpow hN hE]
    have ef : E^q*E^p=E := by rw [← Real.rpow_add ep,ps,Real.rpow_one]
    have eq := (Real.rpow_pos_of_pos ep q).ne'
    field_simp
    linear_combination -ef
  have pa : P*a=N := by
    dsimp only [a,P]
    rw [Real.div_rpow hN hE]
    have nf : N^q*N^p=N := by rw [← Real.rpow_add np,ps,Real.rpow_one]
    have epow := (Real.rpow_pos_of_pos ep p).ne'
    field_simp
    linear_combination nf
  let H := ⌊a⌋₊
  have hH : 1 ≤ H := Nat.floor_pos.mpr a1
  have hHr : (1:ℝ) ≤ H := by exact_mod_cast hH
  have hpos : (0:ℝ) < H := by linarith
  have lo : (H:ℝ)≤a := Nat.floor_le (zero_le_one.trans a1)
  have hi : a≤2*(H:ℝ) := by linarith [Nat.lt_floor_add_one a]
  have inv : N/(2*(H:ℝ)) ≤ P := (div_le_iff₀ (by positivity)).mpr
    (by rw [← pa]; exact mul_le_mul_of_nonneg_left hi Pn)
  have growth : E*(H:ℝ)^k ≤ P := ea ▸ mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hpos.le lo hk.le) hE
  have ce := mul_le_mul_of_nonneg_left growth hC
  have h := budget H hH
  nlinarith only [h,ce,inv]

end FactorialFourier
#print axioms FactorialFourier.optimize_power

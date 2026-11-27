import ReciprocalDifferencing
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Parameter optimization for a van der Corput A-step after a square-root
estimate. Below the crossover the original bound is sufficient. Above it
the single worst inverse-lag error fits into the diagonal budget. -/

noncomputable section
namespace ReciprocalAProcess

/-- The integer differencing scale in a square-root to one-sixth transition.
Here X denotes frequency divided by the square of the denominator scale M. -/
theorem first_A {M X K S : ℝ} {N : ℕ} (hM : 1 ≤ M) (hX : 0 < X)
    (hK : 1 ≤ K) (len : (N:ℝ) ≤ 3*M) (trivial : S ≤ N)
    (base : S ≤ K*(Real.sqrt (M*X)+1/X))
    (shifted : ∀ H : ℕ, 1 ≤ H → (H:ℝ) ≤ M →
      (H:ℝ)*S^2 ≤ ((N:ℝ)+H)*((N:ℝ)+H*K*(Real.sqrt (H*X)+M/X))) :
    S ≤ 8*K*(M^(2/3:ℝ)*X^(1/6:ℝ)+1/X) := by
  have m : 0<M := by linarith
  have kp : 0<K := by linarith
  let T := (M*X)^(1/3:ℝ)
  let W := Real.sqrt (M*T)
  have tp : 0<T := Real.rpow_pos_of_pos (mul_pos m hX) _
  have wp : 0<W := Real.sqrt_pos.mpr (mul_pos m tp)
  have cube : T^3=M*X := by
    dsimp [T]
    rw [← Real.rpow_mul_natCast (mul_nonneg m.le hX.le)]
    norm_num
  have ws : W^2=M*T := Real.sq_sqrt (mul_nonneg m.le tp.le)
  have powers : W=M^(2/3:ℝ)*X^(1/6:ℝ) := by
    dsimp [W,T]
    rw [Real.sqrt_eq_rpow,Real.mul_rpow m.le (by positivity),← Real.rpow_mul (by positivity),
      Real.mul_rpow m.le hX.le,← mul_assoc,← Real.rpow_add m]
    norm_num
  rw [← powers]
  have invpos : 0<1/X := one_div_pos.mpr hX
  have costnon : 0 ≤ K*(W+1/X) := by positivity
  by_cases small : X^2≤M
  · have XT : X≤T := by
      apply le_of_not_gt
      intro lt
      have q := pow_lt_pow_left₀ lt tp.le (by decide : 3≠0)
      nlinarith [mul_le_mul_of_nonneg_right small hX.le]
    have Wb : Real.sqrt (M*X) ≤ W := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left XT m.le)
    have := base.trans (mul_le_mul_of_nonneg_left (add_le_add Wb (le_refl (1/X))) kp.le)
    nlinarith only [this,costnon]
  by_cases high : M^2≤X
  · have MT : M≤T := by
      by_contra! lt
      have q := pow_lt_pow_left₀ lt tp.le (by decide : 3≠0)
      nlinarith [mul_le_mul_of_nonneg_left high m.le]
    have MW : M≤W := by
      by_contra! lt
      have q := pow_lt_pow_left₀ lt wp.le (by decide : 2≠0)
      nlinarith [mul_le_mul_of_nonneg_left MT m.le]
    have Wle := mul_le_mul_of_nonneg_right hK (show 0≤W+1/X by positivity)
    nlinarith only [trivial,len,MW,invpos.le,Wle,costnon]
  have sx : M<X^2 := lt_of_not_ge small
  have lx : X<M^2 := lt_of_not_ge high
  have x1 : 1≤X := by
    by_contra! bad
    have q := mul_lt_mul_of_pos_right bad hX
    nlinarith
  have t1 : 1≤T := by
    by_contra! lt
    have q := pow_lt_pow_left₀ lt tp.le (by decide : 3≠0)
    nlinarith [mul_le_mul hM x1 (by norm_num) m.le]
  have tm : T≤M := by
    by_contra! lt
    have q := pow_lt_pow_left₀ lt m.le (by decide : 3≠0)
    nlinarith [mul_lt_mul_of_pos_left lx m]
  have invcost : M/X ≤ T := by
    apply (div_le_iff₀ hX).mpr
    by_contra! lt
    have q := pow_lt_pow_left₀ lt (mul_nonneg tp.le hX.le) (by decide : 3≠0)
    rw [mul_pow,cube] at q
    have sqbound := mul_lt_mul_of_pos_right sx (by positivity : 0<X^2)
    have msq := mul_lt_mul_of_pos_left sx m
    have mc := mul_lt_mul_of_pos_left (msq.trans sqbound) m
    nlinarith only [q,mc]
  let H := ⌊M/T⌋₊
  have ratio : 1≤M/T := (one_le_div tp).mpr tm
  have hH : 1≤H := Nat.floor_pos.mpr ratio
  have hp : (0:ℝ)<H := by exact_mod_cast hH
  have hfloor : (H:ℝ) ≤ M/T := Nat.floor_le (div_nonneg m.le tp.le)
  have hMT : (H:ℝ)*T ≤ M := (le_div_iff₀ tp).mp hfloor
  have hcap : (H:ℝ) ≤ M := hfloor.trans (div_le_self m.le t1)
  have upper : M ≤ 2*(H:ℝ)*T := by
    have q := Nat.lt_floor_add_one (M/T)
    have z : M/T < 2*H := by linarith [show (1:ℝ) ≤ H by exact_mod_cast hH]
    exact (div_lt_iff₀ tp).mp z |>.le
  have growth : Real.sqrt ((H:ℝ)*X) ≤ T := by
    have h := mul_le_mul_of_nonneg_right hMT hX.le
    have hx : (H:ℝ)*X ≤ T^2 := (le_of_mul_le_mul_right (by
      calc _ = (H:ℝ)*T*X := by ring
           _ ≤ M*X := h
           _ = T^2*T := by rw [← cube]; ring) tp)
    exact (Real.sqrt_le_iff).mpr ⟨tp.le,hx⟩
  have raw := shifted H hH hcap
  have c1 : (N:ℝ)+H ≤ 4*M := by linarith
  have c2 : (N:ℝ)+H*K*(Real.sqrt ((H:ℝ)*X)+M/X) ≤ (H:ℝ)*T*(6+2*K) := by
    have c := mul_le_mul_of_nonneg_left (add_le_add growth invcost) (mul_nonneg hp.le kp.le)
    nlinarith only [c,len,upper]
  have rhs := mul_le_mul c1 c2 (by positivity) (by positivity)
  have ss : S^2 ≤ (4*M*T)*(6+2*K) := by
    apply le_of_mul_le_mul_left _ hp
    apply raw.trans (rhs.trans_eq ?_)
    ring
  have Ksq : 1≤K^2 := by nlinarith [sq_nonneg (K-1)]
  have ksq2 : K ≤ K^2 := by nlinarith [mul_nonneg kp.le (sub_nonneg.mpr hK)]
  have main : S ≤ 8*K*W := by
    by_contra! lt
    have q := pow_lt_pow_left₀ lt (by positivity : 0 ≤ 8*K*W) (by decide : 2≠0)
    have bound : 4*(6+2*K) ≤ 64*K^2 := by linarith
    have big := mul_le_mul_of_nonneg_right bound (mul_nonneg m.le tp.le)
    rw [mul_pow,mul_pow,ws] at q
    nlinarith only [q,big,ss]
  have add := mul_nonneg kp.le invpos.le
  nlinarith only [main,add]


/-- A shifted square-root bound yields the exponent pair (1/6,2/3)
on the original finite exponential sum. -/
theorem first_A_character (p : ℕ → ℝ) (N : ℕ) {M X K : ℝ}
    (hM : 1≤M) (hX : 0<X) (hK : 1≤K) (len : (N:ℝ) ≤ 3*M)
    (base : ‖∑ j ∈ Finset.range N, FactorialDifferencing.character (p j)‖ ≤
      K*(Real.sqrt (M*X)+1/X))
    (shifts : ∀ d : ℕ, 0<d → (d:ℝ) ≤ M →
      ‖∑ j ∈ Finset.range (N-d),FactorialDifferencing.character (p (j+d)-p j)‖ ≤
        K*(Real.sqrt ((d:ℝ)*X)+M/((d:ℝ)*X))) :
    ‖∑ j ∈ Finset.range N,FactorialDifferencing.character (p j)‖ ≤
      8*K*(M^(2/3:ℝ)*X^(1/6:ℝ)+1/X) := by
  refine first_A hM hX hK len ?_ base ?_
  · calc _ ≤ ∑ j ∈ Finset.range N, ‖FactorialDifferencing.character (p j)‖ := norm_sum_le _ _
         _ = (N:ℝ) := by simp only [show ∀ x, ‖FactorialDifferencing.character x‖=1 from
           fun x => Complex.norm_exp_ofReal_mul_I _, Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
  intro H hH hcap
  let E := K*(Real.sqrt ((H:ℝ)*X)+M/X)
  have pos : (0:ℝ)<H := by exact_mod_cast hH
  have epos : 0≤E := by dsimp [E]; positivity
  have each (d : ℕ) (hd : 0<d) (dh : d<H) :
      ‖∑ j ∈ Finset.range (N-d),FactorialDifferencing.character (p (j+d)-p j)‖ ≤ E := by
    have dx : (d:ℝ) ≤ H := by exact_mod_cast dh.le
    have d1 : (1:ℝ) ≤ d := by exact_mod_cast hd
    apply (shifts d hd (dx.trans hcap)).trans
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    apply add_le_add (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right dx hX.le))
    apply div_le_div_of_nonneg_left (by linarith) hX
    simpa using mul_le_mul_of_nonneg_right d1 hX.le
  have c := FactorialDifferencing.uniform_differencing p N H hH E each
  have fa : ((N+H-1:ℕ):ℝ) ≤ (N:ℝ)+H := by exact_mod_cast (show N+H-1 ≤ N+H by omega)
  have h₁ : 1 ≤ (H:ℝ) := by exact_mod_cast hH
  have fb : (N:ℝ)+((H:ℝ)-1)*E ≤ N+H*K*(Real.sqrt (H*X)+M/X) := by
    rw [mul_assoc]
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_right (by linarith) epos
  exact c.trans (mul_le_mul fa fb (add_nonneg (Nat.cast_nonneg _) (mul_nonneg (sub_nonneg.mpr h₁) epos))
    (by positivity))

end ReciprocalAProcess
#print axioms ReciprocalAProcess.first_A
#print axioms ReciprocalAProcess.first_A_character

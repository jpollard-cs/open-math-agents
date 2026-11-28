import ReciprocalDifferencing
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! Optimize an integer van der Corput shift for the second A-step.
M is the reference interval length, X the effective first difference of
the phase. Finite sums can occupy any shorter interval of length at most 3M.
The resulting exponents are (1/14,11/14). -/

noncomputable section
open Finset Real
namespace FactorialDifferencing

private lemma log_monomial {M X : ℝ} (hM : 0 < M) (hX : 0 < X) (a b : ℝ) :
    log (M^a*X^b) = a*log M+b*log X := by
  rw [log_mul (rpow_pos_of_pos hM _).ne' (rpow_pos_of_pos hX _).ne',
    log_rpow hM,log_rpow hX]

/-- Integer shift optimization converting the first A bound to the second.
The input estimate must hold for every integer shift length up to M. -/
theorem optimize_second_A {M X K S : ℝ} {N : ℕ} (hm : 1 ≤ M) (hx : 0 < X)
    (hk : 1 ≤ K) (hn : (N:ℝ) ≤ 3*M) (trivial_bound : S ≤ N)
    (previous : S ≤ K*(M^(2/3:ℝ)*X^(1/6:ℝ)+1/X))
    (step : ∀ H : ℕ, 1 ≤ H → (H:ℝ) ≤ M →
      (H:ℝ)*S^2 ≤ ((N:ℝ)+H)*((N:ℝ)+H*K*(M^(1/2:ℝ)*((H:ℝ)*X)^(1/6:ℝ)+M/X))) :
    S ≤ 8*K*(M^(11/14:ℝ)*X^(1/14:ℝ)+1/X) := by
  have mp : 0 < M := by linarith
  have kp : 0 < K := by linarith
  let T := M^(11/14:ℝ)*X^(1/14:ℝ)
  have tp : 0 < T := by dsimp [T]; positivity
  have lt' : log T = (11/14:ℝ)*log M+(1/14:ℝ)*log X := log_monomial mp hx _ _
  have ml := log_nonneg hm
  have extend (hs : S ≤ 8*K*T) : S ≤ 8*K*(T+1/X) := by
    exact hs.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity))
  by_cases small : X ≤ M^(5/4:ℝ)
  · have l := log_le_log hx small
    rw [log_rpow mp] at l
    have le : M^(2/3:ℝ)*X^(1/6:ℝ) ≤ T := by
      apply (log_le_log_iff (by positivity) tp).mp
      rw [log_monomial mp hx,lt']
      linarith
    apply previous.trans
    calc K*(M^(2/3:ℝ)*X^(1/6:ℝ)+1/X) ≤ K*(T+1/X) :=
           mul_le_mul_of_nonneg_left (add_le_add le le_rfl) kp.le
         _ ≤ 8*K*(T+1/X) := by gcongr; linarith
  have lsmall := log_le_log (rpow_pos_of_pos mp (5/4)) (le_of_not_ge small)
  rw [log_rpow mp] at lsmall
  by_cases large : M^3 ≤ X
  · have l := log_le_log (pow_pos mp 3) large
    rw [log_pow] at l
    have mt : M ≤ T := by
      apply (log_le_log_iff mp tp).mp
      rw [lt']
      norm_num at l ⊢
      linarith
    apply extend
    calc S ≤ (N:ℝ) := trivial_bound
         _ ≤ 3*M := hn
         _ ≤ 8*K*T := mul_le_mul (by linarith) mt mp.le (by positivity)
  have llarge := log_le_log hx (le_of_not_ge large)
  rw [log_pow] at llarge
  let Y := M^(3/7:ℝ)*X^(-(1/7):ℝ)
  let U := M^(4/7:ℝ)*X^(1/7:ℝ)
  have yp : 0 < Y := by dsimp [Y]; positivity
  have up : 0 < U := by dsimp [U]; positivity
  have ly : log Y = (3/7:ℝ)*log M+(-(1/7):ℝ)*log X := log_monomial mp hx _ _
  have lu : log U = (4/7:ℝ)*log M+(1/7:ℝ)*log X := log_monomial mp hx _ _
  have ylo : 1 ≤ Y := by
    apply (log_le_log_iff one_pos yp).mp
    rw [log_one,ly]; norm_num at llarge; linarith
  have ym : Y ≤ M := by
    apply (log_le_log_iff yp mp).mp
    rw [ly]; linarith
  have yx : Y ≤ X := by
    apply (log_le_log_iff yp hx).mp
    rw [ly]; linarith
  have product : Y*U = M := by
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (mul_pos yp up)) mp
    rw [log_mul yp.ne' up.ne',ly,lu]; ring
  have Tsq : T^2 = M*U := by
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (pow_pos tp 2)) (Set.mem_Ioi.mpr (mul_pos mp up))
    rw [log_pow, log_mul mp.ne' up.ne',lt',lu]; norm_num; ring
  have power_eq : M^(1/2:ℝ)*(Y*X)^(1/6:ℝ) = U := by
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) up
    rw [log_mul (rpow_pos_of_pos mp _).ne' (rpow_pos_of_pos (mul_pos yp hx) _).ne',
        log_rpow mp,log_rpow (mul_pos yp hx),log_mul yp.ne' hx.ne',ly,lu]
    ring
  let H := ⌊Y⌋₊
  have h1 : 1 ≤ H := Nat.floor_pos.mpr ylo
  have Hp : 0 < (H:ℝ) := by exact_mod_cast (show 0 < H by omega)
  have hy : (H:ℝ) ≤ Y := Nat.floor_le yp.le
  have floor_lower : Y ≤ 2*(H:ℝ) := by
    have lo : (1:ℝ) ≤ H := by exact_mod_cast h1
    have hi : Y < (H:ℝ)+1 := Nat.lt_floor_add_one _
    linarith
  have original := step H h1 (hy.trans ym)
  have shifted : M^(1/2:ℝ)*((H:ℝ)*X)^(1/6:ℝ)+M/X ≤ 2*U := by
    have pow_le : M^(1/2:ℝ)*((H:ℝ)*X)^(1/6:ℝ) ≤ U := by
      rw [← power_eq]
      gcongr
    have inv_le : M/X ≤ U := (div_le_iff₀ hx).mpr (by
      rw [← product]; simpa [mul_comm] using mul_le_mul_of_nonneg_right yx up.le)
    linarith
  have mass : M ≤ 2*(H:ℝ)*U := by
    rw [← product]
    exact mul_le_mul_of_nonneg_right floor_lower up.le
  have right : (N:ℝ)+H*K*(M^(1/2:ℝ)*((H:ℝ)*X)^(1/6:ℝ)+M/X) ≤
      8*(H:ℝ)*K*U := by
    have main := mul_le_mul_of_nonneg_left shifted (mul_nonneg Hp.le kp.le)
    have huK := mul_le_mul_of_nonneg_right hk (mul_nonneg Hp.le up.le)
    nlinarith only [main,mass,hn,huK]
  have ready : (H:ℝ)*S^2 ≤ (H:ℝ)*(32*K*(M*U)) := by
    apply original.trans
    calc _ ≤ (4*M)*(8*(H:ℝ)*K*U) := by
           apply mul_le_mul (by linarith [hy.trans ym]) right (by positivity) (by positivity)
         _ = _ := by ring
  have sqbound := (mul_le_mul_iff_right₀ Hp).mp ready
  apply extend
  apply le_of_sq_le_sq _ (by positivity)
  apply sqbound.trans
  rw [← Tsq]
  calc 32*K*T^2 ≤ 64*K^2*T^2 := by
         apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
         nlinarith [mul_nonneg kp.le (sub_nonneg.mpr hk)]
       _ = _ := by ring

/-- Second A-step in finite-sum form. Both preceding-pair hypotheses are
ordinary exponential sums on the exact (possibly empty) overlap. -/
theorem second_A_of_differences (p : ℕ → ℝ) {N : ℕ} {M X K : ℝ}
    (hm : 1 ≤ M) (hx : 0 < X) (hk : 1 ≤ K) (hn : (N:ℝ) ≤ 3*M)
    (previous : ‖∑ j ∈ range N, character (p j)‖ ≤ K*(M^(2/3:ℝ)*X^(1/6:ℝ)+1/X))
    (differences : ∀ d : ℕ, 1 ≤ d → (d:ℝ) ≤ M →
      ‖∑ j ∈ range (N-d), character (p (j+d)-p j)‖ ≤
        K*(M^(1/2:ℝ)*((d:ℝ)*X)^(1/6:ℝ)+M/((d:ℝ)*X))) :
    ‖∑ j ∈ range N, character (p j)‖ ≤ 8*K*(M^(11/14:ℝ)*X^(1/14:ℝ)+1/X) := by
  have mp : 0 < M := by linarith
  have kp : 0 < K := by linarith
  have tr : ‖∑ j ∈ range N, character (p j)‖ ≤ (N:ℝ) := by
    apply (norm_sum_le _ _).trans
    have unit (j : ℕ) : ‖character (p j)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    simp only [unit,sum_const,card_range,nsmul_eq_mul,mul_one,le_refl]
  apply optimize_second_A hm hx hk hn tr previous
  intro H hH HM
  let E := K*(M^(1/2:ℝ)*((H:ℝ)*X)^(1/6:ℝ)+M/X)
  have epos : 0 ≤ E := by dsimp [E]; positivity
  have hHR : (1:ℝ) ≤ H := by exact_mod_cast hH
  have each (d : ℕ) (hd : 0 < d) (dh : d < H) :
      ‖∑ j ∈ range (N-d), character (p (j+d)-p j)‖ ≤ E := by
    have dh' : (d:ℝ) ≤ H := by exact_mod_cast dh.le
    have dlo : (1:ℝ) ≤ d := by exact_mod_cast hd
    apply (differences d hd (dh'.trans HM)).trans
    dsimp [E]
    apply mul_le_mul_of_nonneg_left _ kp.le
    apply add_le_add
    · gcongr
    · apply div_le_div_of_nonneg_left mp.le hx
      simpa using mul_le_mul_of_nonneg_right dlo hx.le
  have b := uniform_differencing p N H hH E each
  have pref : ((N+H-1:ℕ):ℝ) ≤ (N:ℝ)+H := by exact_mod_cast Nat.sub_le (N+H) 1
  have hm0 : 0 ≤ (H:ℝ)-1 := sub_nonneg.mpr hHR
  apply b.trans
  calc _ ≤ ((N:ℝ)+H)*(N+H*E) := by
         apply mul_le_mul pref (by gcongr; linarith) (by positivity) (by positivity)
       _ = _ := by dsimp [E]; ring

end FactorialDifferencing
#print axioms FactorialDifferencing.optimize_second_A
#print axioms FactorialDifferencing.second_A_of_differences

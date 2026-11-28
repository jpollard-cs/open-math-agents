import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Explicit comparison of the upper sieve-band errors with
three power savings, including the dyadic count and the rounded sieve level. -/
noncomputable section
open Real
namespace ReciprocalBandEnvelope

local notation "c" => (4/9:ℝ)
local notation "γ" => (1/12-1/1000000:ℝ)

/-- The floor in the sieve level is nonzero and its square stays within the band. -/
theorem sieve_level_le (n : ℕ) (hn : 2≤n) (a : ℝ) (ha : (1:ℝ)/2 ≤ a) :
    1 ≤ ⌊(n:ℝ)^γ⌋₊ ∧ ((⌊(n:ℝ)^γ⌋₊ : ℕ):ℝ)^2 ≤ (n:ℝ)^a := by
  have n1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1≤n by omega)
  have n0 : (0:ℝ) ≤ n := by positivity
  have q1 : 1 ≤ (n:ℝ)^γ := Real.one_le_rpow n1 (by norm_num)
  constructor
  · exact Nat.floor_pos.mpr q1
  · calc _ ≤ ((n:ℝ)^γ)^2 := pow_le_pow_left₀ (by positivity) (Nat.floor_le (by positivity)) _
         _ = (n:ℝ)^(2*γ) := by rw [← Real.rpow_mul_natCast n0]; norm_num
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le n1 (by linarith)

/-- A uniform envelope for all three errors over the high-prime range. -/
theorem band_envelope (n : ℕ) (hn : 2≤n) (a b : ℝ) (ha : (1:ℝ)/2 ≤ a)
    (hab : a≤b) (hb : b ≤ 50009/90000) :
    let X : ℝ := n
    let h : ℝ := ⌊X^c⌋₊
    let z : ℝ := ⌊X^γ⌋₊
    let u := X^a
    let v := X^b
    4*h*z^2/u + (1+log (v/u)/log 2)*(3150*(X+h)^(1/3:ℝ)*z^(4/3:ℝ))
      + (10720/3)*v^2/X*(1+log z)^3 ≤
    50000*((1+log X)^4*(X^(c+2*γ-a)+X^(1/3+4*γ/3)+X^(2*b-1))) := by
  let X : ℝ := n
  let h : ℝ := ⌊X^c⌋₊
  let z : ℝ := ⌊X^γ⌋₊
  let u := X^a
  let v := X^b
  let S := 1+log X
  let A := X^(c+2*γ-a)
  let B := X^(1/3+4*γ/3)
  let C := X^(2*b-1)
  change 4*h*z^2/u + (1+log (v/u)/log 2)*(3150*(X+h)^(1/3:ℝ)*z^(4/3:ℝ))
      + (10720/3)*v^2/X*(1+log z)^3 ≤ 50000*(S^4*(A+B+C))
  have n1 : 1≤X := by dsimp [X]; exact_mod_cast (show 1≤n by omega)
  have xp : 0<X := zero_lt_one.trans_le n1
  have up : 0<u := Real.rpow_pos_of_pos xp _
  have vp : 0<v := Real.rpow_pos_of_pos xp _
  have logp := Real.log_nonneg n1
  have s1 : 1≤S := by dsimp [S]; linarith
  have s0 : 0≤S := zero_le_one.trans s1
  have z1 : 1≤z := by dsimp [z,X]; exact_mod_cast (sieve_level_le n hn a ha).1
  have zp : 0<z := zero_lt_one.trans_le z1
  have hc : h ≤ X^c := Nat.floor_le (by positivity)
  have hγ : z ≤ X^γ := Nat.floor_le (by positivity)
  have h0 : 0≤h := Nat.cast_nonneg _
  have hX : h≤X := hc.trans (by simpa using Real.rpow_le_rpow_of_exponent_le n1 (by norm_num : c ≤ 1))
  have zX : z≤X := hγ.trans (by simpa using Real.rpow_le_rpow_of_exponent_le n1 (by norm_num : γ ≤ 1))
  have ap : 0≤A := Real.rpow_nonneg xp.le _
  have bp : 0≤B := Real.rpow_nonneg xp.le _
  have cp : 0≤C := Real.rpow_nonneg xp.le _
  have first : 4*h*z^2/u ≤ 4*A := by
    calc _ ≤ 4*X^c*(X^γ)^2/u := by gcongr
         _ = _ := by
           dsimp [A,u]
           rw [← Real.rpow_mul_natCast xp.le, Real.rpow_sub xp,Real.rpow_add xp]
           ring_nf
  have unitlog : 1/2 ≤ log (2:ℝ) := by
    have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : 0<(2:ℝ))
    norm_num at hl ⊢
    exact hl
  have log2p : 0 < log (2:ℝ) := by linarith
  have count : 1+log (v/u)/log 2 ≤ 2*S := by
    have l : log (v/u) = (b-a)*log X := by
      dsimp [u,v]; rw [Real.log_div vp.ne' up.ne',Real.log_rpow xp,Real.log_rpow xp]; ring
    have uv : b-a ≤ 1 := by linarith
    have d : log (v/u)/log 2 ≤ 2*log X := by
      apply (div_le_iff₀ log2p).mpr
      rw [l]
      nlinarith [mul_le_mul_of_nonneg_right uv logp,
        mul_le_mul_of_nonneg_left unitlog logp]
    dsimp [S]
    linarith
  have root : (X+h)^(1/3:ℝ) ≤ 2*(X^(1/3:ℝ)) := by
    calc _ ≤ (2*X)^(1/3:ℝ) := Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
         _ = (2:ℝ)^(1/3:ℝ)*X^(1/3:ℝ) := Real.mul_rpow (by norm_num) xp.le
         _ ≤ _ := mul_le_mul_of_nonneg_right (by
           simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
             (by norm_num : (1/3:ℝ)≤1)) (by positivity)
  have zpow := Real.rpow_le_rpow zp.le hγ (by norm_num : 0≤(4/3:ℝ))
  have power : 3150*(X+h)^(1/3:ℝ)*z^(4/3:ℝ) ≤ 6300*B := by
    calc _ ≤ 3150*(2*X^(1/3:ℝ))*(X^γ)^(4/3:ℝ) := by gcongr
         _ = _ := by
           dsimp [B]; rw [← Real.rpow_mul xp.le,Real.rpow_add xp]
           ring_nf
  have middle : (1+log (v/u)/log 2)*(3150*(X+h)^(1/3:ℝ)*z^(4/3:ℝ)) ≤
      12600*S*B := by
    calc _ ≤ (2*S)*(6300*B) := mul_le_mul count power (by positivity) (by positivity)
         _ = _ := by ring
  have scale : v^2/X = C := by
    dsimp [C,v]
    rw [Real.rpow_sub xp,Real.rpow_one,← Real.rpow_mul_natCast xp.le]
    congr 2; ring
  have ceilLog : (1+log z)^3 ≤ S^3 := by
    apply pow_le_pow_left₀ (by linarith [Real.log_nonneg z1]) _ 3
    exact add_le_add le_rfl (Real.log_le_log zp zX)
  have last : (10720/3)*v^2/X*(1+log z)^3 ≤ (10720/3)*S^3*C := by
    rw [mul_div_assoc,scale]
    calc _ ≤ (10720/3)*C*S^3 := mul_le_mul_of_nonneg_left ceilLog (by positivity)
         _ = _ := by ring
  have L1 : 1≤S^4 := one_le_pow₀ s1
  have L2 : S≤S^4 := by simpa using pow_le_pow_right₀ s1 (by decide : 1≤4)
  have L3 : S^3≤S^4 := pow_le_pow_right₀ s1 (by decide)
  have f := mul_le_mul_of_nonneg_right L1 ap
  have m := mul_le_mul_of_nonneg_right L2 bp
  have e := mul_le_mul_of_nonneg_right L3 cp
  nlinarith [mul_nonneg (by positivity : 0≤S^4) ap,
    mul_nonneg (by positivity : 0≤S^4) bp,mul_nonneg (by positivity : 0≤S^4) cp]

#print axioms sieve_level_le
#print axioms band_envelope
end ReciprocalBandEnvelope

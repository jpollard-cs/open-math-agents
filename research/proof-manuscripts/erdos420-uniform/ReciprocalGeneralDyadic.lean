import ReciprocalDyadic
import ReciprocalLowerBandInput

/-! Pass from scale-dependent single-modulus estimates to a prime-count bound
on an arbitrary band. The constant is independent of the scale and the endpoints. -/
noncomputable section
open Finset Real
namespace FactorialDyadic

/-- A reciprocal sawtooth estimate on every factor-two interval and single modulus. -/
def UniformSaw (p q s : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x t : ℕ, 0 < x → 0 < t → ∀ u v : ℝ,
    (t:ℝ) ≤ u → u ≤ v → v ≤ 2*u → |FactorialSieve.remainder u v x t| ≤ 
      C*((x:ℝ)^p*u^q*(t:ℝ)^(-s)+u^2/((x:ℝ)*t))

/-- A single constant controls both dyadic error terms throughout the band. -/
theorem prime_band_from_saw (p q s : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hs : 0 ≤ s) (hs1 : s < 1)
    (local_est : UniformSaw p q s) : FactorialLowerBands.BandBound p q s := by
  obtain ⟨C,hC,local_est⟩ := local_est
  let M := (1+1/(1-s))/(1-s)^2
  have ds : 0 < 1-s := sub_pos.mpr hs1
  have m0 : 0 ≤ M := by dsimp [M]; positivity
  let K := max 1 (max (2*C*M) ((8/3)*C))
  refine ⟨K,le_max_left ..,?_⟩
  intro n h z u v hn hz zu uv
  have nz : 0 < (n:ℝ) := by exact_mod_cast hn
  have zz : 0 < (z:ℝ) := by exact_mod_cast hz
  have up : 0 < u := (sq_pos_of_pos zz).trans_le zu
  have vp := up.trans_le uv
  let X : ℝ := (n:ℝ)+h
  let A := C*X^p*v^q
  let B := C/(n:ℝ)
  have xp : 0 < X := by dsimp [X]; positivity
  have ap : 0 ≤ A := by dsimp [A]; positivity
  have bp : 0 ≤ B := by dsimp [B]; positivity
  have est (a b : ℝ) (ha : u ≤ a) (ab : a ≤ b) (bv : b ≤ v) (short : b ≤ 2*a) :
      ∀ x ∈ ({n,n+h} : Finset ℕ), ∀ t : ℕ, 1 ≤ t → t ≤ z^2 →
      |FactorialSieve.remainder a b x t| ≤ A*(t:ℝ)^(-s)+B*a^2/t := by
    intro x xmem t ht tz
    have nx : n ≤ x ∧ x ≤ n+h := by
      simp only [mem_insert,mem_singleton] at xmem
      rcases xmem with e|e <;> subst x <;> omega
    have tp : 0 < (t:ℝ) := by exact_mod_cast ht
    have l := local_est x t (hn.trans_le nx.1) ht a b
      ((by exact_mod_cast tz : (t:ℝ) ≤ (z:ℝ)^2).trans (zu.trans ha)) ab short
    apply l.trans
    have boundx : (x:ℝ) ≤ X := by dsimp [X]; exact_mod_cast nx.2
    have y := Real.rpow_le_rpow (Nat.cast_nonneg x) boundx hp
    have w := Real.rpow_le_rpow (up.le.trans ha) (ab.trans bv) hq
    have aa := mul_le_mul y w (Real.rpow_nonneg (up.le.trans ha) q) (Real.rpow_nonneg xp.le p)
    have xx : (n:ℝ) ≤ x := by exact_mod_cast nx.1
    have dd := div_le_div_of_nonneg_left (sq_nonneg a) (mul_pos nz tp)
      (mul_le_mul_of_nonneg_right xx tp.le)
    calc
      _ ≤ C*(X^p*v^q*(t:ℝ)^(-s)+a^2/((n:ℝ)*t)) := by
        exact mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_right aa (Real.rpow_nonneg tp.le _)) dd) hC.le
      _ = _ := by dsimp only [A,B]; ring
  have raw := prime_band_from_local n h z hz zu uv ap bp hs hs1 est
  apply raw.trans
  have K₁ : 2*C*M ≤ K := (le_max_left ..).trans (le_max_right ..)
  have K₂ : (8/3)*C ≤ K := (le_max_right ..).trans (le_max_right ..)
  let J := 1+log (v/u)/log 2
  have j0 : 0 ≤ J := by
    have one : 1 ≤ v/u := (one_le_div up).mpr uv
    have lg := log_nonneg one
    let two := log_pos (show (1:ℝ) < 2 by norm_num)
    dsimp [J]
    exact add_nonneg zero_le_one (div_nonneg lg two.le)
  have lz := Real.log_natCast_nonneg z
  have mid : J*(2*A*(M*(z:ℝ)^(2*(1-s)))) ≤ K*J*X^p*v^q*(z:ℝ)^(2*(1-s)) := by
    calc _ = (2*C*M)*(J*X^p*v^q*(z:ℝ)^(2*(1-s))) := by dsimp only [A]; ring
         _ ≤ K*(J*X^p*v^q*(z:ℝ)^(2*(1-s))) := mul_le_mul_of_nonneg_right K₁ (by positivity)
         _ = _ := by ring
  have last : (8/3)*B*(1+log z)^3*v^2 ≤ K*(v^2/(n:ℝ))*(1+log z)^3 := by
    calc _ = ((8/3)*C)*((v^2/(n:ℝ))*(1+log z)^3) := by dsimp only [B]; ring
         _ ≤ K*((v^2/(n:ℝ))*(1+log z)^3) := mul_le_mul_of_nonneg_right K₂ (by positivity)
         _ = _ := by ring
  exact add_le_add (add_le_add le_rfl mid) last

#print axioms prime_band_from_saw
end FactorialDyadic

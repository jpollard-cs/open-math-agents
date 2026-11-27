import FactorialSelbergBlock

/-! A clipped dyadic cover for the prime blocks in the four-ninths sieve.
The logarithmic main term telescopes exactly, the reciprocal rounding error
sums from the lower endpoint, and the quadratic error sums from the upper
endpoint. The summand may have either sign. -/

noncomputable section
open Finset Real
namespace FactorialDyadic

/-- An interval sum with the same open-left, closed-right convention as the sieve. -/
def intervalSum (f : ℕ → ℝ) (u v : ℝ) : ℝ := ∑ m ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, f m

private theorem interval_add (f : ℕ → ℝ) {u b v : ℝ} (hub : u ≤ b) (hbv : b ≤ v) :
    intervalSum f u b + intervalSum f b v = intervalSum f u v :=
  sum_Ioc_consecutive f (Nat.floor_mono hub) (Nat.floor_mono hbv)

private theorem covering (f : ℕ → ℝ) (D E F G : ℝ)
    (hE : 0 ≤ E) (hF : 0 ≤ F) (hG : 0 ≤ G) (K : ℕ) {u v : ℝ}
    (hu : 0 < u) (huv : u ≤ v) (cap : v ≤ u*2^K)
    (block : ∀ a b, u ≤ a → a ≤ b → b ≤ v → b ≤ 2*a →
      intervalSum f a b ≤ D*log (b/a) + E/a + F + G*a^2) :
    intervalSum f u v ≤ D*log (v/u) + E*(2/u-1/v) +
      (K:ℝ)*F + G*((4*v^2-u^2)/3) := by
  have hv := hu.trans_le huv
  induction K generalizing u with
  | zero =>
    have eq : v=u := le_antisymm (by simpa using cap) huv
    subst v
    simp only [intervalSum,Ioc_self,sum_empty,div_self hu.ne',Real.log_one,mul_zero,
      zero_add,Nat.cast_zero,zero_mul,add_zero]
    have h₁ : 0 ≤ E*(2/u-1/u) := by
      apply mul_nonneg hE; rw [← sub_div]; positivity
    have h₂ : 0 ≤ G*((4*u^2-u^2)/3) := by
      apply mul_nonneg hG; nlinarith [sq_nonneg u]
    linarith
  | succ K ih =>
    have up : u ≤ 2*u := by linarith
    by_cases small : v ≤ 2*u
    · apply (block u v le_rfl huv le_rfl small).trans
      have e : 1/v ≤ 1/u := one_div_le_one_div_of_le hu huv
      have e' : E/u ≤ E*(2/u-1/v) := by
        rw [div_eq_mul_one_div]; apply mul_le_mul_of_nonneg_left _ hE
        linarith [show 2/u = 2*(1/u) by ring]
      have g' : G*u^2 ≤ G*((4*v^2-u^2)/3) := by
        apply mul_le_mul_of_nonneg_left _ hG
        nlinarith [sq_le_sq' (by linarith : -v ≤ u) huv]
      rw [Nat.cast_succ]
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) K) hF]
    · have split_le : 2*u ≤ v := le_of_not_ge small
      have pos : 0 < 2*u := by positivity
      have upper : v ≤ (2*u)*2^K := by rw [pow_succ] at cap; linarith only [cap,show u*(2^K*2)=(2*u)*2^K by ring]
      have first := block u (2*u) le_rfl up split_le le_rfl
      have rest := ih pos split_le upper
        (fun a b ha hab hb hba => block a b (up.trans ha) hab hb hba)
      rw [← interval_add f up split_le]
      apply (add_le_add first rest).trans
      apply le_of_eq
      rw [Real.log_div hv.ne' hu.ne', Real.log_div pos.ne' hu.ne', Real.log_div hv.ne' pos.ne',
        Nat.cast_succ]
      field_simp
      ring

/-- The exact logarithmic main term survives clipping the last block.
The number of blocks is at most 1+log(v/u)/log 2. The endpoint errors
have bounds 2E/u and (4/3)G v² regardless of the number of blocks. -/
theorem clipped_dyadic_sum (f : ℕ → ℝ) {u v D E F G : ℝ}
    (hu : 0 < u) (huv : u ≤ v) (hE : 0 ≤ E) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (block : ∀ a b, u ≤ a → a ≤ b → b ≤ v → b ≤ 2*a →
      intervalSum f a b ≤ D*log (b/a) + E/a + F + G*a^2) :
    intervalSum f u v ≤ D*log (v/u) + 2*E/u +
      (1+log (v/u)/log 2)*F + (4/3)*G*v^2 := by
  let q := log (v/u)/log 2
  let K := ⌊q⌋₊+1
  have hv := hu.trans_le huv
  have pos2 : 0 < log (2:ℝ) := Real.log_pos (by norm_num)
  have hq : 0 ≤ q := div_nonneg (log_nonneg ((le_div_iff₀ hu).mpr (by simpa using huv))) pos2.le
  have k_low : q ≤ (K:ℝ) := by
    dsimp [K]; push_cast; exact (Nat.lt_floor_add_one q).le
  have k_high : (K:ℝ) ≤ 1+q := by
    dsimp [K]; push_cast; linarith [Nat.floor_le hq]
  have cap : v ≤ u*2^K := by
    apply (Real.log_le_log_iff hv (by positivity)).mp
    rw [log_mul hu.ne' (by positivity),log_pow]
    have e := (div_le_iff₀ pos2).mp k_low
    rw [log_div hv.ne' hu.ne'] at e
    linarith
  apply (covering f D E F G hE hF hG K hu huv cap block).trans
  have low : E*(2/u-1/v) ≤ 2*E/u := by
    calc _ ≤ E*(2/u) := mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) hE
         _ = _ := by ring
  have high : G*((4*v^2-u^2)/3) ≤ (4/3)*G*v^2 := by
    nlinarith [mul_nonneg hG (sq_nonneg u)]
  have mid := mul_le_mul_of_nonneg_right k_high hF
  dsimp [q] at mid
  linarith

/-- Transfer the single-modulus bounds on clipped dyadic blocks directly to
a prime count over the whole band. Constants A and B are uniform over the
two endpoints and all subblocks. -/
theorem prime_band_from_local (n h z : ℕ) {u v A B s : ℝ}
    (hz : 1 ≤ z) (hzu : (z:ℝ)^2 ≤ u) (huv : u ≤ v)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (local_est : ∀ a b, u ≤ a → a ≤ b → b ≤ v → b ≤ 2*a →
      ∀ x ∈ ({n,n+h} : Finset ℕ), ∀ t : ℕ, 1 ≤ t → t ≤ z^2 →
        |FactorialSieve.remainder a b x t| ≤ A*(t:ℝ)^(-s) + B*a^2/t) :
    (∑ p ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime, (FactorialSieve.multiplicity n h p:ℝ)) ≤
      (h:ℝ)*log (v/u)/log ((z:ℝ)+1) + 4*h*(z:ℝ)^2/u +
      (1+log (v/u)/log 2)*
        (2*A*(((1+1/(1-s))/(1-s)^2)*(z:ℝ)^(2*(1-s)))) +
      (8/3)*B*(1+log z)^3*v^2 := by
  let f (p : ℕ) : ℝ := if p.Prime then FactorialSieve.multiplicity n h p else 0
  let M := (((1+1/(1-s))/(1-s)^2)*(z:ℝ)^(2*(1-s)))
  have hpow : 0 < 1-s := sub_pos.mpr hs1
  have mpos : 0 ≤ M := by dsimp [M]; positivity
  have zpos : 0 < (z:ℝ) := by exact_mod_cast (show 0<z by omega)
  have hu : 0 < u := (sq_pos_of_pos zpos).trans_le hzu
  have lg := Real.log_natCast_nonneg z
  have local_block (a b : ℝ) (ha : u ≤ a) (hab : a ≤ b) (hb : b ≤ v) (tw : b ≤ 2*a) :
      intervalSum f a b ≤ ((h:ℝ)/log ((z:ℝ)+1))*log (b/a) +
        (2*h*(z:ℝ)^2)/a + (2*A*M) + (2*B*(1+log z)^3)*a^2 := by
    have raw := FactorialSieve.short_interval_from_local n h z a b A (B*a^2) s hz
      (hzu.trans ha) hab hA (mul_nonneg hB (sq_nonneg _)) hs0 hs1 (local_est a b ha hab hb tw)
    dsimp only [intervalSum,f]
    rw [← sum_filter]
    apply raw.trans
    apply le_of_eq
    dsimp only [M]
    ring
  have total := clipped_dyadic_sum f hu huv (by positivity : 0 ≤ 2*h*(z:ℝ)^2)
    (by positivity : 0 ≤ 2*A*M) (by positivity : 0 ≤ 2*B*(1+log z)^3) local_block
  dsimp only [intervalSum,f] at total
  rw [← sum_filter] at total
  apply total.trans
  apply le_of_eq
  dsimp only [M]
  ring

/-- Fixed constants for the square-root exponent pair over any whole prime
band. The input is the unconditional single-block theorem with its original
upper limit b ≤ 3a. The cover only needs b ≤ 2a. -/
theorem prime_band_sqrt_of_block (n h z : ℕ) (u v : ℝ) (hn : 0 < n)
    (hz : 1 ≤ z) (zu : (z:ℝ)^2 ≤ u) (huv : u ≤ v)
    (single : ∀ a b : ℝ, (z:ℝ)^2 ≤ a → a ≤ b → b ≤ 3*a →
      (∑ p ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (FactorialSieve.multiplicity n h p:ℝ)) ≤
      (h:ℝ)*log (b/a)/log ((z:ℝ)+1) + 2*h*(z:ℝ)^2/a +
      3150*((n:ℝ)+h)^(1/3:ℝ)*(z:ℝ)^(4/3:ℝ) + 2680*a^2/(n:ℝ)*(1+log z)^3) :
    (∑ p ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime, (FactorialSieve.multiplicity n h p:ℝ)) ≤
      (h:ℝ)*log (v/u)/log ((z:ℝ)+1) + 4*h*(z:ℝ)^2/u +
      (1+log (v/u)/log 2)*(3150*((n:ℝ)+h)^(1/3:ℝ)*(z:ℝ)^(4/3:ℝ)) +
      (10720/3)*v^2/(n:ℝ)*(1+log z)^3 := by
  let f (p : ℕ) : ℝ := if p.Prime then FactorialSieve.multiplicity n h p else 0
  let F := 3150*((n:ℝ)+h)^(1/3:ℝ)*(z:ℝ)^(4/3:ℝ)
  let G := 2680/(n:ℝ)*(1+log z)^3
  have zpos : (0:ℝ) < z := by exact_mod_cast (show 0<z by omega)
  have hu := (sq_pos_of_pos zpos).trans_le zu
  have npos : (0:ℝ) < n := by exact_mod_cast hn
  have lg := Real.log_natCast_nonneg z
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have block (a b : ℝ) (ha : u ≤ a) (hab : a ≤ b) (_hb : b ≤ v) (tw : b ≤ 2*a) :
      intervalSum f a b ≤ ((h:ℝ)/log ((z:ℝ)+1))*log (b/a) +
        (2*h*(z:ℝ)^2)/a + F + G*a^2 := by
    dsimp only [intervalSum,f]
    rw [← sum_filter]
    apply (single a b (zu.trans ha) hab (by linarith)).trans_eq
    dsimp only [F,G]
    ring
  have total := clipped_dyadic_sum f hu huv (by positivity : 0 ≤ 2*h*(z:ℝ)^2) hF hG block
  dsimp only [intervalSum,f] at total
  rw [← sum_filter] at total
  apply total.trans_eq
  dsimp only [F,G]
  ring

end FactorialDyadic
#print axioms FactorialDyadic.clipped_dyadic_sum
#print axioms FactorialDyadic.prime_band_from_local
#print axioms FactorialDyadic.prime_band_sqrt_of_block

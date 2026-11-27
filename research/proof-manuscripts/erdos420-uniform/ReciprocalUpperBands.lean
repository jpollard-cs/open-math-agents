import ReciprocalPrimeBlock
import ReciprocalHitCount
import ReciprocalDyadic
import ReciprocalBandRates
import ReciprocalBandEnvelope
import PrimeBlockMesh

/-! The upper seventeen of the 48 prime-hit bounds in the four-ninths
factorial-window reduction. These are the bands assigned exponent pair
(1/2,1/2) by Erdős, Graham, Ivić and Pomerance, Lemma 3, together
with the preceding band whose right-endpoint allowance is also twelve. -/
noncomputable section
open Finset Real Filter
open scoped Classical
namespace FactorialUpperBands
open ReciprocalBandRates FactorialFourier PrimeBlockMesh

def primeHits (n h : ℕ) (u v : ℝ) : ℝ :=
  ∑ p ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime, (FactorialSieve.multiplicity n h p:ℝ)

/-- Any fixed band in the upper range with width at most 1/250 satisfies
the required asymptotic hit-count estimate with coefficient twelve. -/
theorem prime_hits_eventually (a b : ℝ) (ha : 1/2 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 50009/90000) (hw : b-a ≤ 1/250) :
    ∀ᶠ n : ℕ in atTop,
      primeHits n ⌊(n:ℝ)^c⌋₊ ((n:ℝ)^a) ((n:ℝ)^b) ≤ ((b-a)*12+1/1000000)*window n := by
  apply band_from_errors_wide _ a b 50000 ha hb hw (by norm_num)
  filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
  let z := ⌊(n:ℝ)^gamma⌋₊
  let h := ⌊(n:ℝ)^c⌋₊
  let u := (n:ℝ)^a
  let v := (n:ℝ)^b
  have level := ReciprocalBandEnvelope.sieve_level_le n hn a ha
  have huv : u ≤ v := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤n by omega)) hab
  have pos : 0<n := by omega
  have block := FactorialDyadic.prime_band_sqrt_of_block n h z u v pos level.1 level.2 huv
    (fun r s => prime_block_sqrt n h z r s pos level.1)
  have env := ReciprocalBandEnvelope.band_envelope n hn a b ha hab hb
  have mainB := mul_le_mul_of_nonneg_left (floor_sieve_main n hn a b hab) (Nat.cast_nonneg h)
  change (h:ℝ)*(log (v/u)/log ((z:ℝ)+1)) ≤ h*((b-a)/gamma) at mainB
  change primeHits n h u v ≤ _
  change primeHits n h u v ≤ _ at block
  change 4*h*(z:ℝ)^2/u +
    (1+log (v/u)/log 2)*(3150*((n:ℝ)+h)^(1/3:ℝ)*(z:ℝ)^(4/3:ℝ)) +
    (10720/3)*v^2/(n:ℝ)*(1+log z)^3 ≤ 50000*errors n a b at env
  change primeHits n h u v ≤ ((b-a)/gamma)*h+50000*errors n a b
  rw [← mul_div_assoc] at mainB
  rw [mul_comm (h:ℝ) ((b-a)/gamma)] at mainB
  linarith only [block,mainB,env]

def bandSet (n j : ℕ) : Finset ((_:ℕ) × ℕ) :=
  let h := ⌊(n:ℝ)^(4/9:ℝ)⌋₊
  let S := (range h).sigma (fun i => (n+i+1).primeFactors.filter (fun p : ℕ =>
    (n:ℝ)^(4/9:ℝ) < p ∧ (p:ℝ) ≤ (n:ℝ)^(5/9+1/10000:ℝ)))
  S.filter (fun z => (n:ℝ)^(edge j:ℝ) < (z.2:ℝ) ∧ (z.2:ℝ) ≤ (n:ℝ)^(edge (j+1):ℝ))

private theorem upper_params : ∀ j ∈ Ico 31 48,
    (1/2:ℝ) ≤ (edge j:ℝ) ∧ (edge j:ℝ) ≤ (edge (j+1):ℝ) ∧ (edge (j+1):ℝ) ≤ 50009/90000 ∧
      (edge (j+1):ℝ)-(edge j:ℝ) ≤ 1/250 ∧
      (allowance j:ℝ) = ((edge (j+1):ℝ)-(edge j:ℝ))*12+1/1000000 := by
  intro j hj
  obtain ⟨l,r⟩ := mem_Ico.mp hj
  interval_cases j <;> norm_num [edge,allowance]

/-- The same finite set of pairs and rational allowances as in H1 of the
48-band reduction, for every j from 31 through 47 simultaneously. -/
theorem upper_seventeen :
    ∀ᶠ n : ℕ in atTop, ∀ j ∈ Ico 31 48,
      ((bandSet n j).card:ℝ) ≤ (allowance j:ℝ)*⌊(n:ℝ)^(4/9:ℝ)⌋₊ := by
  apply (eventually_all_finset _).mpr
  intro j hj
  obtain ⟨ha,hab,hb,hw,teq⟩ := upper_params j hj
  let a : ℝ := edge j
  let b : ℝ := edge (j+1)
  have B := prime_hits_eventually a b ha hab hb hw
  filter_upwards [B] with n count
  have bridge := hit_card_le n ⌊(n:ℝ)^(4/9:ℝ)⌋₊ ((n:ℝ)^a) ((n:ℝ)^b)
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) (bandSet n j) (by
      intro z hz
      obtain ⟨hs,hband⟩ := mem_filter.mp hz
      obtain ⟨hi,hp⟩ := mem_sigma.mp hs
      have prime := (mem_filter.mp hp).1
      exact ⟨mem_range.mp hi,Nat.prime_of_mem_primeFactors prime,
        Nat.dvd_of_mem_primeFactors prime,hband⟩)
  apply bridge.trans
  have eqA : (allowance j:ℝ) = (b-a)*12+1/1000000 := teq
  rw [eqA]
  exact count

end FactorialUpperBands
#print axioms FactorialUpperBands.prime_hits_eventually
#print axioms FactorialUpperBands.upper_seventeen

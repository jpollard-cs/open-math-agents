import PrimeGapTranslatedCover
import LcmSeed
import FactorialGain

/-! The simultaneous-residue theorem and the explicit prime-power budget
give an actual upper bound on the factorial divisor ratio in a translated window. -/

namespace CertifiedFactorialWindow

open LongGapsBetweenPrimes SeedAverage TranslatedDivisorCover Real

/-- The only seed hypothesis is the numerical count of positive multiples
of the obstructing prime powers. The translation parameter j is arbitrary
subject to the displayed lower bound on the start. -/
theorem eventually_window_of_budget : ∀ᶠ x : ℝ in Filter.atTop,
    ∀ N w h r U j : ℕ, 0 < w → N ≤ sieveZ x → h ≤ sieveZ x →
      2*w ≤ sieveZ x → 2*w+h < U → sieveY x < U →
      U*U ≤ Nat.lcmUpto N*j → (r:ℝ) ≤ sieveDelta*x →
      h*((primePowerObstructions N (2*w+h+1)).map (fun q => (2*w+h+1)/q)).sum ≤ (w+1)*r →
      ∃ A, w ≤ A ∧ A ≤ 2*w ∧ ∃ t < sieveT x,
        let n := A + Nat.lcmUpto N*j + Nat.lcmUpto N*(t+1)
        log ((n+h).factorial.divisors.card : ℝ) - log (n.factorial.divisors.card : ℝ) ≤
          2*(h:ℝ)/w := by
  filter_upwards [eventually_fill_lcm_window] with x cover
  intro N w h r U j hw hN hh hW hU hY hbase hr hbudget
  obtain ⟨A,hlo,hhi,hseed⟩ := exists_lcm_seed_card N w h r hbudget
  obtain ⟨t,ht,hc⟩ := cover N h A U j hN hh (hhi.trans hW) (by omega) hY
    ((by exact_mod_cast hseed : (((Finset.Icc 1 h).filter (fun i => ¬ A+i ∣ Nat.lcmUpto N)).card : ℝ) ≤ r).trans hr)
  refine ⟨A,hlo,hhi,t,ht,FactorialGain.window_log_gain_le _ _ _ hw ?_⟩
  intro i hi hi'
  obtain ⟨d,hAd,hdU,hdvd⟩ := hc i hi hi'
  refine ⟨d,hlo.trans_lt hAd,?_,hdvd⟩
  have hsq : d*d ≤ U*U := Nat.mul_le_mul hdU.le hdU.le
  omega

end CertifiedFactorialWindow

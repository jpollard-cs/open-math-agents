import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Factorization.PrimePow
import SeedAverage

/-! A finite seed for short windows using the prime powers above the LCM cutoff. -/

namespace SeedAverage

/-- Every failure to divide the LCM is witnessed by a prime power above its cutoff. -/
theorem large_prime_power_of_not_dvd {m x : ℕ} (hm : 0 < m) (hbad : ¬ m ∣ Nat.lcmUpto x) :
    ∃ q, x < q ∧ q ≤ m ∧ IsPrimePow q ∧ q ∣ m := by
  by_contra hn
  apply hbad
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p k hp hpk
  by_cases hk : k = 0
  · simp [hk]
  by_cases hx : p^k ≤ x
  · have hp0 : 0 < p := hp.pos
    change p^k ∣ (Finset.Icc 1 x).lcm id
    exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨pow_pos hp0 k, hx⟩)
  · exact False.elim (hn ⟨p^k, by omega, Nat.le_of_dvd hm hpk,
      (isPrimePow_nat_iff _).mpr ⟨p,k,hp,by omega,rfl⟩, hpk⟩)

/-- The exact finite obstruction budget from the seed argument. The list
contains each relevant prime power once. -/
noncomputable def primePowerObstructions (x z : ℕ) : List ℕ := by
  classical
  exact ((Finset.Ioc x z).filter IsPrimePow).toList

theorem exists_lcm_seed (x w h r : ℕ)
    (hbudget : h * ((primePowerObstructions x (2*w+h+1)).map
      (fun q => (2*w+h+1)/q)).sum ≤ (w+1)*r) :
    ∃ A, w ≤ A ∧ A ≤ 2*w ∧
      intervalSum (fun m => if m ∣ Nat.lcmUpto x then 0 else 1) (A+1) h ≤ r := by
  classical
  refine exists_seed_of_obstructions _ _ _ _ _ ?_ hbudget
  intro m hm hmZ hbad
  obtain ⟨q,hxq,hqm,hq,hd⟩ := large_prime_power_of_not_dvd hm hbad
  refine ⟨q, ?_, hd⟩
  simpa [primePowerObstructions] using And.intro (And.intro hxq (hqm.trans hmZ)) hq

/-- The interval sum counts precisely the exceptional offsets used in the sieve. -/
theorem window_sum_eq_card (A h M : ℕ) :
    intervalSum (fun m => if m ∣ M then 0 else 1) (A+1) h =
      ((Finset.Icc 1 h).filter (fun i => ¬ A+i ∣ M)).card := by
  classical
  induction h with
  | zero => simp [intervalSum]
  | succ h ih =>
    have hu : Finset.Icc 1 (h+1) = insert (h+1) (Finset.Icc 1 h) := by
      ext i
      simp
      omega
    have hout : h+1 ∉ (Finset.Icc 1 h).filter (fun i => ¬ A+i ∣ M) := by simp
    by_cases hd : A+(h+1) ∣ M
    · simp [intervalSum, ih, hu, Finset.filter_insert, hd, show A+1+h=A+(h+1) by omega]
    · simp [intervalSum, ih, hu, Finset.filter_insert, hd, hout, show A+1+h=A+(h+1) by omega]

theorem exists_lcm_seed_card (x w h r : ℕ)
    (hbudget : h * ((primePowerObstructions x (2*w+h+1)).map
      (fun q => (2*w+h+1)/q)).sum ≤ (w+1)*r) :
    ∃ A, w ≤ A ∧ A ≤ 2*w ∧
      ((Finset.Icc 1 h).filter (fun i => ¬ A+i ∣ Nat.lcmUpto x)).card ≤ r := by
  obtain ⟨A, hlo, hhi, hcount⟩ := exists_lcm_seed x w h r hbudget
  exact ⟨A,hlo,hhi, (window_sum_eq_card A h _) ▸ hcount⟩

end SeedAverage

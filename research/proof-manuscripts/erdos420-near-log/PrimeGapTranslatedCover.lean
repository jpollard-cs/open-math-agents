/-
Jordan Pollard. Developed and checked with OpenAI Codex, November 2026.
The imported simultaneous-residue and linear-root lemmas are due to OpenAI,
"Improved Long Gaps Between Primes", commit 03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b.
-/
import LongGapsBetweenPrimes
import TranslatedDivisorCover

/-!
# Applying the simultaneous-residue theorem to factorial-window divisors

This adapter imports the original proof of the simultaneous-residue theorem
and the finite divisor-cover lemma. Its hypotheses on the ordinary offsets
are precisely the input supplied by the least-common-multiple construction.
-/

namespace TranslatedDivisorCover

open LongGapsBetweenPrimes

/-- For all sufficiently large sieve parameters, any small set of exceptional
offsets can be filled into a translated family of bounded divisor certificates.
The progression coefficient may be any integer whose prime factors lie below
the lower sieve cutoff. -/
theorem eventually_fill_exceptional_offsets : ∀ᶠ x : ℝ in Filter.atTop,
    ∀ (H b M W U : ℕ) (S : Finset ℕ),
      H ≤ sieveZ x → W ≤ sieveZ x → sieveY x < U →
      (∀ q : ℕ, q.Prime → q ∣ M → q ≤ sieveZ x) →
      S ⊆ Finset.Icc 1 H → (S.card : ℝ) ≤ sieveDelta * x →
      (∀ i, 1 ≤ i → i ≤ H → i ∉ S →
        ∃ d, W < d ∧ d < U ∧ d ∣ b + i ∧ d ∣ M) →
      ∃ t < sieveT x, ∀ i, 1 ≤ i → i ≤ H →
        ∃ d, W < d ∧ d < U ∧ d ∣ b + M * (t + 1) + i := by
  classical
  filter_upwards [eventually_simultaneous_roots, Filter.eventually_ge_atTop (2 : ℝ)]
    with x hroots hx
  intro H b M W U S hHZ hWZ hYU hM hSH hcard hgood
  rcases S.eq_empty_or_nonempty with rfl | hne
  · have hT : 0 < sieveT x := by
      exact_mod_cast (half_pos (Real.exp_pos x)).trans_le (sieveT_lower hx)
    refine ⟨0, hT, ?_⟩
    intro i hi hiH
    obtain ⟨d, hdW, hdU, hdb, hdM⟩ := hgood i hi hiH (by simp)
    refine ⟨d, hdW, hdU, ?_⟩
    have h := Nat.dvd_add hdb hdM
    simpa only [Nat.zero_add, Nat.mul_one, Nat.add_right_comm b i] using h
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne.card_pos.ne'
  let e : Fin (k + 1) ≃ S :=
    (Fintype.equivFinOfCardEq (by simpa using hk : Fintype.card S = k + 1)).symm
  let s : Fin (k + 1) → ℕ := fun i => (e i).val
  have hpr (p : PrimeIndex (sieveP x)) :
      p.val.Prime ∧ sieveZ x < p.val ∧ p.val ≤ sieveY x := by
    obtain ⟨hp, hdvd, _⟩ := Nat.mem_primeFactors.mp p.property
    exact mem_auxiliaryPrimes.mp (prime_dvd_auxiliaryProduct hp hdvd)
  apply of_simultaneous_roots (fun p : PrimeIndex (sieveP x) => p.val) s
  · intro root hinj
    obtain ⟨t, ht, hh⟩ := hroots k (by simpa [hk] using hcard) root
      (fun p _ _ hij => hinj p _ _ hij)
    refine ⟨t, ht, fun i => ?_⟩
    obtain ⟨p, hp⟩ := hh i
    exact ⟨p, congrArg Fin.val hp⟩
  · intro p
    obtain ⟨hp, hZp, _⟩ := hpr p
    have hcop : M.Coprime p.val :=
      (hp.coprime_iff_not_dvd.mpr (fun hdvd => hZp.not_ge (hM _ hp hdvd))).symm
    obtain ⟨r, hr, hd⟩ := exists_linear_roots (b := b) hp hcop s
      (Subtype.val_injective.comp e.injective)
      (fun i => ((Finset.mem_Icc.mp (hSH (e i).property)).2.trans hHZ).trans_lt hZp)
    exact ⟨r, fun _ _ h => hr h, hd⟩
  · intro p
    exact ⟨hWZ.trans_lt (hpr p).2.1, (hpr p).2.2.trans_lt hYU⟩
  · intro i hi hiH hne
    apply hgood i hi hiH
    intro hmem
    obtain ⟨j, hj⟩ := e.surjective ⟨i, hmem⟩
    exact hne j (congrArg Subtype.val hj)

/-- Specialization to the actual least-common-multiple seed. The only
remaining arithmetic input is the cardinality bound for offsets whose
shift fails to divide the least common multiple. The arbitrary `r`
allows the interval to be translated before applying the sieve. -/
theorem eventually_fill_lcm_window : ∀ᶠ x : ℝ in Filter.atTop,
    ∀ N H A U r : ℕ, N ≤ sieveZ x → H ≤ sieveZ x → A ≤ sieveZ x →
      A + H < U → sieveY x < U →
      (((Finset.Icc 1 H).filter (fun i => ¬ A + i ∣ Nat.lcmUpto N)).card : ℝ)
        ≤ sieveDelta * x →
      ∃ t < sieveT x, ∀ i, 1 ≤ i → i ≤ H →
        ∃ d, A < d ∧ d < U ∧
          d ∣ (A + Nat.lcmUpto N * r) + Nat.lcmUpto N * (t + 1) + i := by
  classical
  filter_upwards [eventually_fill_exceptional_offsets] with x hfill
  intro N H A U r hNZ hHZ hAZ hAH hYU hcard
  let S := (Finset.Icc 1 H).filter (fun i => ¬ A + i ∣ Nat.lcmUpto N)
  apply hfill H (A + Nat.lcmUpto N * r) (Nat.lcmUpto N) A U S hHZ hAZ hYU
  · intro q hq hd
    have hm := hq.mem_primeFactors hd (Nat.lcmUpto_ne_zero N)
    rw [Nat.primeFactors_lcmUpto] at hm
    exact (Nat.le_of_mem_primesLE hm).trans hNZ
  · exact Finset.filter_subset _ _
  · exact hcard
  · intro i hi hiH hnot
    have hd : A + i ∣ Nat.lcmUpto N := by
      by_contra h
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hi, hiH⟩, h⟩)
    refine ⟨A + i, by omega, by omega, ?_, hd⟩
    have h := Nat.dvd_add (Nat.dvd_refl (A + i)) (Nat.dvd_mul_right_of_dvd hd r)
    simpa only [Nat.add_right_comm A i] using h

/-- A seeded window sufficiently far out on the progression contains no
prime times a cofactor of size at most `A`, under the same exceptional-set
cardinality bound. -/
theorem eventually_exclude_small_cofactors : ∀ᶠ x : ℝ in Filter.atTop,
    ∀ N H A U r : ℕ, N ≤ sieveZ x → H ≤ sieveZ x → A ≤ sieveZ x →
      A + H < U → sieveY x < U → U * U ≤ A + Nat.lcmUpto N * r →
      (((Finset.Icc 1 H).filter (fun i => ¬ A + i ∣ Nat.lcmUpto N)).card : ℝ)
        ≤ sieveDelta * x →
      ∃ t < sieveT x, ∀ i, 1 ≤ i → i ≤ H → ∀ p s : ℕ, p.Prime →
        (A + Nat.lcmUpto N * r) + Nat.lcmUpto N * (t + 1) + i = p * s →
        A < s := by
  filter_upwards [eventually_fill_lcm_window] with x hfill
  intro N H A U r hNZ hHZ hAZ hAH hYU hbase hcard
  obtain ⟨t, ht, hdiv⟩ := hfill N H A U r hNZ hHZ hAZ hAH hYU hcard
  refine ⟨t, ht, ?_⟩
  intro i hi hiH p s hp heq
  obtain ⟨d, hAd, hdU, hd⟩ := hdiv i hi hiH
  have hsq : d * d < p * s := by
    have h := Nat.mul_self_lt_mul_self hdU
    omega
  rw [heq] at hd
  exact cofactor_gt_of_divisor hAd hsq hd hp.eq_one_or_self_of_dvd

end TranslatedDivisorCover

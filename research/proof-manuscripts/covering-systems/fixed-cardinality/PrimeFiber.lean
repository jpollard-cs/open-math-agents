import FormalConjectures.ErdosProblems.«1189»

/-! The prime-power cap for the exact covering-set predicate in Erdős #1189. -/
namespace FixedSizeCovering
open Erdos1189

/-- Divisors of the period that do not divide the step contain the full prime power. -/
private theorem top_power {p a v n : ℕ} (hp : p.Prime)
    (hn : n ∣ p ^ (a+1) * v) (hmiss : ¬ n ∣ p ^ a * v) :
    p ^ (a+1) ∣ n := by
  obtain ⟨c,hc⟩ := hn
  have hpc : ¬ p ∣ c := by
    rintro ⟨d, rfl⟩
    apply hmiss
    use d
    rw [pow_succ] at hc
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    simpa [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using hc
  apply ((hp.coprime_iff_not_dvd.mpr hpc).pow_left (a+1)).dvd_of_dvd_mul_right
  rw [← hc]
  exact dvd_mul_right _ _

/-- A project-defined irreducible cover with moduli at most X. A period with
    full p-part p^(a+1) forces p^(a+2) ≤ X whenever a modulus uses that part.
    The period may be any common multiple meeting the hypotheses. -/
theorem prime_power_cap {M : Finset ℕ} (hM : IsIrreducibleCoveringSet M)
    {p a v X : ℕ} (hp : p.Prime) (hv : ¬ p ∣ v)
    (period : ∀ n ∈ M, n ∣ p ^ (a+1) * v)
    (used : ∃ n ∈ M, ¬ n ∣ p ^ a * v)
    (cap : ∀ n ∈ M, n ≤ X) : p ^ (a+2) ≤ X := by
  classical
  let lower := M.filter (fun n => n ∣ p ^ a * v)
  have hsub : lower ⊂ M := by
    refine lt_of_le_of_ne (Finset.filter_subset _ _) ?_
    intro h
    obtain ⟨n, hn, hstep⟩ := used
    have hn' : n ∈ lower := h.symm ▸ hn
    exact hstep (Finset.mem_filter.mp hn').2
  obtain ⟨r,cover⟩ := hM.1.2
  have hx : ∃ x : ℤ, ∀ n ∈ lower, ¬ x ≡ r n [ZMOD n] := by
    by_contra! h
    exact hM.2 lower hsub ⟨fun n hn => hM.1.1 n ((Finset.mem_filter.mp hn).1), r, h⟩
  obtain ⟨x,hx⟩ := hx
  let site (j : ℕ) : ℤ := x + ((p ^ a * v * j : ℕ) : ℤ)
  choose owner howner hhit using fun j => cover (site j)
  have htop (j : ℕ) : p ^ (a+1) ∣ owner j := by
    apply top_power hp (period _ (howner j))
    intro hdiv
    apply hx _ (Finset.mem_filter.mpr ⟨howner j,hdiv⟩)
    apply Int.ModEq.trans (b := site j) _ (hhit j)
    rw [Int.modEq_iff_dvd]
    simp only [site, add_sub_cancel_left]
    exact_mod_cast dvd_mul_of_dvd_left hdiv j
  have hinj (i j : ℕ) (hi : i < p) (hj : j < p) (e : owner i = owner j) : i = j := by
    have he := hhit i
    rw [e] at he
    have hs := (he.trans (hhit j).symm).of_dvd (Int.ofNat_dvd.mpr (htop j))
    have hn := Int.natCast_modEq_iff.mp (Int.ModEq.add_left_cancel' x hs)
    rw [pow_succ, Nat.mul_assoc, Nat.mul_assoc] at hn
    have hcancel := Nat.ModEq.mul_left_cancel' (pow_ne_zero a hp.ne_zero) hn
    exact (Nat.ModEq.cancel_left_of_coprime (hp.coprime_iff_not_dvd.mpr hv) hcancel).eq_of_lt_of_lt hi hj
  let D := p ^ (a+1)
  have hD : 0 < D := Nat.pow_pos hp.pos
  have hcount : (Finset.range p).card ≤ (Finset.Icc 1 (X/D)).card := by
    apply Finset.card_le_card_of_injOn (fun i => owner i / D)
    · intro i _
      refine Finset.mem_Icc.mpr ⟨?_,Nat.div_le_div_right (cap _ (howner i))⟩
      have hge : D ≤ owner i := Nat.le_of_dvd (by have := hM.1.1 _ (howner i); omega) (htop i)
      exact (Nat.le_div_iff_mul_le hD).mpr (by simpa [D] using hge)
    · intro i hi j hj e
      apply hinj i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
      change owner i / D = owner j / D at e
      calc
        owner i = owner i / D * D := (Nat.div_mul_cancel (htop i)).symm
        _ = owner j / D * D := congrArg (· * D) e
        _ = owner j := Nat.div_mul_cancel (htop j)
  have h : p ≤ X/D := by simpa using hcount
  have hlast := (Nat.le_div_iff_mul_le hD).mp h
  simpa [D, pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlast

/-- No period data need be supplied: any prime power dividing an actual
    modulus forces the next power to lie below the cap. -/
theorem cap_of_member {M : Finset ℕ} (hM : IsIrreducibleCoveringSet M)
    {p a n X : ℕ} (hp : p.Prime) (hn : n ∈ M) (hpn : p ^ (a+1) ∣ n)
    (cap : ∀ d ∈ M, d ≤ X) : p ^ (a+2) ≤ X := by
  let L := M.lcm id
  have hL : L ≠ 0 := Finset.lcm_ne_zero_iff.mpr
    (fun m hm => by have h := hM.1.1 m hm; simpa using (show m ≠ 0 by omega))
  have hle : a+1 ≤ L.factorization p := (hp.pow_dvd_iff_le_factorization hL).mp
    (hpn.trans (Finset.dvd_lcm hn))
  let v := L / p ^ (L.factorization p)
  have hv : ¬ p ∣ v := Nat.not_dvd_ordCompl hp hL
  have hprod : p ^ (L.factorization p) * v = L := Nat.ordProj_mul_ordCompl_eq_self L p
  obtain ⟨b,hb⟩ : ∃ b, L.factorization p = b + 1 := ⟨L.factorization p - 1, by omega⟩
  rw [hb] at hprod
  have hvp : 0 < v := Nat.ordCompl_pos p hL
  have hsmall : p ^ b * v < L := by
    rw [← hprod, pow_succ]
    exact Nat.mul_lt_mul_of_pos_right
      (by simpa using Nat.mul_lt_mul_of_pos_left hp.one_lt (Nat.pow_pos hp.pos (n := b))) hvp
  have hit : ∃ d ∈ M, ¬ d ∣ p ^ b * v := by
    by_contra! h
    have hdiv : L ∣ p ^ b * v := Finset.lcm_dvd (fun d hd => h d hd)
    have hpos : 0 < p ^ b * v := Nat.mul_pos (Nat.pow_pos hp.pos) hvp
    exact (Nat.not_le_of_gt hsmall) (Nat.le_of_dvd hpos hdiv)
  have hcap := prime_power_cap hM hp hv
    (fun d hd => show d ∣ p ^ (b+1) * v by rw [hprod]; exact Finset.dvd_lcm hd) hit cap
  exact (Nat.pow_le_pow_right hp.pos (by omega : a+2 ≤ b+2)).trans hcap

#print axioms prime_power_cap
#print axioms cap_of_member
end FixedSizeCovering

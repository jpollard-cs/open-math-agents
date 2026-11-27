import Mathlib

/-! Selberg weights for the divisor density 1/d on the squarefree integers
up to an integer level. The normalization is at least the harmonic sum.
The signed weights are bounded by one and their main term is exactly the
reciprocal normalizer. This supplies the main term of the short-interval
sieve in Erdős, Graham, Ivić and Pomerance (1996), equations (14)–(17). -/
noncomputable section
open Finset UniqueFactorizationMonoid

namespace FactorialSieve

def level (z : ℕ) : Finset ℕ := (Icc 1 z).filter Squarefree

def normalizer (z : ℕ) : ℝ := ∑ d ∈ level z, ((d.totient : ℝ)⁻¹)

private lemma equal_totient_ratios {a b : ℕ} (h : a.primeFactors = b.primeFactors) :
    a.totient * b = b.totient * a := by
  have ha := Nat.totient_eq_mul_prod_factors a
  have hb := Nat.totient_eq_mul_prod_factors b
  rw [h] at ha
  exact_mod_cast (show (a.totient : ℚ)*b = (b.totient : ℚ)*a by rw [ha,hb]; ring)

private lemma radical_fiber (z q : ℕ) (hq : 0 < q) :
    (∑ n ∈ (Icc 1 z).filter (fun n : ℕ => radical n = q), (n : ℝ)⁻¹) ≤
    (q.totient : ℝ)⁻¹ := by
  let S := (Icc 1 z).filter (fun n : ℕ => radical n = q)
  let M := q ^ z
  let t (n : ℕ) := (M/n)*q
  have hM : 0 < M := pow_pos hq _
  have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have info (n : ℕ) (hn : n ∈ S) :
      0 < n ∧ 0 < t n ∧ t n * n = M*q ∧ t n ∣ M ∧ (t n).totient*n = M*q.totient := by
    obtain ⟨hi,hr⟩ := mem_filter.mp hn
    obtain ⟨hpos,hle⟩ := mem_Icc.mp hi
    have hqdiv : q ∣ n := hr ▸ radical_dvd_self
    have hd : n ∣ M := by
      have hd1 := Nat.dvd_radical_pow_self (show n ≠ 0 by omega)
      rw [hr] at hd1
      exact hd1.trans (pow_dvd_pow q hle)
    have hm := Nat.div_mul_cancel hd
    have hqk := Nat.div_mul_cancel hqdiv
    have heq : t n*n=M*q := by dsimp [t]; rw [mul_right_comm, hm]
    have ht : 0 < t n := by
      by_contra! hbad
      have hh : t n = 0 := by omega
      rw [hh, zero_mul] at heq
      exact (Nat.ne_of_gt (Nat.mul_pos hM hq)) heq.symm
    have hdM : t n ∣ M := by
      refine ⟨n/q, ?_⟩
      dsimp [t]
      rw [mul_assoc, mul_comm q (n/q), hqk, hm]
    have factors : (t n).primeFactors = q.primeFactors := by
      apply Subset.antisymm
      · exact (Nat.primeFactors_mono hdM hM.ne').trans (by
          by_cases hz : z = 0
          · omega
          · simp [M, Nat.primeFactors_pow _ hz])
      · exact Nat.primeFactors_mono (dvd_mul_left q _) ht.ne'
    have ratio := equal_totient_ratios factors
    have cross : (t n).totient*n*q = M*q.totient*q := by
      calc (t n).totient*n*q = ((t n).totient*q)*n := by ring
           _ = q.totient*(t n*n) := by rw [ratio]; ring
           _ = M*q.totient*q := by rw [heq]; ring
    exact ⟨hpos,ht,heq,hdM,Nat.eq_of_mul_eq_mul_right hq cross⟩
  have inj : Set.InjOn t S := by
    intro a ha b hb e
    obtain ⟨_,ht,hab,_,_⟩ := info a ha
    obtain ⟨_,_,hbb,_,_⟩ := info b hb
    rw [← e] at hbb
    exact Nat.eq_of_mul_eq_mul_left ht (hab.trans hbb.symm)
  have small : S.image t ⊆ M.divisors := by
    intro a ha
    obtain ⟨n, hn, rfl⟩ := mem_image.mp ha
    exact Nat.mem_divisors.mpr ⟨(info n hn).2.2.2.1,hM.ne'⟩
  have cnt : (∑ n ∈ S, (t n).totient) ≤ M := by
    rw [← Nat.sum_totient M, ← Finset.sum_image (f := Nat.totient) inj]
    exact sum_le_sum_of_subset_of_nonneg small (by intros; omega)
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  change (∑ n ∈ S, (n : ℝ)⁻¹) ≤ _
  calc
    _ = ∑ n ∈ S, ((t n).totient : ℝ)/(M*q.totient) := by
      apply sum_congr rfl
      intro n hn
      obtain ⟨hp,_,_,_,hh⟩ := info n hn
      have hpR : (0:ℝ) < n := by exact_mod_cast hp
      have hhR : ((t n).totient : ℝ)*n=(M:ℝ)*q.totient := by exact_mod_cast hh
      field_simp
      linarith
    _ = ((∑ n ∈ S, (t n).totient : ℕ):ℝ)/(M*q.totient) := by simp [sum_div]
    _ ≤ (M:ℝ)/(M*q.totient) := div_le_div_of_nonneg_right (by exact_mod_cast cnt) (by positivity)
    _ = _ := by field_simp

theorem harmonic_le_normalizer (z : ℕ) : (harmonic z : ℝ) ≤ normalizer z := by
  have maps (n : ℕ) (hn : n ∈ Icc 1 z) : radical n ∈ level z := by
    obtain ⟨hp,hle⟩ := mem_Icc.mp hn
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.radical_pos _,
      (Nat.radical_le_self_iff.mpr (by omega)).trans hle⟩, squarefree_radical⟩
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  simp only [Rat.cast_inv, Rat.cast_natCast]
  rw [← Finset.sum_fiberwise_of_maps_to maps (fun n : ℕ => (n:ℝ)⁻¹)]
  exact sum_le_sum (fun q hq => radical_fiber z q (mem_Icc.mp (mem_filter.mp hq).1).1)

theorem log_le_normalizer (z : ℕ) : Real.log ((z:ℝ)+1) ≤ normalizer z := by
  apply le_trans _ (harmonic_le_normalizer z)
  simpa using log_add_one_le_harmonic z


open ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

def alpha (z d : ℕ) : ℝ := (μ d : ℝ) * ∑ q ∈ level z, if d ∣ q then (q.totient : ℝ)⁻¹ else 0
def weight (z d : ℕ) : ℝ := d * alpha z d / normalizer z

lemma mem_level {z d : ℕ} : d ∈ level z ↔ (1 ≤ d ∧ d ≤ z) ∧ Squarefree d := by
  simp [level]

lemma down {z q d : ℕ} (hq : q ∈ level z) (hd : d ∣ q) : d ∈ level z := by
  obtain ⟨⟨hp,hle⟩,hs⟩ := mem_level.mp hq
  exact mem_level.mpr ⟨⟨Nat.pos_of_dvd_of_pos hd hp,(Nat.le_of_dvd hp hd).trans hle⟩,hs.squarefree_of_dvd hd⟩

private lemma mu_sum (m : ℕ) : (∑ k ∈ m.divisors, (μ k : ℝ)) = if m=1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f m) moebius_mul_coe_zeta
  simp only [coe_mul_zeta_apply, one_apply] at h
  split_ifs at h ⊢ <;> exact_mod_cast h

private lemma mu_interval {z q l : ℕ} (hq : q ∈ level z) (hl : l ∈ level z) :
    (∑ d ∈ level z, if l ∣ d ∧ d ∣ q then (μ d : ℝ) else 0) =
      if q=l then (μ l : ℝ) else 0 := by
  have lp := (mem_level.mp hl).1.1
  have qp := (mem_level.mp hq).1.1
  have qsf := (mem_level.mp hq).2
  by_cases hd : l ∣ q
  · obtain ⟨m, rfl⟩ := hd
    have mp : 0 < m := Nat.pos_of_mul_pos_left qp
    have shift (k : ℕ) (hk : k ∈ m.divisors) : l*k ∈ level z :=
      down hq (Nat.mul_dvd_mul_left l (Nat.dvd_of_mem_divisors hk))
    rw [← sum_filter]
    have ev : (∑ d ∈ (level z).filter (fun d => l ∣ d ∧ d ∣ l*m), (μ d : ℝ)) =
        ∑ k ∈ m.divisors, (μ l : ℝ)*(μ k : ℝ) := by
      symm
      apply sum_bij (fun k _ => l*k)
      · intro k hk
        exact mem_filter.mpr ⟨shift k hk, dvd_mul_right _ _, Nat.mul_dvd_mul_left _ (Nat.dvd_of_mem_divisors hk)⟩
      · intro a _ b _ he
        exact Nat.eq_of_mul_eq_mul_left lp he
      · intro d h
        obtain ⟨_, ⟨k,rfl⟩, hk⟩ := mem_filter.mp h
        exact ⟨k,Nat.mem_divisors.mpr ⟨Nat.dvd_of_mul_dvd_mul_left lp hk, mp.ne'⟩,rfl⟩
      · intro k hk
        have cop := Nat.coprime_of_squarefree_mul (mem_level.mp (shift k hk)).2
        exact_mod_cast (isMultiplicative_moebius.map_mul_of_coprime cop).symm
    rw [ev, ← mul_sum, mu_sum]
    by_cases hm : m=1
    · simp [hm]
    · have hne : l*m ≠ l := fun eq => hm (Nat.eq_of_mul_eq_mul_left lp (eq.trans (Nat.mul_one l).symm))
      simp [hm,hne]
  · have hne : q ≠ l := by rintro rfl; exact hd dvd_rfl
    rw [if_neg hne, sum_eq_zero]
    intro d _
    exact if_neg (fun h => hd (h.1.trans h.2))

/-- These are the diagonal coordinates of the unnormalized weights. -/
theorem transform {z l : ℕ} (hl : l ∈ level z) :
    (∑ d ∈ level z, if l ∣ d then alpha z d else 0) = (μ l : ℝ)*(l.totient : ℝ)⁻¹ := by
  calc
    _ = ∑ d ∈ level z, ∑ q ∈ level z, (if l ∣ d ∧ d ∣ q then (μ d : ℝ) else 0)*(q.totient : ℝ)⁻¹ := by
      apply sum_congr rfl
      intro d _
      by_cases hd : l ∣ d
      · simp only [if_pos hd, alpha, mul_sum]
        apply sum_congr rfl
        intro q _
        by_cases hq : d ∣ q <;> simp [hd,hq]
      · simp [hd]
    _ = ∑ q ∈ level z, (if q=l then (μ l : ℝ) else 0)*(q.totient : ℝ)⁻¹ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro q hq
      rw [← sum_mul, mu_interval hq hl]
    _ = _ := by simp [ite_mul, hl]

/-- Writing gcd(d,e) as a sum of totients diagonalizes the quadratic form. -/
theorem diagonal (z : ℕ) (a : ℕ → ℝ) :
    (∑ d ∈ level z, ∑ e ∈ level z, a d*a e*(d.gcd e : ℝ)) =
      ∑ l ∈ level z, (l.totient : ℝ)*(∑ d ∈ level z, if l ∣ d then a d else 0)^2 := by
  have expand {d e : ℕ} (hd : d ∈ level z) (he : e ∈ level z) :
      (d.gcd e : ℝ) = ∑ l ∈ level z, if l ∣ d ∧ l ∣ e then (l.totient : ℝ) else 0 := by
    rw [← sum_filter]
    have filt : (level z).filter (fun l => l ∣ d ∧ l ∣ e) = (d.gcd e).divisors := by
      ext l
      have gn : d.gcd e ≠ 0 := (Nat.gcd_pos_of_pos_left _ (mem_level.mp hd).1.1).ne'
      constructor
      · intro h
        exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd_iff.mpr (mem_filter.mp h).2,gn⟩
      · intro h
        have both := Nat.dvd_gcd_iff.mp (Nat.dvd_of_mem_divisors h)
        exact mem_filter.mpr ⟨down hd both.1,both⟩
    rw [filt, ← Nat.cast_sum, Nat.sum_totient]
  calc
    _ = ∑ d ∈ level z, ∑ e ∈ level z, ∑ l ∈ level z,
      (l.totient : ℝ)*(if l ∣ d then a d else 0)*(if l ∣ e then a e else 0) := by
      apply sum_congr rfl; intro d hd
      apply sum_congr rfl; intro e he
      rw [expand hd he, mul_sum]
      apply sum_congr rfl; intro l _
      by_cases h₁ : l ∣ d <;> by_cases h₂ : l ∣ e <;> simp [h₁,h₂]
      ring
    _ = _ := by
      simp_rw [sq, mul_sum, sum_mul]
      rw [sum_comm]
      -- Move the l-sum to the outside before collecting each of the two copies.
      conv_lhs => congr; rfl; intro e; rw [sum_comm]
      rw [sum_comm]
      apply sum_congr rfl; intro l _
      rw [sum_comm]
      apply sum_congr rfl; intro d _
      rw [mul_sum]
      apply sum_congr rfl; intro e _
      ring

theorem normalizer_pos {z : ℕ} (hz : 1 ≤ z) : 0 < normalizer z := by
  apply Finset.sum_pos' (fun q _ => by positivity)
  exact ⟨1, mem_level.mpr ⟨⟨le_rfl,hz⟩,squarefree_one⟩, by norm_num⟩

theorem weight_one {z : ℕ} (hz : 1 ≤ z) : weight z 1 = 1 := by
  simp [weight,alpha,normalizer]
  exact (normalizer_pos hz).ne'

/-- Exact value of the Selberg main term for the constructed weights. -/
theorem main_term {z : ℕ} (hz : 1 ≤ z) :
    (∑ d ∈ level z, ∑ e ∈ level z, weight z d*weight z e/(Nat.lcm d e : ℝ)) = (normalizer z)⁻¹ := by
  have gp := normalizer_pos hz
  have diag := diagonal z (alpha z)
  have eval : (∑ d ∈ level z, ∑ e ∈ level z, alpha z d*alpha z e*(d.gcd e : ℝ)) = normalizer z := by
    rw [diag]
    apply sum_congr rfl
    intro l hl
    rw [transform hl]
    have sqμ := moebius_sq_eq_one_of_squarefree (mem_level.mp hl).2
    have sqR : (μ l : ℝ)^2=1 := by exact_mod_cast sqμ
    have tp : (0:ℝ) < l.totient := by exact_mod_cast Nat.totient_pos.mpr (mem_level.mp hl).1.1
    rw [mul_pow, sqR, one_mul]
    field_simp
  calc
    _ = (∑ d ∈ level z, ∑ e ∈ level z, alpha z d*alpha z e*(d.gcd e : ℝ))/(normalizer z)^2 := by
      simp only [sum_div]
      apply sum_congr rfl; intro d hd
      apply sum_congr rfl; intro e he
      have hp := Nat.lcm_pos (mem_level.mp hd).1.1 (mem_level.mp he).1.1
      have lp : (0:ℝ) < Nat.lcm d e := by exact_mod_cast hp
      have eq : (d.gcd e : ℝ)*(d.lcm e : ℝ)=(d:ℝ)*e := by exact_mod_cast Nat.gcd_mul_lcm d e
      dsimp only [weight]
      field_simp
      linear_combination (alpha z d * alpha z e) * (-eq)
    _ = _ := by rw [eval]; field_simp

/-- For each multiple q of d, deleting a divisor of d gives a different
member of the level. Its least common multiple with d recovers q. -/
lemma divisor_budget (z d : ℕ) :
    (∑ q ∈ (level z).filter (fun q => d ∣ q), (d:ℝ)/(q.totient:ℝ)) ≤ normalizer z := by
  let F := (level z).filter (fun q => d ∣ q)
  let pairs := F ×ˢ d.divisors
  let f (x : ℕ × ℕ) := x.1/x.2
  have pair_facts (x : ℕ × ℕ) (hx : x ∈ pairs) :
      f x ∈ level z ∧ d.lcm (f x) = x.1 ∧ x.1/(f x) = x.2 := by
    obtain ⟨hq,ht⟩ := mem_product.mp hx
    obtain ⟨hL,hdq⟩ := mem_filter.mp hq
    have td := Nat.dvd_of_mem_divisors ht
    have tq := td.trans hdq
    have fs := Nat.div_mul_cancel tq
    have hf := Nat.div_dvd_of_dvd tq
    have cp := Nat.coprime_of_squarefree_mul (by rw [fs]; exact (mem_level.mp hL).2)
    refine ⟨down hL hf,Nat.dvd_antisymm (Nat.lcm_dvd hdq hf) ?_,Nat.div_div_self tq (mem_level.mp hL).2.ne_zero⟩
    change x.1 ∣ d.lcm (x.1/x.2)
    have hprod := cp.mul_dvd_of_dvd_of_dvd (Nat.dvd_lcm_right d (x.1/x.2))
      (td.trans (Nat.dvd_lcm_left d _))
    rwa [fs] at hprod
  have inj : Set.InjOn f pairs := by
    intro x hx y hy h
    obtain ⟨_,hl,hdiv⟩ := pair_facts x hx
    obtain ⟨_,hl',hdiv'⟩ := pair_facts y hy
    have qeq := hl.symm.trans ((congrArg (Nat.lcm d) h).trans hl')
    exact Prod.ext qeq (hdiv.symm.trans (by rw [qeq,h,hdiv']))
  have sub : pairs.image f ⊆ level z := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    exact (pair_facts y hy).1
  have row (q : ℕ) (hq : q ∈ F) :
      (d:ℝ)/(q.totient:ℝ) = ∑ t ∈ d.divisors, ((q/t).totient:ℝ)⁻¹ := by
    obtain ⟨hL,hdq⟩ := mem_filter.mp hq
    have pos := (mem_level.mp hL).1.1
    have ttl : (∑ t ∈ d.divisors, (t.totient:ℝ)) = d := by exact_mod_cast Nat.sum_totient d
    rw [← ttl, sum_div]
    apply sum_congr rfl
    intro t ht
    have tq := (Nat.dvd_of_mem_divisors ht).trans hdq
    have hf := Nat.div_mul_cancel tq
    have sf : Squarefree (q/t*t) := by rw [hf]; exact (mem_level.mp hL).2
    have cop := Nat.coprime_of_squarefree_mul sf
    have tot := Nat.totient_mul cop
    rw [hf] at tot
    have posT : 0 < t.totient := Nat.totient_pos.mpr (Nat.pos_of_mem_divisors ht)
    have posU : 0 < (q/t).totient := Nat.totient_pos.mpr (Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd tq) pos)
    rw [tot, Nat.cast_mul]
    field_simp
  calc
    _ = ∑ q ∈ F, ∑ t ∈ d.divisors, ((q/t).totient:ℝ)⁻¹ := sum_congr rfl row
    _ = ∑ x ∈ pairs, ((f x).totient:ℝ)⁻¹ := by rw [Finset.sum_product]
    _ = ∑ q ∈ pairs.image f, (q.totient:ℝ)⁻¹ := (sum_image (f := fun n : ℕ => (n.totient:ℝ)⁻¹) inj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg sub (by intros; positivity)

theorem weight_abs_le_one {z d : ℕ} (hz : 1 ≤ z) (hd : d ∈ level z) :
    |weight z d| ≤ 1 := by
  have sfree := (mem_level.mp hd).2
  have hm : |(μ d : ℝ)| = 1 := by exact_mod_cast abs_moebius_eq_one_of_squarefree sfree
  have gp := normalizer_pos hz
  let F := (level z).filter (fun q => d ∣ q)
  have nonneg : 0 ≤ ∑ q ∈ F, (q.totient:ℝ)⁻¹ := sum_nonneg (by intros; positivity)
  rw [weight,alpha, ← sum_filter, abs_div, abs_mul, abs_mul, hm, one_mul,
    abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos gp, abs_of_nonneg nonneg, div_le_one gp, mul_sum]
  simpa only [div_eq_mul_inv] using divisor_budget z d


theorem main_term_bound {z : ℕ} (hz : 1 ≤ z) :
    (∑ d ∈ level z, ∑ e ∈ level z, weight z d*weight z e/(Nat.lcm d e : ℝ)) ≤
    (Real.log ((z:ℝ)+1))⁻¹ := by
  rw [main_term hz]
  have pos : 0 < Real.log ((z:ℝ)+1) := Real.log_pos (by exact_mod_cast (show 1 < z+1 by omega))
  exact inv_anti₀ pos (log_le_normalizer z)

end FactorialSieve
#print axioms FactorialSieve.main_term_bound
#print axioms FactorialSieve.weight_abs_le_one

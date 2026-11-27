import OMAReductions.R_Erdos420_erdos_420_variants_pow_four_ninths_R1

/-!
# A finite sieve reduction for the intermediate-prime estimate

The analytic input is an unweighted count of prime occurrences on 48 fixed
logarithmic bands. These bounds follow on paper by summing (19) of Erdős,
Graham, Ivić and Pomerance over multiplicative blocks. The theorem
prime_power_removal below proves the second hypothesis unconditionally.
-/

namespace OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R2

open Finset Real Filter
open scoped Classical

/-- On each of the 48 fixed bands, count a prime only once per window term.
The tolerance absorbs the uniform error in the local sieve bound. -/
def H1 : Prop := ∀ᶠ n : ℕ in atTop,
  let edge (j : ℕ) : ℚ :=
    if j ≤ 16 then 4/9 + j*(77/162-4/9)/16
    else if j ≤ 32 then 77/162 + ((j-16 : ℕ) : ℚ)*(29/54-77/162)/16
    else 29/54 + ((j-32 : ℕ) : ℚ)*(50009/90000-29/54)/16
  let allowance (j : ℕ) : ℚ :=
    let v := edge (j+1)
    let θ := if j < 16 then (4/7)/(17/42-(5/7)*v)
             else if j < 32 then 1/(19/54-v/2) else 12
    (v-edge j)*θ + 1/1000000
  let h := ⌊(n:ℝ)^(4/9:ℝ)⌋₊
  let S := (range h).sigma (fun i => (n+i+1).primeFactors.filter (fun p : ℕ =>
    (n:ℝ)^(4/9:ℝ) < p ∧ (p:ℝ) ≤ (n:ℝ)^(5/9+1/10000:ℝ)))
  ∀ j < 48,
    ((S.filter (fun z => (n:ℝ)^(edge j : ℝ) < (z.2:ℝ) ∧
      (z.2:ℝ) ≤ (n:ℝ)^(edge (j+1) : ℝ))).card : ℝ) ≤ (allowance j : ℝ)*h

/-- Repeated prime powers in the middle range have negligible logarithmic weight. -/
def H2 : Prop := ∀ᶠ n : ℕ in atTop,
  let h := ⌊(n:ℝ)^(4/9:ℝ)⌋₊
  let S := (range h).sigma (fun i => (n+i+1).primeFactors.filter (fun p : ℕ =>
    (n:ℝ)^(4/9:ℝ) < p ∧ (p:ℝ) ≤ (n:ℝ)^(5/9+1/10000:ℝ)))
  (∑ z ∈ S, ((n+z.1+1).factorization z.2 : ℝ)*log z.2) ≤
    (∑ z ∈ S, log z.2) + (1/5000)*(h:ℝ)*log n

/-- An interval of length h contains at most (n+h)/(h+1)² pairs (m,p)
with p > h and p² ∣ m. The base p can be composite. -/
theorem square_hits (n h : ℕ) (s : Finset (ℕ × ℕ))
    (hits : ∀ z ∈ s, n < z.1 ∧ z.1 ≤ n+h ∧ h < z.2 ∧ z.2^2 ∣ z.1) :
    s.card ≤ (n+h)/(h+1)^2 := by
  let q (z : ℕ × ℕ) := z.1 / z.2^2
  have recover (z : ℕ × ℕ) (hz : z ∈ s) : q z * z.2^2 = z.1 :=
    Nat.div_mul_cancel (hits z hz).2.2.2
  have pos (z : ℕ × ℕ) (hz : z ∈ s) : 0 < q z := by
    by_contra! hn
    have hzero : q z = 0 := by omega
    have hrec := recover z hz
    rw [hzero, zero_mul] at hrec
    have := (hits z hz).1
    omega
  have gap {p r t : ℕ} (ht : 0 < t) (hp : h < p) (hpr : p < r) :
      t*p^2+h < t*r^2 := by
    have hstep : p^2 + (h+1) ≤ r^2 := by
      have hs := Nat.pow_le_pow_left (show p+1 ≤ r by omega) 2
      nlinarith
    have hh := Nat.mul_le_mul_left t hstep
    have hg := Nat.mul_le_mul_right (h+1) (show 1 ≤ t by omega)
    nlinarith
  have bound := Finset.card_le_card_of_injOn (s := s)
    (t := Icc 1 ((n+h)/(h+1)^2)) q (by
      intro z hz
      obtain ⟨_, hu, hp, _⟩ := hits z hz
      apply mem_Icc.mpr
      refine ⟨pos z hz, (Nat.le_div_iff_mul_le (by positivity)).mpr ?_⟩
      calc q z * (h+1)^2 ≤ q z * z.2^2 :=
             Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
           _ = z.1 := recover z hz
           _ ≤ n+h := hu) (by
      intro x hx y hy eq
      obtain ⟨hxl, hxu, hxp, _⟩ := hits x hx
      obtain ⟨hyl, hyu, hyp, _⟩ := hits y hy
      have rx := recover x hx
      have ry := recover y hy
      rw [← eq] at ry
      have hp : x.2 = y.2 := by
        rcases lt_trichotomy x.2 y.2 with h|h|h
        · have hg := gap (pos x hx) hxp h
          omega
        · exact h
        · have hg := gap (pos x hx) hyp h
          omega
      apply Prod.ext _ hp
      rw [hp] at rx
      omega)
  simpa using bound

/-- Replacing valuations by one copy per prime incurs at most the displayed
additive error. The input s may restrict the primes to any desired band. -/
theorem weighted_excess (n h : ℕ) (s : Finset (ℕ × ℕ)) (hcube : n+h < (h+1)^3)
    (hits : ∀ z ∈ s, n < z.1 ∧ z.1 ≤ n+h ∧ h < z.2 ∧ z.2.Prime ∧ z.2 ∣ z.1) :
    (∑ z ∈ s, (z.1.factorization z.2 : ℝ) * log z.2) ≤
      (∑ z ∈ s, log z.2) + (((n+h)/(h+1)^2 : ℕ) : ℝ) * log (n+h : ℕ) := by
  let t := s.filter (fun z => z.2^2 ∣ z.1)
  have bound := square_hits n h t (by
    intro z hz
    obtain ⟨hs, hd⟩ := mem_filter.mp hz
    obtain ⟨hl, hu, hp, _⟩ := hits z hs
    exact ⟨hl, hu, hp, hd⟩)
  have hlog : 0 ≤ log (n+h : ℕ) := Real.log_natCast_nonneg _
  have single (z : ℕ × ℕ) (hz : z ∈ s) :
      (z.1.factorization z.2 : ℝ) * log z.2 ≤
        log z.2 + (if z.2^2 ∣ z.1 then log (n+h : ℕ) else 0) := by
    obtain ⟨hl, hu, hp, hprime, hd⟩ := hits z hz
    have hm : z.1 ≠ 0 := by omega
    have ppos := hprime.pos
    have logp := Real.log_natCast_nonneg z.2
    have logle : log (z.2 : ℝ) ≤ log (n+h : ℕ) :=
      log_le_log (by exact_mod_cast ppos) (by exact_mod_cast (Nat.le_of_dvd (by omega) hd).trans hu)
    have exp_le : z.1.factorization z.2 ≤ 2 := by
      by_contra! hbig
      have hd3 := (hprime.pow_dvd_iff_le_factorization hm).mpr (show 3 ≤ z.1.factorization z.2 by omega)
      have hlo := Nat.pow_le_pow_left (show h+1 ≤ z.2 by omega) 3
      have hhi := Nat.le_of_dvd (show 0 < z.1 by omega) hd3
      omega
    split_ifs with hs
    · have he : (z.1.factorization z.2 : ℝ) ≤ 2 := by exact_mod_cast exp_le
      nlinarith [mul_nonneg (sub_nonneg.mpr he) logp]
    · have he : z.1.factorization z.2 ≤ 1 := by
        by_contra! hh
        exact hs ((hprime.pow_dvd_iff_le_factorization hm).mpr hh)
      have he' : (z.1.factorization z.2 : ℝ) ≤ 1 := by exact_mod_cast he
      nlinarith [mul_nonneg (sub_nonneg.mpr he') logp]
  calc (∑ z ∈ s, (z.1.factorization z.2 : ℝ) * log z.2) ≤ _ := sum_le_sum single
       _ = (∑ z ∈ s, log z.2) + (t.card : ℝ)*log (n+h : ℕ) := by
         rw [sum_add_distrib, ← sum_filter]
         simp [t]
       _ ≤ _ := by gcongr


/-- At the four-ninths window, the square-hit budget is at most 2 n^(1/9). -/
theorem four_ninths_scale : ∀ᶠ n : ℕ in Filter.atTop,
    let h := ⌊(n:ℝ)^(4/9 : ℝ)⌋₊
    n+h < (h+1)^3 ∧ (((n+h)/(h+1)^2 : ℕ) : ℝ) ≤ 2*(n:ℝ)^(1/9 : ℝ) := by
  have pw : Filter.Tendsto (fun n : ℕ => (n:ℝ)^(1/3:ℝ)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/3)).comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_ge_atTop (1:ℕ), pw.eventually_ge_atTop 2] with n hn hthird
  let A := (n:ℝ)^(4/9:ℝ)
  let h := ⌊A⌋₊
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hA : 0 ≤ A := Real.rpow_nonneg hn0.le _
  have hfloor : A < (h:ℝ)+1 := Nat.lt_floor_add_one A
  have hsmall : (h:ℝ) ≤ n := (Nat.floor_le hA).trans (by
    simpa [A] using Real.rpow_le_rpow_of_exponent_le hn1 (show (4:ℝ)/9 ≤ 1 by norm_num))
  have cube : A^3 = (n:ℝ)*(n:ℝ)^(1/3:ℝ) := by
    dsimp [A]
    rw [← Real.rpow_mul_natCast hn0.le, show (4/9:ℝ)*(3:ℕ) = 1+1/3 by norm_num, Real.rpow_add hn0, Real.rpow_one]
  have square : A^2*(n:ℝ)^(1/9:ℝ) = n := by
    dsimp [A]
    rw [← Real.rpow_mul_natCast hn0.le, ← Real.rpow_add hn0]
    norm_num
  change n+h < (h+1)^3 ∧ _
  constructor
  · have hcube : A^3 < ((h:ℝ)+1)^3 := pow_lt_pow_left₀ hfloor hA (by decide)
    have hn3 : (n:ℝ)+(h:ℝ) < ((h:ℝ)+1)^3 := by
      nlinarith [mul_nonneg hn0.le (sub_nonneg.mpr hthird)]
    exact_mod_cast hn3
  · let q := (n+h)/(h+1)^2
    have hdiv : q*(h+1)^2 ≤ n+h := Nat.div_mul_le_self _ _
    have hdivR : (q:ℝ)*((h:ℝ)+1)^2 ≤ (n:ℝ)+h := by exact_mod_cast hdiv
    have hs := pow_le_pow_left₀ hA hfloor.le 2
    have hx : 0 < A^2 := by dsimp [A]; positivity
    have hx' : (q:ℝ)*A^2 ≤ (2*(n:ℝ)^(1/9:ℝ))*A^2 := by
      nlinarith [mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg q)]
    exact (mul_le_mul_iff_left₀ hx).mp hx'


/-- The logarithmic cost of repeated hits is eventually at most one five-thousandth
of the total window scale. No estimate on the distribution of primes is used. -/
theorem four_ninths_error : ∀ᶠ n : ℕ in atTop,
    let h := ⌊(n:ℝ)^(4/9:ℝ)⌋₊
    n+h < (h+1)^3 ∧
    (((n+h)/(h+1)^2 : ℕ) : ℝ)*log (n+h : ℕ) ≤ (1/5000)*(h:ℝ)*log n := by
  have pw (r : ℝ) (hr : 0 < r) : Tendsto (fun n : ℕ => (n:ℝ)^r) atTop atTop :=
    (tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop
  filter_upwards [four_ninths_scale, eventually_ge_atTop (2:ℕ),
    (pw (1/3) (by norm_num)).eventually_ge_atTop 40000,
    (pw (4/9) (by norm_num)).eventually_ge_atTop 2] with n hs hn hthird hbig
  let A := (n:ℝ)^(4/9:ℝ)
  let h := ⌊A⌋₊
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0:ℝ) < n := by linarith
  have hA : 0 ≤ A := Real.rpow_nonneg hn0.le _
  have hle : (h:ℝ) ≤ n := (Nat.floor_le hA).trans (by
    simpa [A] using Real.rpow_le_rpow_of_exponent_le hn1 (show (4:ℝ)/9 ≤ 1 by norm_num))
  have hfloor : A < (h:ℝ)+1 := Nat.lt_floor_add_one A
  change 2 ≤ A at hbig
  have heq : (n:ℝ)^(1/9:ℝ)*(n:ℝ)^(1/3:ℝ) = A := by
    rw [← Real.rpow_add hn0]
    dsimp [A]
    norm_num
  change 40000 ≤ (n:ℝ)^(1/3:ℝ) at hthird
  have ninth := Real.rpow_nonneg hn0.le (1/9:ℝ)
  have coeff : 4*(n:ℝ)^(1/9:ℝ) ≤ (1/5000)*(h:ℝ) := by
    nlinarith [mul_nonneg ninth (sub_nonneg.mpr hthird)]
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have arg : (0:ℝ) < n+h := by positivity
  have logle : log (n+h : ℕ) ≤ 2*log n := by
    push_cast
    calc log ((n:ℝ)+h) ≤ log ((n:ℝ)^2) :=
           log_le_log arg (by nlinarith [mul_nonneg hn0.le (sub_nonneg.mpr hn2)])
         _ = 2*log n := by simp [Real.log_pow]
  refine ⟨hs.1, ?_⟩
  have lognonneg := Real.log_natCast_nonneg n
  calc
    _ ≤ (2*(n:ℝ)^(1/9:ℝ))*(2*log n) :=
      mul_le_mul hs.2 logle (Real.log_natCast_nonneg _) (by positivity)
    _ = (4*(n:ℝ)^(1/9:ℝ))*log n := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right coeff lognonneg

lemma crossing(f : ℕ → ℝ) (x : ℝ) (h0 : f 0 < x) (k : ℕ) (hk : x ≤ f k) :
    ∃ j < k, f j < x ∧ x ≤ f (j+1) := by
  induction k with
  | zero => exact (not_lt_of_ge hk h0).elim
  | succ k ih =>
    by_cases hend : x ≤ f k
    · obtain ⟨j, hj, lo, hi⟩ := ih hend
      exact ⟨j, by omega, lo, hi⟩
    · exact ⟨k, by omega, lt_of_not_ge hend, hk⟩

/-- The log weight of any set of hits in the complete middle range is bounded
by the finite unweighted counts. S can label a prime together with its position. -/
theorem first_power_mass (edge allowance : ℕ → ℚ)
    (edge0 : edge 0 = 4/9) (edge48 : edge 48 = 5/9+1/10000)
    (edge_nonnegative : ∀ j, 0 ≤ edge (j+1))
    (budget : (4/9 : ℚ) + ∑ j ∈ range 48, edge (j+1)*allowance j < 2499/2500)
    {α : Type*} (S : Finset α) (p : α → ℕ) (n h : ℕ) (hn : 1 ≤ n)
    (range_hits : ∀ z ∈ S, (n:ℝ)^(4/9:ℝ) < (p z:ℝ) ∧
      (p z:ℝ) ≤ (n:ℝ)^(5/9+1/10000:ℝ))
    (counts : ∀ j < 48,
      ((S.filter (fun z => (n:ℝ)^(edge j : ℝ) < (p z:ℝ) ∧
        (p z:ℝ) ≤ (n:ℝ)^(edge (j+1) : ℝ))).card : ℝ) ≤ (allowance j : ℝ)*h) :
    (∑ z ∈ S, log (p z)) ≤ (5/9-1/2500)*(h:ℝ)*log n := by
  let bin (j : ℕ) := S.filter (fun z => (n:ℝ)^(edge j : ℝ) < (p z:ℝ) ∧
                                      (p z:ℝ) ≤ (n:ℝ)^(edge (j+1) : ℝ))
  let cap (j : ℕ) := (edge (j+1) : ℝ)*log n
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have cap_pos (j : ℕ) : 0 ≤ cap j := by
    exact mul_nonneg (by exact_mod_cast edge_nonnegative j) (Real.log_natCast_nonneg n)
  have cover (z : α) (hz : z ∈ S) :
      ∃ j < 48, z ∈ bin j ∧ log (p z) ≤ cap j := by
    obtain ⟨hlo,hhi⟩ := range_hits z hz
    let f (j : ℕ) := (n:ℝ)^(edge j : ℝ)
    have hzero : f 0 < (p z:ℝ) := by simpa [f,edge0] using hlo
    have hlast : (p z:ℝ) ≤ f 48 := by simpa [f,edge48] using hhi
    obtain ⟨j, hj, lo, hi⟩ := crossing f (p z) hzero 48 hlast
    have pp : (0:ℝ) < p z := (Real.rpow_pos_of_pos hn0 _).trans lo
    refine ⟨j,hj,mem_filter.mpr ⟨hz, lo, hi⟩, ?_⟩
    simpa only [f, cap, log_rpow hn0] using Real.log_le_log pp hi
  have point (z : α) (hz : z ∈ S) : log (p z) ≤ ∑ j ∈ range 48, if z ∈ bin j then cap j else 0 := by
    obtain ⟨j,hj,hmem,hle⟩ := cover z hz
    apply hle.trans
    have hs := Finset.single_le_sum (f := fun j => if z ∈ bin j then cap j else 0)
      (fun j (_ : j ∈ range 48) => by split <;> first | exact cap_pos j | exact le_rfl) (mem_range.mpr hj)
    simpa only [if_pos hmem] using hs
  calc
    (∑ z ∈ S, log (p z)) ≤ _ := sum_le_sum point
    _ = ∑ j ∈ range 48, ((bin j).card : ℝ)*cap j := by
      rw [sum_comm]
      apply sum_congr rfl
      intro j hj
      rw [← sum_filter]
      have filt : S.filter (fun z => z ∈ bin j) = bin j := by
        ext z
        simp [bin]
      simp [filt]
    _ ≤ ∑ j ∈ range 48, ((allowance j : ℝ)*h)*cap j := by
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (counts j (mem_range.mp hj)) (cap_pos j)
    _ = ((∑ j ∈ range 48, edge (j+1)*allowance j : ℚ) : ℝ)*h*log n := by
      push_cast
      simp only [sum_mul]
      apply sum_congr rfl
      intro j _
      dsimp [cap]
      ring
    _ ≤ _ := by
      have H := budget
      have R : (∑ j ∈ range 48, edge (j+1)*allowance j : ℚ) ≤ 5/9-1/2500 := by linarith
      have R' : ((∑ j ∈ range 48, edge (j+1)*allowance j : ℚ):ℝ) ≤ 5/9-1/2500 := by
        have v := (Rat.cast_le (K := ℝ)).mpr R
        norm_num at v ⊢
        exact v
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right R' (Nat.cast_nonneg _))
        (Real.log_natCast_nonneg _)

/-- The second input is already proved; its proof uses no sieve estimate. -/
theorem prime_power_removal : H2 := by
  filter_upwards [four_ninths_error] with n herr
  let h := ⌊(n:ℝ)^(4/9:ℝ)⌋₊
  let S := (range h).sigma (fun i => (n+i+1).primeFactors.filter (fun p : ℕ =>
    (n:ℝ)^(4/9:ℝ) < p ∧ (p:ℝ) ≤ (n:ℝ)^(5/9+1/10000:ℝ)))
  let e : (Σ _ : ℕ, ℕ) ↪ (ℕ × ℕ) := ⟨fun z => (n+z.1+1,z.2), by
    rintro ⟨i,p⟩ ⟨j,q⟩ heq
    have hi := congrArg Prod.fst heq
    have hp := congrArg Prod.snd heq
    change n+i+1=n+j+1 at hi
    change p=q at hp
    have ij : i=j := by omega
    subst j
    subst q
    rfl⟩
  have hA : (h:ℝ) ≤ (n:ℝ)^(4/9:ℝ) := Nat.floor_le (by positivity)
  have mass := weighted_excess n h (S.map e) herr.1 (by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := mem_map.mp hx
    obtain ⟨hi, hp⟩ := mem_sigma.mp hz
    have hilt := mem_range.mp hi
    obtain ⟨hp, hlo, _⟩ := mem_filter.mp hp
    change n < n+z.1+1 ∧ n+z.1+1 ≤ n+h ∧ h < z.2 ∧ z.2.Prime ∧ z.2 ∣ n+z.1+1
    exact ⟨by omega, by omega, by exact_mod_cast hA.trans_lt hlo,
      Nat.prime_of_mem_primeFactors hp, Nat.dvd_of_mem_primeFactors hp⟩)
  change (∑ z ∈ S, ((n+z.1+1).factorization z.2 : ℝ)*log z.2) ≤
    (∑ z ∈ S, log z.2) + (1/5000)*(h:ℝ)*log n
  have em (z : (Σ _ : ℕ, ℕ)) : e z = (n+z.1+1,z.2) := rfl
  simp only [Finset.sum_map, em] at mass
  exact mass.trans (add_le_add le_rfl herr.2)

set_option maxRecDepth 4000 in
theorem main : H1 → H2 → OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1.H2 := by
  intro hcount hrepeat
  refine ⟨1/5000, by norm_num, ?_⟩
  filter_upwards [hcount, hrepeat, eventually_ge_atTop (1:ℕ)] with n hc hr hn
  let edge (j : ℕ) : ℚ :=
    if j ≤ 16 then 4/9 + j*(77/162-4/9)/16
    else if j ≤ 32 then 77/162 + ((j-16 : ℕ) : ℚ)*(29/54-77/162)/16
    else 29/54 + ((j-32 : ℕ) : ℚ)*(50009/90000-29/54)/16
  let allowance (j : ℕ) : ℚ :=
    let v := edge (j+1)
    let θ := if j < 16 then (4/7)/(17/42-(5/7)*v)
             else if j < 32 then 1/(19/54-v/2) else 12
    (v-edge j)*θ + 1/1000000
  let h := ⌊(n:ℝ)^(4/9:ℝ)⌋₊
  let S := (range h).sigma (fun i => (n+i+1).primeFactors.filter (fun p : ℕ =>
    (n:ℝ)^(4/9:ℝ) < p ∧ (p:ℝ) ≤ (n:ℝ)^(5/9+1/10000:ℝ)))
  have zero : edge 0 = 4/9 := by norm_num [edge]
  have last : edge 48 = 5/9+1/10000 := by norm_num [edge]
  have nonneg (j : ℕ) : 0 ≤ edge (j+1) := by
    dsimp only [edge]
    split
    · norm_num
      positivity
    · split <;> norm_num <;> positivity
  have B : (4/9 : ℚ) + ∑ j ∈ range 48, edge (j+1)*allowance j < 2499/2500 := by
    dsimp only [edge, allowance]
    decide +kernel
  have sta := first_power_mass edge allowance zero last nonneg B S (fun z => z.2) n h hn
    (fun z hz => (mem_filter.mp (mem_sigma.mp hz).2).2) hc
  change (∑ z ∈ S, ((n+z.1+1).factorization z.2 : ℝ)*log z.2) ≤
    (∑ z ∈ S, log z.2) + (1/5000)*(h:ℝ)*log n at hr
  have bound := hr.trans (add_le_add sta le_rfl)
  have total : (∑ z ∈ S, ((n+z.1+1).factorization z.2 : ℝ)*log z.2) ≤
      (5/9-1/5000)*(h:ℝ)*log n := by linarith only [bound]
  simpa only [S, Finset.sum_sigma] using total

end OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R2
#print axioms OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R2.main
#print axioms OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1_H2_R2.prime_power_removal

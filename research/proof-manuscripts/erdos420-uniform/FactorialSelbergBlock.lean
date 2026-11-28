import FactorialSelbergWeights
import FiniteWindowSieve

/-! Boundary error for the harmonic sum of the multiples of a single
modulus in a multiplicative interval. Both endpoints may be real. -/
noncomputable section
open Finset Real
namespace FactorialRounding

private lemma harmonic_bracket (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    log ((b:ℝ)+1) - log ((a:ℝ)+1) ≤ ∑ j ∈ Ioc a b, (j:ℝ)⁻¹ ∧
    (∑ j ∈ Ioc a b, (j:ℝ)⁻¹) ≤ log b - log a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b h ih =>
    have bp : (0:ℝ) < b := by exact_mod_cast (show 0 < b by omega)
    have p : 0 < (b:ℝ)+1 := by positivity
    have pp : 0 < (b:ℝ)+1+1 := by positivity
    have top := Real.log_le_sub_one_of_pos (div_pos pp p)
    rw [log_div pp.ne' p.ne'] at top
    have low := Real.one_sub_inv_le_log_of_pos (div_pos p bp)
    rw [log_div p.ne' bp.ne'] at low
    have e₁ : ((b:ℝ)+1+1)/(b+1)-1 = ((b:ℝ)+1)⁻¹ := by field_simp; ring
    have e₂ : 1-(((b:ℝ)+1)/b)⁻¹ = ((b:ℝ)+1)⁻¹ := by field_simp; ring
    rw [e₁] at top
    rw [e₂] at low
    rw [sum_Ioc_succ_top h]
    push_cast
    exact ⟨by linarith [ih.1], by linarith [ih.2]⟩

lemma harmonic_floor_error (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) :
    |(∑ j ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, (j:ℝ)⁻¹) - log (v/u)| ≤ 2/u := by
  let a := ⌊u⌋₊
  let b := ⌊v⌋₊
  have up : 0 < u := by linarith
  have vp : 0 < v := by linarith
  have ha : 1 ≤ a := Nat.floor_pos.mpr hu
  have ap : (0:ℝ) < a := by exact_mod_cast ha
  have hab : a ≤ b := Nat.floor_mono huv
  have bp : (0:ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have al : (a:ℝ) ≤ u := Nat.floor_le up.le
  have ah : u < (a:ℝ)+1 := Nat.lt_floor_add_one u
  have bl : (b:ℝ) ≤ v := Nat.floor_le vp.le
  have bh : v < (b:ℝ)+1 := Nat.lt_floor_add_one v
  have e₁ : log ((a:ℝ)+1)-log u ≤ 1/u := by
    have h := Real.log_le_sub_one_of_pos (div_pos (by positivity : 0 < (a:ℝ)+1) up)
    rw [log_div (by positivity) up.ne'] at h
    apply h.trans
    rw [sub_le_iff_le_add, div_le_iff₀ up]
    field_simp
    linarith
  have e₂ : log u - log a ≤ 2/u := by
    have h := Real.log_le_sub_one_of_pos (div_pos up ap)
    rw [log_div up.ne' ap.ne'] at h
    apply h.trans
    have step : u/(a:ℝ)-1 ≤ 1/a := by
      rw [sub_le_iff_le_add, div_le_iff₀ ap]
      field_simp
      linarith
    apply step.trans
    apply (div_le_div_iff₀ ap up).mpr
    have haR : (1:ℝ) ≤ a := by exact_mod_cast ha
    linarith
  have entry := harmonic_bracket a b ha hab
  rw [log_div vp.ne' up.ne', abs_le]
  change - (2/u) ≤ (∑ j ∈ Ioc a b, (j:ℝ)⁻¹) - _ ∧ _ ≤ _
  constructor
  · linarith [entry.1,log_le_log vp bh.le, one_div_pos.mpr up, show 2/u = 2*(1/u) by ring]
  · linarith [entry.2,log_le_log bp bl]

lemma sum_multiples (u v : ℝ) (t : ℕ) (ht : 0 < t) (f : ℕ → ℝ) :
    (∑ m ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, if t ∣ m then f m else 0) =
    ∑ j ∈ Ioc ⌊u/(t:ℝ)⌋₊ ⌊v/(t:ℝ)⌋₊, f (j*t) := by
  rw [← sum_filter, Nat.floor_div_natCast, Nat.floor_div_natCast]
  symm
  apply sum_bij (fun j _ => j*t)
  · intro j hj
    obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hj
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul ht).mp hlo,
      (Nat.le_div_iff_mul_le ht).mp hhi⟩, dvd_mul_left t j⟩
  · intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_right ht h
  · intro m hm
    obtain ⟨hm,hd⟩ := mem_filter.mp hm
    obtain ⟨lo,hi⟩ := mem_Ioc.mp hm
    have hrec :=  Nat.div_mul_cancel hd
    refine ⟨m/t, mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul ht).mpr (by rwa [hrec]), Nat.div_le_div_right hi⟩, hrec⟩
  · intros; rfl

theorem multiples_error (u v : ℝ) (t : ℕ) (ht : 0 < t) (htu : (t:ℝ) ≤ u) (huv : u ≤ v) :
    |(∑ m ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, if t ∣ m then (m:ℝ)⁻¹ else 0) - log (v/u)/t| ≤ 2/u := by
  have tp : (0:ℝ) < t := by exact_mod_cast ht
  have up := tp.trans_le htu
  have vp := up.trans_le huv
  have base := harmonic_floor_error (u/t) (v/t) ((one_le_div tp).mpr htu) (by gcongr)
  have ratio : (v/(t:ℝ))/(u/t) = v/u := by field_simp
  rw [ratio] at base
  rw [sum_multiples _ _ t ht]
  simp only [Nat.cast_mul, mul_inv_rev, ← mul_sum]
  rw [div_eq_inv_mul (log (v/u)) (t:ℝ), ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr tp)]
  calc _ ≤ (t:ℝ)⁻¹*(2/(u/t)) := mul_le_mul_of_nonneg_left base (by positivity)
       _ = _ := by field_simp

end FactorialRounding
namespace FactorialSieve
open Finset Real

/-- The number of positive multiples of m in (n,n+h]. -/
def multiplicity (n h m : ℕ) : ℕ := (n+h)/m-n/m

/-- The centered fractional part of x/m for natural inputs and positive m. -/
def saw (x m : ℕ) : ℝ := (x%m : ℕ)/ (m : ℝ) - 1/2

/-- The sawtooth sum with moduli divisible by t in the multiplicative block. -/
def remainder (u v : ℝ) (x t : ℕ) : ℝ :=
  ∑ m ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, if t ∣ m then saw x m else 0

def weightedRemainder (z : ℕ) (u v : ℝ) (x : ℕ) : ℝ :=
  ∑ d ∈ level z, ∑ e ∈ level z, weight z d * weight z e * remainder u v x (d.lcm e)

private lemma quotient_real (x m : ℕ) (hm : 0 < m) :
    ((x/m : ℕ):ℝ) = (x:ℝ)/m - saw x m - 1/2 := by
  have exactR : (m:ℝ)*((x/m : ℕ):ℝ)+(x%m:ℕ) = x := by exact_mod_cast Nat.div_add_mod x m
  have hp : (0:ℝ) < m := by exact_mod_cast hm
  unfold saw
  field_simp
  linarith

private lemma split_count (n h m : ℕ) (hm : 0 < m) :
    (multiplicity n h m : ℝ) = h*(m:ℝ)⁻¹ + saw n m - saw (n+h) m := by
  rw [multiplicity, Nat.cast_sub (Nat.div_le_div_right (Nat.le_add_right n h)),
    quotient_real _ _ hm, quotient_real _ _ hm, Nat.cast_add]
  ring

/-- The factorial-window form of the finite Selberg block bound. The oscillating
remainder is kept signed. The elementary endpoint error has the explicit
constant 2 and holds for arbitrary real endpoints u,v. -/
theorem short_interval_block (n h z : ℕ) (u v : ℝ) (hz : 1 ≤ z) (hzu : (z:ℝ)^2 ≤ u) (huv : u ≤ v) :
    (∑ p ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime, (multiplicity n h p:ℝ)) ≤
    (h:ℝ)*log (v/u)/log ((z:ℝ)+1) + 2*h*(z:ℝ)^2/u +
      (weightedRemainder z u v n - weightedRemainder z u v (n+h)) := by
  let S := Ioc ⌊u⌋₊ ⌊v⌋₊
  let L := log (v/u)
  let C := (h:ℝ)*(2/u)
  let H (t : ℕ) := ∑ m ∈ S, if t ∣ m then (m:ℝ)⁻¹ else 0
  let W (d e : ℕ) := weight z d * weight z e
  have zr : (1:ℝ) ≤ z := by exact_mod_cast hz
  have zu : (z:ℝ) ≤ u := by nlinarith [sq_nonneg ((z:ℝ)-1)]
  have up : 0 < u := by linarith
  have lpos : 0 ≤ L := log_nonneg ((one_le_div up).mpr huv)
  have sieve := FiniteWindowSieve.prime_block S (level z) (fun m => (multiplicity n h m : ℝ))
    (weight z) z (fun _ _ => Nat.cast_nonneg _) (mem_level.mpr ⟨⟨le_rfl,hz⟩,squarefree_one⟩)
    (weight_one hz) (fun d hd => (mem_level.mp hd).1.2) (fun m hm =>
      (Nat.le_floor zu).trans_lt (mem_Ioc.mp hm).1)
  have split_row (t : ℕ) :
      (∑ m ∈ S, if t ∣ m then (multiplicity n h m : ℝ) else 0) =
      (h:ℝ)*H t + remainder u v n t - remainder u v (n+h) t := by
    simp only [H, remainder, ← sum_sub_distrib, ← sum_add_distrib, mul_sum, S]
    apply sum_congr rfl
    intro m hm
    by_cases hd : t ∣ m
    · simp only [if_pos hd]
      apply split_count
      have := (mem_Ioc.mp hm).1
      omega
    · simp [hd]
  have pair (d : ℕ) (hd : d ∈ level z) (e : ℕ) (he : e ∈ level z) :
      W d e*(∑ m ∈ S, if d.lcm e ∣ m then (multiplicity n h m:ℝ) else 0) ≤
      (h:ℝ)*L*(W d e/(d.lcm e : ℝ)) + C +
        (W d e*remainder u v n (d.lcm e) - W d e*remainder u v (n+h) (d.lcm e)) := by
    let t := d.lcm e
    have tp : 0 < t := Nat.lcm_pos (mem_level.mp hd).1.1 (mem_level.mp he).1.1
    have tl : t ≤ z^2 := by
      calc t ≤ d*e := Nat.le_of_dvd (Nat.mul_pos (mem_level.mp hd).1.1 (mem_level.mp he).1.1)
                         (Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _))
           _ ≤ _ := by rw [sq]; exact Nat.mul_le_mul (mem_level.mp hd).1.2 (mem_level.mp he).1.2
    have htu : (t:ℝ) ≤ u := (by exact_mod_cast tl : (t:ℝ) ≤ (z:ℝ)^2).trans hzu
    have herr := FactorialRounding.multiples_error u v t tp htu huv
    change |H t-L/t| ≤ 2/u at herr
    have wh : |W d e| ≤ 1 := by
      change |weight z d * weight z e| ≤ 1
      rw [abs_mul]
      simpa using mul_le_mul (weight_abs_le_one hz hd) (weight_abs_le_one hz he) (abs_nonneg _) zero_le_one
    have scaled : W d e*((h:ℝ)*(H t - L/t)) ≤ C := by
      apply (le_abs_self _).trans
      have ah : |(h:ℝ)| = (h:ℝ) := abs_of_nonneg (Nat.cast_nonneg h)
      rw [abs_mul (W d e) _,abs_mul (h:ℝ) _,ah]
      calc _ ≤ 1*((h:ℝ)*(2/u)) := mul_le_mul wh (mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg h))
                                      (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)) zero_le_one
           _ = _ := one_mul _
    rw [split_row]
    change W d e*((h:ℝ)*H t + remainder u v n t - remainder u v (n+h) t) ≤ _
    dsimp only [t] at scaled ⊢
    simp only [div_eq_mul_inv] at scaled ⊢
    linear_combination scaled
  have total := (sum_le_sum (fun d hd => sum_le_sum (fun e he => pair d hd e he)))
  have mainBound := main_term_bound hz
  have cardBound : (level z).card ≤ z := by
    simpa [level] using Finset.card_le_card (filter_subset Squarefree (Icc 1 z))
  have cardR : ((level z).card : ℝ) ≤ z := by exact_mod_cast cardBound
  have Cr : 0 ≤ C := mul_nonneg (Nat.cast_nonneg h) (by positivity)
  have constant : ((level z).card : ℝ)*((level z).card*C) ≤ 2*h*(z:ℝ)^2/u := by
    calc _ ≤ (z:ℝ)*(z*C) := by gcongr
         _ = _ := by dsimp [C]; ring
  have mainB := mul_le_mul_of_nonneg_left mainBound (mul_nonneg (Nat.cast_nonneg h) lpos)
  dsimp only [weightedRemainder]
  apply sieve.trans
  calc
    _ ≤ _ := total
    _ = ((h:ℝ)*L)*(∑ d ∈ level z, ∑ e ∈ level z, W d e/(d.lcm e : ℝ)) +
        ((level z).card : ℝ)*((level z).card*C) +
        ((∑ d ∈ level z, ∑ e ∈ level z, W d e*remainder u v n (d.lcm e)) -
        (∑ d ∈ level z, ∑ e ∈ level z, W d e*remainder u v (n+h) (d.lcm e))) := by
      simp only [sum_add_distrib, sum_sub_distrib, mul_sum, sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      change _ ≤ (h:ℝ)*L/log ((z:ℝ)+1) + _ + _
      rw [div_eq_mul_inv]
      exact add_le_add (add_le_add mainB constant) le_rfl




private lemma decreasing_power_sum (N : ℕ) (hN : 1 ≤ N) (e : ℝ) (he : e ≤ 0) (hne : e ≠ -1) :
    (∑ n ∈ Icc 1 N, (n:ℝ)^e) ≤ 1 + ((N:ℝ)^(e+1)-1)/(e+1) := by
  have NR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have ant : AntitoneOn (fun x : ℝ => x^e) (Set.Icc 1 (N:ℝ)) :=
    fun x hx y _ hxy => Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy he
  have bound := AntitoneOn.sum_le_integral_Ico (f := fun x : ℝ => x^e) hN (by simpa using ant)
  simp only [Nat.cast_one] at bound
  have miss : (0:ℝ) ∉ Set.uIcc 1 (N:ℝ) := by simp [Set.uIcc_of_le NR]
  rw [integral_rpow (Or.inr ⟨hne,miss⟩), Real.one_rpow] at bound
  have shift : (∑ n ∈ Ioc 1 N, (n:ℝ)^e) =
      ∑ i ∈ Ico 1 N, ((i+1 : ℕ):ℝ)^e := by
    symm
    apply sum_bij (fun i _ => i+1)
    · intro i hi
      obtain ⟨hl,hu⟩ := mem_Ico.mp hi
      exact mem_Ioc.mpr ⟨by omega, by omega⟩
    · intros; omega
    · intro n hn
      obtain ⟨hl,hu⟩ := mem_Ioc.mp hn
      exact ⟨n-1,mem_Ico.mpr ⟨by omega,by omega⟩,by omega⟩
    · intros; rfl
  have seteq : Icc 1 N = insert 1 (Ioc 1 N) := by ext i; simp; omega
  rw [seteq,sum_insert (by simp),shift,Nat.cast_one,Real.one_rpow]
  exact add_le_add le_rfl bound

private lemma quotient_box (z : ℕ) (s : ℝ) :
    (∑ d ∈ level z, ∑ e ∈ level z, (d.lcm e : ℝ)^(-s)) ≤
    ∑ g ∈ Icc 1 z, (g:ℝ)^(-s)*(∑ a ∈ Icc 1 (z/g), (a:ℝ)^(-s))^2 := by
  let P := (level z) ×ˢ (level z)
  let g (x : ℕ × ℕ) := x.1.gcd x.2
  let h (x : ℕ × ℕ) := (x.1/g x,x.2/g x)
  let w (a : ℕ) := (a:ℝ)^(-s)
  have nonneg (a : ℕ) : 0 ≤ w a := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have gmem (x : ℕ × ℕ) (hx : x ∈ P) : g x ∈ Icc 1 z := by
    have hd := (mem_level.mp (mem_product.mp hx).1).1
    exact mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_left _ hd.1, (Nat.le_of_dvd hd.1 (Nat.gcd_dvd_left _ _)).trans hd.2⟩
  have result (t : ℕ) (ht : t ∈ Icc 1 z) :
      (∑ x ∈ P.filter (fun x => g x = t), w (x.1.lcm x.2)) ≤ w t*(∑ a ∈ Icc 1 (z/t), w a)^2 := by
    let F := P.filter (fun x => g x=t)
    let I := Icc 1 (z/t)
    have tp := (mem_Icc.mp ht).1
    have info (x : ℕ × ℕ) (hx : x ∈ F) :
        (h x).1*t=x.1 ∧ (h x).2*t=x.2 ∧ h x ∈ I ×ˢ I ∧ x.1.lcm x.2=t*(h x).1*(h x).2 := by
      obtain ⟨hp,heq⟩ := mem_filter.mp hx
      have d := (mem_level.mp (mem_product.mp hp).1).1
      have e := (mem_level.mp (mem_product.mp hp).2).1
      have t1 : t ∣ x.1 := heq ▸ Nat.gcd_dvd_left x.1 x.2
      have t2 : t ∣ x.2 := heq ▸ Nat.gcd_dvd_right x.1 x.2
      have r1 : (h x).1*t=x.1 := by dsimp [h]; rw [heq,Nat.div_mul_cancel t1]
      have r2 : (h x).2*t=x.2 := by dsimp [h]; rw [heq,Nat.div_mul_cancel t2]
      have hp1 : 1 ≤ (h x).1 := by
        change 1 ≤ x.1 / g x
        rw [heq]
        exact Nat.div_pos (Nat.le_of_dvd d.1 t1) tp
      have hp2 : 1 ≤ (h x).2 := by
        change 1 ≤ x.2 / g x
        rw [heq]
        exact Nat.div_pos (Nat.le_of_dvd e.1 t2) tp
      refine ⟨r1,r2,mem_product.mpr ⟨mem_Icc.mpr ⟨hp1,(Nat.le_div_iff_mul_le tp).mpr (r1.trans_le d.2)⟩,
        mem_Icc.mpr ⟨hp2,(Nat.le_div_iff_mul_le tp).mpr (r2.trans_le e.2)⟩⟩,?_⟩
      apply Nat.eq_of_mul_eq_mul_right tp
      calc x.1.lcm x.2 * t = x.1*x.2 := by rw [← heq,mul_comm]; exact Nat.gcd_mul_lcm _ _
           _ = _ := by nth_rw 1 [← r1,← r2]; ring
    have inj : Set.InjOn h F := by
      intro x hx y hy eq
      obtain ⟨a,b,_,_⟩ := info x hx
      obtain ⟨c,d,_,_⟩ := info y hy
      exact Prod.ext (a.symm.trans (by rw [eq,c])) (b.symm.trans (by rw [eq,d]))
    have sub : F.image h ⊆ I ×ˢ I := by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
      exact (info x hx).2.2.1
    let wpair (y : ℕ × ℕ) := w t*w y.1*w y.2
    calc
      _ = ∑ x ∈ F, wpair (h x) := by
        apply sum_congr rfl
        intro x hx
        rw [(info x hx).2.2.2]
        simp only [wpair,w,Nat.cast_mul]
        rw [Real.mul_rpow (by positivity) (by positivity),Real.mul_rpow (Nat.cast_nonneg t) (by positivity)]
      _ = ∑ y ∈ F.image h, wpair y := (sum_image (f := wpair) inj).symm
      _ ≤ ∑ y ∈ I ×ˢ I, wpair y := sum_le_sum_of_subset_of_nonneg sub (fun y _ _ =>
        mul_nonneg (mul_nonneg (nonneg _) (nonneg _)) (nonneg _))
      _ = _ := by simp only [sum_product,wpair, I, sq,← mul_sum,← sum_mul]; ring
  have sums := sum_le_sum result
  rw [sum_fiberwise_of_maps_to gmem] at sums
  simpa only [P,sum_product,w] using sums

/-- With both input divisors at most z, the positive fractional moment has
no logarithmic loss for any fixed 0 ≤ s < 1. -/
theorem lcm_fractional_moment {z : ℕ} (hz : 1 ≤ z) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∑ d ∈ level z, ∑ e ∈ level z, (d.lcm e : ℝ)^(-s)) ≤
    ((1+1/(1-s))/(1-s)^2)*(z:ℝ)^(2*(1-s)) := by
  let r := 1-s
  have rp : 0 < r := sub_pos.mpr hs1
  have zr : (0:ℝ) < z := by exact_mod_cast hz
  let C := (z:ℝ)^(2*r)/r^2
  have Cp : 0 ≤ C := by dsimp [C]; positivity
  have row (g : ℕ) (hg : g ∈ Icc 1 z) :
      (g:ℝ)^(-s)*(∑ a ∈ Icc 1 (z/g), (a:ℝ)^(-s))^2 ≤ C*(g:ℝ)^(s-2) := by
    obtain ⟨gp,gz⟩ := mem_Icc.mp hg
    have gpR : (0:ℝ) < g := by exact_mod_cast gp
    have q1 : 1 ≤ z/g := (Nat.le_div_iff_mul_le gp).mpr (by simpa using gz)
    have hh := decreasing_power_sum (z/g) q1 (-s) (by linarith) (by linarith)
    rw [show -s+1=r by dsimp [r]; ring] at hh
    have cap : (∑ a ∈ Icc 1 (z/g), (a:ℝ)^(-s)) ≤ ((z:ℝ)/g)^r/r := by
      apply hh.trans
      have cmp := Real.rpow_le_rpow (Nat.cast_nonneg (z/g))
        (Nat.cast_div_le : ((z/g : ℕ):ℝ) ≤ (z:ℝ)/g) rp.le
      apply (le_div_iff₀ rp).mpr
      rw [add_mul, div_mul_cancel₀ _ rp.ne']
      dsimp [r] at *
      linarith
    have nneg : 0 ≤ ∑ a ∈ Icc 1 (z/g), (a:ℝ)^(-s) := sum_nonneg (by intros; positivity)
    calc _ ≤ (g:ℝ)^(-s)*(((z:ℝ)/g)^r/r)^2 :=
               mul_le_mul_of_nonneg_left (pow_le_pow_left₀ nneg cap _) (by positivity)
         _ = _ := by
           dsimp only [C]
           rw [Real.div_rpow zr.le gpR.le,div_pow,div_pow,← Real.rpow_mul_natCast zr.le,
               ← Real.rpow_mul_natCast gpR.le]
           have eq : (g:ℝ)^(-s) = (g:ℝ)^(s-2)*(g:ℝ)^(r*(2:ℕ)) := by
             rw [← Real.rpow_add gpR]
             congr 1
             dsimp [r]
             ring
           rw [eq,show r*(2:ℕ) = 2*r by norm_num; ring]
           field_simp
  have tail : (∑ g ∈ Icc 1 z, (g:ℝ)^(s-2)) ≤ 1+1/r := by
    have h := decreasing_power_sum z hz (s-2) (by linarith) (by linarith)
    rw [show s-2+1 = -r by dsimp [r]; ring] at h
    apply h.trans
    have np := Real.rpow_nonneg zr.le (-r)
    have hterm : ((z:ℝ)^(-r)-1)/(-r) = (1-(z:ℝ)^(-r))/r := by ring
    rw [hterm]
    gcongr
    linarith
  calc
    _ ≤ _ := quotient_box z s
    _ ≤ ∑ g ∈ Icc 1 z, C*(g:ℝ)^(s-2) := sum_le_sum row
    _ = C*(∑ g ∈ Icc 1 z, (g:ℝ)^(s-2)) := (mul_sum ..).symm
    _ ≤ C*(1+1/r) := mul_le_mul_of_nonneg_left tail Cp
    _ = _ := by dsimp [C,r]; ring


/-- The endpoint s=1 has at most three harmonic factors. -/
theorem reciprocal_lcm_sum (z : ℕ) :
    (∑ d ∈ level z, ∑ e ∈ level z, ((d.lcm e : ℝ)⁻¹)) ≤ (harmonic z : ℝ)^3 := by
  have box := quotient_box z 1
  simp only [Real.rpow_neg_one] at box
  apply box.trans
  have harm (N : ℕ) : (∑ j ∈ Icc 1 N, (j:ℝ)⁻¹) = (harmonic N : ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  calc
    _ ≤ ∑ g ∈ Icc 1 z, (g:ℝ)⁻¹*(harmonic z : ℝ)^2 := by
      apply sum_le_sum; intro g _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply pow_le_pow_left₀ (sum_nonneg (by intros; positivity)) _ 2
      rw [← harm]
      exact sum_le_sum_of_subset_of_nonneg (fun a ha =>
        mem_Icc.mpr ⟨(mem_Icc.mp ha).1,(mem_Icc.mp ha).2.trans (Nat.div_le_self _ _)⟩) (by intros; positivity)
    _ = _ := by rw [← sum_mul,harm]; ring

/-- Pass from a single-modulus exponent-pair bound to the whole signed
sieve remainder. The fractional-power term has no logarithmic loss. -/
theorem remainder_bound {z x : ℕ} (u v A B s : ℝ) (hz : 1 ≤ z)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (local_bound : ∀ t : ℕ, 1 ≤ t → t ≤ z^2 →
      |remainder u v x t| ≤ A*(t:ℝ)^(-s) + B/t) :
    |weightedRemainder z u v x| ≤
    A*(((1+1/(1-s))/(1-s)^2)*(z:ℝ)^(2*(1-s))) + B*(1+log z)^3 := by
  have entry (d e : ℕ) (hd : d ∈ level z) (he : e ∈ level z) :
      |weight z d*weight z e*remainder u v x (d.lcm e)| ≤
      A*(d.lcm e : ℝ)^(-s) + B*(d.lcm e : ℝ)⁻¹ := by
    have tp := Nat.lcm_pos (mem_level.mp hd).1.1 (mem_level.mp he).1.1
    have th : d.lcm e ≤ z^2 := by
      calc _ ≤ d*e := Nat.le_of_dvd (Nat.mul_pos (mem_level.mp hd).1.1 (mem_level.mp he).1.1)
                          (Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _))
           _ ≤ _ := by rw [sq]; exact Nat.mul_le_mul (mem_level.mp hd).1.2 (mem_level.mp he).1.2
    have wt : |weight z d*weight z e| ≤ 1 := by
      rw [abs_mul]
      simpa using mul_le_mul (weight_abs_le_one hz hd) (weight_abs_le_one hz he) (abs_nonneg _) zero_le_one
    rw [abs_mul]
    apply (mul_le_mul_of_nonneg_right wt (abs_nonneg _)).trans
    simpa only [one_mul,div_eq_mul_inv] using local_bound _ tp th
  have hh : (0:ℝ) ≤ harmonic z := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    exact sum_nonneg (by intros; positivity)
  calc
    _ ≤ ∑ d ∈ level z, |∑ e ∈ level z, weight z d*weight z e*remainder u v x (d.lcm e)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ level z, ∑ e ∈ level z, (A*(d.lcm e : ℝ)^(-s) + B*(d.lcm e : ℝ)⁻¹) := by
      apply sum_le_sum; intro d hd
      exact (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun e he => entry d e hd he))
    _ = A*(∑ d ∈ level z, ∑ e ∈ level z, (d.lcm e : ℝ)^(-s)) +
        B*(∑ d ∈ level z, ∑ e ∈ level z, (d.lcm e : ℝ)⁻¹) := by simp only [sum_add_distrib,mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (lcm_fractional_moment hz s hs0 hs1) hA)
      (mul_le_mul_of_nonneg_left ((reciprocal_lcm_sum z).trans
        (pow_le_pow_left₀ hh (harmonic_le_one_add_log z) 3)) hB)

/-- The complete block inequality conditional only on the two endpoint
sawtooth estimates for individual moduli. -/
theorem short_interval_from_local (n h z : ℕ) (u v A B s : ℝ) (hz : 1 ≤ z) (hzu : (z:ℝ)^2 ≤ u)
    (huv : u ≤ v) (hA : 0 ≤ A) (hB : 0 ≤ B) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (bounds : ∀ x ∈ ({n,n+h} : Finset ℕ), ∀ t : ℕ, 1 ≤ t → t ≤ z^2 →
      |remainder u v x t| ≤ A*(t:ℝ)^(-s) + B/t) :
    (∑ p ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime, (multiplicity n h p:ℝ)) ≤
    (h:ℝ)*log (v/u)/log ((z:ℝ)+1) + 2*h*(z:ℝ)^2/u +
      2*(A*(((1+1/(1-s))/(1-s)^2)*(z:ℝ)^(2*(1-s))) + B*(1+log z)^3) := by
  apply (short_interval_block n h z u v hz hzu huv).trans
  apply add_le_add le_rfl
  have lo := (abs_le.mp (remainder_bound u v A B s hz hA hB hs0 hs1 (bounds n (by simp)))).2
  have hi := (abs_le.mp (remainder_bound u v A B s hz hA hB hs0 hs1 (bounds (n+h) (by simp)))).1
  linarith

end FactorialSieve
#print axioms FactorialSieve.short_interval_block
#print axioms FactorialSieve.lcm_fractional_moment
#print axioms FactorialSieve.short_interval_from_local

import ReciprocalLowerBandInput

/-! Fixed rational sieve levels for the two lower exponent-pair ranges.
A level below the critical value leaves strict power savings in the error
terms and an arbitrarily small fixed loss in the prime-count coefficient. -/
noncomputable section
open Real Filter Finset
namespace FactorialLowerBands
open ReciprocalBandRates

private lemma admissible_level {X g a : ℝ} (hX : 1≤X) (hg : 0<g) (hga : 2*g≤a) :
    1≤⌊X^g⌋₊ ∧ ((⌊X^g⌋₊:ℕ):ℝ)^2 ≤ X^a := by
  have xp := zero_lt_one.trans_le hX
  refine ⟨Nat.floor_pos.mpr (Real.one_le_rpow hX hg.le),?_⟩
  calc _ ≤ (X^g)^2 := pow_le_pow_left₀ (by positivity) (Nat.floor_le (by positivity)) _
       _ = X^(2*g) := by rw [← Real.rpow_mul_natCast xp.le]; congr 1; ring
       _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hX hga

private lemma log_level {X g a b : ℝ} (hX : 1<X) (hg : 0<g) (hab : a≤b) :
    log (X^b/X^a)/log ((⌊X^g⌋₊:ℝ)+1) ≤ (b-a)/g := by
  have xp := zero_lt_one.trans hX
  have lx := Real.log_pos hX
  have lg := Real.log_le_log (Real.rpow_pos_of_pos xp g) (Nat.lt_floor_add_one (X^g)).le
  rw [Real.log_rpow xp] at lg
  have lp := (mul_pos hg lx).trans_le lg
  rw [Real.log_div (Real.rpow_pos_of_pos xp _).ne' (Real.rpow_pos_of_pos xp _).ne',
    Real.log_rpow xp,Real.log_rpow xp,div_le_div_iff₀ lp hg]
  nlinarith only [mul_le_mul_of_nonneg_left lg (sub_nonneg.mpr hab)]

/-- In the whole lower range the normalized sieve errors are dominated by three powers
of X, all with at most four logarithms. -/
theorem error_envelope (n : ℕ) (hn : 2≤n) {g a b p q s C : ℝ} (hg : 0<g)
    (hgu : g≤1) (ha : 0≤a) (hab : a≤b) (hb : b≤1) (hga : 2*g≤a)
    (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hs : s<1) (hC : 1≤C) :
    let X : ℝ := n
    let h : ℝ := ⌊X^c⌋₊
    let z : ℝ := ⌊X^g⌋₊
    let u := X^a
    let v := X^b
    4*h*z^2/u + C*(1+log (v/u)/log 2)*(X+h)^p*v^q*z^(2*(1-s)) +
      C*(v^2/X)*(1+log z)^3 ≤
      4*C*(1+log X)^4*(X^(c+2*g-a)+X^(p+b*q+g*(2*(1-s)))+X^(2*b-1)) := by
  let X : ℝ := n
  let h : ℝ := ⌊X^c⌋₊
  let z : ℝ := ⌊X^g⌋₊
  let u := X^a
  let v := X^b
  let T := 1+log X
  let E₁ := X^(c+2*g-a)
  let E₂ := X^(p+b*q+g*(2*(1-s)))
  let E₃ := X^(2*b-1)
  let r := 2*(1-s)
  change 4*h*z^2/u+C*(1+log (v/u)/log 2)*(X+h)^p*v^q*z^r+C*(v^2/X)*(1+log z)^3 ≤
    4*C*T^4*(E₁+E₂+E₃)
  have x1 : 1≤X := by dsimp [X]; exact_mod_cast (show 1≤n by omega)
  have xp := zero_lt_one.trans_le x1
  have cp : 0≤C := by linarith
  have gr : 0≤r := by dsimp [r]; linarith
  have up := Real.rpow_pos_of_pos xp a
  have vp := Real.rpow_pos_of_pos xp b
  have lx := Real.log_nonneg x1
  have t1 : 1≤T := by dsimp [T]; linarith
  have t0 := zero_le_one.trans t1
  have z1 : 1≤z := by dsimp [z]; exact_mod_cast (admissible_level x1 hg hga).1
  have zp := zero_lt_one.trans_le z1
  have hc : h ≤ X^c := Nat.floor_le (by positivity)
  have hz : z ≤ X^g := Nat.floor_le (by positivity)
  have h0 : 0≤h := Nat.cast_nonneg _
  have hx : h≤X := hc.trans (by simpa using Real.rpow_le_rpow_of_exponent_le x1 (show c≤1 by norm_num [c]))
  have zx : z≤X := hz.trans (by simpa using Real.rpow_le_rpow_of_exponent_le x1 hgu)
  have e1 : 0≤E₁ := Real.rpow_nonneg xp.le _
  have e2 : 0≤E₂ := Real.rpow_nonneg xp.le _
  have e3 : 0≤E₃ := Real.rpow_nonneg xp.le _
  have first : 4*h*z^2/u ≤ 4*E₁ := by
    calc _ ≤ 4*X^c*(X^g)^2/u := by gcongr
         _ = _ := by dsimp [E₁,u]; rw [← Real.rpow_mul_natCast xp.le,Real.rpow_sub xp,Real.rpow_add xp]; ring_nf
  have count : 1+log (v/u)/log 2 ≤ 2*T := by
    have l : log (v/u) = (b-a)*log X := by
      dsimp [u,v]; rw [Real.log_div vp.ne' up.ne',Real.log_rpow xp,Real.log_rpow xp]; ring
    have l2 : 1/2 ≤ log (2:ℝ) := by
      have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : 0<(2:ℝ))
      norm_num at hh ⊢
      exact hh
    have width : b-a ≤ 1 := by linarith
    have d : log (v/u)/log 2 ≤ 2*log X := by
      apply (div_le_iff₀ (by linarith : 0<log (2:ℝ))).mpr; rw [l]
      nlinarith [mul_le_mul_of_nonneg_right width lx,mul_le_mul_of_nonneg_left l2 lx]
    dsimp [T]; linarith
  have root : (X+h)^p ≤ 2*X^p := by
    calc _ ≤ (2*X)^p := Real.rpow_le_rpow (by positivity) (by linarith) hp
         _ = (2:ℝ)^p*X^p := Real.mul_rpow (by norm_num) xp.le
         _ ≤ _ := mul_le_mul_of_nonneg_right (by
           simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hp1) (by positivity)
  have poly : (X+h)^p*v^q*z^r ≤ 2*E₂ := by
    calc _ ≤ (2*X^p)*v^q*(X^g)^r := mul_le_mul
           (mul_le_mul_of_nonneg_right root (Real.rpow_nonneg vp.le _))
           (Real.rpow_le_rpow zp.le hz gr) (Real.rpow_nonneg zp.le _) (by positivity)
         _ = _ := by
           dsimp [v,E₂,r]
           rw [← Real.rpow_mul xp.le,← Real.rpow_mul xp.le,Real.rpow_add xp,Real.rpow_add xp]
           ring
  have mid : C*(1+log (v/u)/log 2)*(X+h)^p*v^q*z^r ≤ 4*C*T*E₂ := by
    have hcmp := mul_le_mul count poly (by positivity) (by positivity)
    have sc := mul_le_mul_of_nonneg_left hcmp cp
    linarith only [show C*((1+log (v/u)/log 2)*((X+h)^p*v^q*z^r))=
      C*(1+log (v/u)/log 2)*(X+h)^p*v^q*z^r by ring,sc,
      show C*(2*T*(2*E₂))=4*C*T*E₂ by ring]
  have scale : v^2/X = E₃ := by
    dsimp [E₃,v]; rw [Real.rpow_sub xp,Real.rpow_one,← Real.rpow_mul_natCast xp.le]; congr 2; ring
  have zlog : (1+log z)^3 ≤ T^3 :=
    pow_le_pow_left₀ (by linarith [Real.log_nonneg z1]) (add_le_add le_rfl (Real.log_le_log zp zx)) _
  have last : C*(v^2/X)*(1+log z)^3 ≤ C*T^3*E₃ := by
    rw [scale]
    exact (mul_le_mul_of_nonneg_left zlog (mul_nonneg cp e3)).trans_eq (by ring)
  have L1 : 1≤T^4 := one_le_pow₀ t1
  have L2 : T≤T^4 := by simpa using pow_le_pow_right₀ t1 (by decide : 1≤4)
  have L3 : T^3≤T^4 := pow_le_pow_right₀ t1 (by decide)
  have b1 : 4*E₁ ≤ 4*C*T^4*E₁ := by
    apply mul_le_mul_of_nonneg_right _ e1
    nlinarith [mul_le_mul_of_nonneg_left L1 cp]
  have b2 : 4*C*T*E₂ ≤ 4*C*T^4*E₂ := by gcongr
  have b3 : C*T^3*E₃ ≤ 4*C*T^4*E₃ := by
    apply mul_le_mul_of_nonneg_right _ e3
    nlinarith [mul_le_mul_of_nonneg_left L3 cp, mul_nonneg cp (show 0≤T^4 by positivity)]
  linarith only [first,mid,last,b1,b2,b3, show 4*C*T^4*(E₁+E₂+E₃) =
    4*C*T^4*E₁+4*C*T^4*E₂+4*C*T^4*E₃ by ring]

/-- A strict exponent saving in all three errors and positive allowance
above the fixed-level main term give the required eventual band count. -/
theorem prime_hits_of_band_bound (a b g p q s L : ℝ) (bb : BandBound p q s) (hg : 0<g)
    (hgu : g≤1) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (hp : 0≤p) (hp1 : p≤1) (hq : 0≤q) (hs : s<1)
    (gap₁ : 2*g<a) (gap₂ : p+b*q+g*(2*(1-s))<c) (gap₃ : 2*b-1<c)
    (margin : (b-a)/g<L) :
    ∀ᶠ n : ℕ in atTop,
      FactorialUpperBands.primeHits n ⌊(n:ℝ)^c⌋₊ ((n:ℝ)^a) ((n:ℝ)^b) ≤ L*window n := by
  obtain ⟨C,hC,estim⟩ := bb
  have cp : 0<C := by linarith
  have cpos : 0<c := by norm_num [c]
  let e := (L-(b-a)/g)/(12*C)
  have ep : 0<e := div_pos (sub_pos.mpr margin) (by positivity)
  have coeff : 12*C*e = L-(b-a)/g := by dsimp only [e]; field_simp
  filter_upwards [eventually_ge_atTop (2:ℕ),power_rate (show c+2*g-a<c by linarith) cpos ep,
    power_rate gap₂ cpos ep,power_rate gap₃ cpos ep] with n hn r₁ r₂ r₃
  let X := (n:ℝ)
  let h := ⌊X^c⌋₊
  let z := ⌊X^g⌋₊
  let u := X^a
  let v := X^b
  let T := (1+log X)^4
  let E₁ := X^(c+2*g-a)
  let E₂ := X^(p+b*q+g*(2*(1-s)))
  let E₃ := X^(2*b-1)
  have x1 : 1<X := by dsimp [X]; exact_mod_cast (show 1<n by omega)
  have hnon : 0 ≤ (h:ℝ) := Nat.cast_nonneg _
  have zu := admissible_level x1.le hg gap₁.le
  have uv := Real.rpow_le_rpow_of_exponent_le x1.le hab
  have cnt := estim n h z u v (by omega) zu.1 zu.2 uv
  have main := mul_le_mul_of_nonneg_left (log_level x1 hg hab) hnon
  rw [← mul_div_assoc] at main
  have env := error_envelope n hn hg hgu ha hab hb gap₁.le hp hp1 hq hs hC
  change 4*h*(z:ℝ)^2/u+C*(1+log (v/u)/log 2)*(X+h)^p*v^q*(z:ℝ)^(2*(1-s))+
    C*(v^2/X)*(1+log z)^3 ≤ 4*C*T*(E₁+E₂+E₃) at env
  change (h:ℝ)*log (v/u)/log ((z:ℝ)+1) ≤ (h:ℝ)*((b-a)/g) at main
  change T*E₁ ≤ e*(h:ℝ) at r₁
  change T*E₂ ≤ e*(h:ℝ) at r₂
  change T*E₃ ≤ e*(h:ℝ) at r₃
  have sum : T*(E₁+E₂+E₃) ≤ 3*e*(h:ℝ) := by
    rw [mul_add,mul_add]; linarith only [r₁,r₂,r₃]
  have tot : 4*C*T*(E₁+E₂+E₃) ≤ (L-(b-a)/g)*(h:ℝ) := by
    calc _ = (4*C)*(T*(E₁+E₂+E₃)) := by ring
         _ ≤ (4*C)*(3*e*(h:ℝ)) := mul_le_mul_of_nonneg_left sum (by positivity)
         _ = _ := by rw [← coeff]; ring
  change FactorialUpperBands.primeHits n h u v ≤ L*(h:ℝ)
  change FactorialUpperBands.primeHits n h u v ≤ (h:ℝ)*log (v/u)/log ((z:ℝ)+1)+
    4*h*(z:ℝ)^2/u+C*(1+log (v/u)/log 2)*(X+h)^p*v^q*(z:ℝ)^(2*(1-s))+
    C*(v^2/X)*(1+log z)^3 at cnt
  linarith only [cnt,main,env,tot,show (h:ℝ)*((b-a)/g)+(L-(b-a)/g)*(h:ℝ) = L*(h:ℝ) by ring]

end FactorialLowerBands
#print axioms FactorialLowerBands.error_envelope
#print axioms FactorialLowerBands.prime_hits_of_band_bound

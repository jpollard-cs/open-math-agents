import FactorialSelbergBlock
import ReciprocalFirstDerivative

/-! Reindex the exponential sums on multiples in a real interval, and
apply the reciprocal-phase square-root estimate before smoothing. -/
noncomputable section
open Finset
namespace FactorialFourier

variable {u v : ℝ} {x t j : ℕ}

private lemma sum_on_multiples {A : Type*} [AddCommMonoid A]
    (u v : ℝ) (t : ℕ) (ht : 0 < t) (f : ℕ → A) :
    (∑ m ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter (t ∣ ·), f m) =
      ∑ q ∈ Icc (⌊u/(t:ℝ)⌋₊+1) ⌊v/(t:ℝ)⌋₊, f (q*t) := by
  rw [Nat.floor_div_natCast,Nat.floor_div_natCast]
  symm
  apply sum_bij (fun q _ => q*t)
  · intro q hq
    obtain ⟨lo,hi⟩ := mem_Icc.mp hq
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul ht).mp lo,
      (Nat.le_div_iff_mul_le ht).mp hi⟩,dvd_mul_left t q⟩
  · intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_right ht h
  · intro m hm
    obtain ⟨hm,hd⟩ := mem_filter.mp hm
    obtain ⟨lo,hi⟩ := mem_Ioc.mp hm
    have h := Nat.div_mul_cancel hd
    exact ⟨m/t,mem_Icc.mpr ⟨(Nat.div_lt_iff_lt_mul ht).mpr (by rwa [h]),
      Nat.div_le_div_right hi⟩,h⟩
  · intros; rfl

/-- A factor-three interval contains at most 3u/t multiples of t. -/
theorem multiple_window_card (ht : 0 < t) (htu : (t:ℝ) ≤ u) (huv : u ≤ v) (hv : v ≤ 3*u) :
    (((Ioc ⌊u⌋₊ ⌊v⌋₊).filter (t ∣ ·)).card:ℝ) ≤ 3*u/t := by
  have tp : (0:ℝ) < t := by exact_mod_cast ht
  have up := tp.trans_le htu
  have eq := sum_on_multiples u v t ht (fun _ => (1:ℝ))
  simp only [sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc] at eq
  rw [eq]
  have cardle : ⌊v/(t:ℝ)⌋₊+1-(⌊u/(t:ℝ)⌋₊+1) ≤ ⌊v/(t:ℝ)⌋₊ := by omega
  exact (show ((⌊v/(t:ℝ)⌋₊+1-(⌊u/(t:ℝ)⌋₊+1):ℕ):ℝ) ≤ ⌊v/(t:ℝ)⌋₊ by exact_mod_cast cardle).trans
    ((Nat.floor_le (div_nonneg (up.le.trans huv) tp.le)).trans (div_le_div_of_nonneg_right hv tp.le))

/-- Trivial bound including exact integer phases, which attain magnitude 1/2. -/
theorem remainder_le_half_card (u v : ℝ) (x t : ℕ) :
    |FactorialSieve.remainder u v x t| ≤ (((Ioc ⌊u⌋₊ ⌊v⌋₊).filter (t ∣ ·)).card:ℝ)/2 := by
  rw [FactorialSieve.remainder,← sum_filter]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ _m ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter (t ∣ ·), (1:ℝ)/2 := by
      apply sum_le_sum; intro m hm
      have mp : 0 < m := lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp (mem_filter.mp hm).1).1
      have p : (0:ℝ) < m := by exact_mod_cast mp
      have cut : ((x%m:ℕ):ℝ) < m := by exact_mod_cast Nat.mod_lt x mp
      have h : ((x%m:ℕ):ℝ)/m < 1 := (div_lt_one p).mpr cut
      unfold FactorialSieve.saw
      exact abs_le.mpr ⟨by linarith [show (0:ℝ) ≤ ((x%m:ℕ):ℝ)/m by positivity],by linarith⟩
    _ = _ := by simp; ring

/-- The square-root bound on an integer reciprocal block implies the
frequency estimate on the exact prime-sieve window. -/
theorem window_exponential_of_sqrt
    (sqrt_bound : ∀ {Y : ℝ} {M a b : ℕ}, 0 < Y → 1 ≤ M → M ≤ a → b ≤ 3*M →
      ‖∑ q ∈ Icc a b, ReciprocalFirstDerivative.wave (Y/(q:ℝ))‖ ≤
        335*(Real.sqrt (Y/M)+(M:ℝ)^2/Y))
    (hx : 0 < x) (ht : 0 < t) (hj : 0 < j) (htu : (t:ℝ) ≤ u) (huv : u ≤ v)
    (hv : v ≤ 3*u) :
    ‖∑ m ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter (t ∣ ·),
      Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*x/m)‖ ≤
      335*Real.sqrt ((x:ℝ)/u)*(j:ℝ)^(1/2:ℝ) + (1340*u^2/((x:ℝ)*t))/j := by
  let M := ⌊u/(t:ℝ)⌋₊+1
  let b := ⌊v/(t:ℝ)⌋₊
  let Y := (j:ℝ)*x/t
  have tp : (0:ℝ) < t := by exact_mod_cast ht
  have xp : (0:ℝ) < x := by exact_mod_cast hx
  have jp : (0:ℝ) < j := by exact_mod_cast hj
  have up := tp.trans_le htu
  have yp : 0 < Y := by dsimp [Y]; positivity
  have mn : 1 ≤ M := Nat.succ_le_succ (Nat.zero_le _)
  have mp : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have ml : u/t ≤ (M:ℝ) := by simpa only [M,Nat.cast_add,Nat.cast_one] using (Nat.lt_floor_add_one (u/(t:ℝ))).le
  have mu : (M:ℝ) ≤ 2*(u/t) := by
    simp only [M,Nat.cast_add,Nat.cast_one]
    linarith [Nat.floor_le (div_nonneg up.le tp.le), (one_le_div tp).mpr htu]
  have b3 : b ≤ 3*M := by
    have h₁ : (b:ℝ) ≤ v/t := Nat.floor_le (div_nonneg (up.le.trans huv) tp.le)
    have h₂ : v/t ≤ 3*(u/t) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hv tp.le
    exact_mod_cast (show (b:ℝ) ≤ 3*(M:ℝ) by linarith)
  have eq (q : ℕ) :
      Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*x/((q*t:ℕ):ℂ)) =
        ReciprocalFirstDerivative.wave (Y/(q:ℝ)) := by
    unfold ReciprocalFirstDerivative.wave
    dsimp [Y]; push_cast; simp only [div_eq_mul_inv,mul_inv_rev]; ring
  rw [sum_on_multiples u v t ht]
  simp only [eq]
  apply (sqrt_bound yp mn le_rfl b3).trans
  have ratio : Y/(M:ℝ) ≤ ((x:ℝ)/u)*j := by
    apply (div_le_div_of_nonneg_left yp.le (div_pos up tp) ml).trans_eq
    dsimp [Y]; field_simp
  have hsq : Real.sqrt (Y/(M:ℝ)) ≤ Real.sqrt ((x:ℝ)/u)*(j:ℝ)^(1/2:ℝ) := by
    rw [← Real.sqrt_eq_rpow,← Real.sqrt_mul (div_nonneg xp.le up.le)]
    exact Real.sqrt_le_sqrt ratio
  have hir : (M:ℝ)^2/Y ≤ (4*u^2/((x:ℝ)*t))/j := by
    apply (div_le_div_of_nonneg_right (pow_le_pow_left₀ mp.le mu 2) yp.le).trans_eq
    dsimp [Y]; field_simp <;> ring
  calc
    _ ≤ 335*(Real.sqrt ((x:ℝ)/u)*(j:ℝ)^(1/2:ℝ)+(4*u^2/((x:ℝ)*t))/j) :=
      mul_le_mul_of_nonneg_left (add_le_add hsq hir) (by norm_num)
    _ = _ := by ring

end FactorialFourier
#print axioms FactorialFourier.remainder_le_half_card
#print axioms FactorialFourier.multiple_window_card
#print axioms FactorialFourier.window_exponential_of_sqrt

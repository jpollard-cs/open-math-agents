import ReciprocalGrid
import ReciprocalFolding
import ReciprocalFrequency
import ReciprocalSmoothing
import ReciprocalFourier

/-! A finite Fourier transfer from ordinary exponential sums to the centered
fractional parts in a Selberg sieve block. No oscillation bound is assumed
at frequency zero and the estimate has no logarithm of the denominator. -/

noncomputable section
open Finset
namespace FactorialFourier

/-- Finite Fourier transfer on a common grid with Q=H L. -/
theorem grid_transfer {ι : Type*} {Q H L : ℕ} [NeZero Q]
    (s : Finset ι) (p : ι → ZMod Q) (hH : 1 ≤ H) (hL : 1 ≤ L) (hQ : Q=H*L)
    (E F k : ℝ) (hE : 0 ≤ E) (hF : 0 ≤ F) (hk : 0 < k) (hk1 : k < 1)
    (B : ∀ j : ℕ, 0 < j →
       ‖∑ i ∈ s, ZMod.stdAddChar ((j:ZMod Q)*p i)‖ ≤ E*(j:ℝ)^k+F/j) :
    |∑ i ∈ s, ReciprocalSmoothing.saw (p i)| ≤
      s.card/(2*(H:ℝ)) + (E*((1/k+1/(1-k))*(H:ℝ)^k)+2*F)/2 := by
  classical
  have hqr : (Q:ℝ)=(H:ℝ)*L := by exact_mod_cast hQ
  have qp : (0:ℝ)<Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hp : (0:ℝ)<H := by exact_mod_cast hH
  have lp : (0:ℝ)<L := by exact_mod_cast hL
  have f_eq : (fun a : ZMod Q => (ReciprocalSmoothing.saw a : ℂ)) = gridSaw := by
    funext a
    simp only [ReciprocalSmoothing.saw,gridSaw,Complex.ofReal_sub,Complex.ofReal_div,
      Complex.ofReal_natCast,Complex.ofReal_one,Complex.ofReal_ofNat]
  let spec (a : ZMod Q) := ‖∑ i ∈ s, ZMod.stdAddChar (a*p i)‖
  let raw (a : ZMod Q) := ‖ZMod.dft (gridSaw (Q:=Q)) a‖ / Q * spec a *
                            ‖boxCoeff L (ZMod.stdAddChar a)‖
  let M (j : ℕ) := E*(j:ℝ)^k+F/j
  let f (j : ℕ) := frequencyWeight H j * M j
  have Mpos (j : ℕ) : 0 ≤ M j := by dsimp [M]; positivity
  have fpos (j : ℕ) : 0 ≤ f j := by dsimp [f,frequencyWeight]; positivity
  have bound (a : ZMod Q) (ha : a ≠ 0) : raw a ≤ f (folded a)/4 := by
    have m : (0:ℝ)<folded a := by exact_mod_cast folded_pos ha
    have bb := box_frequency_bound (L:=L) hL ha
    have cmp : (Q:ℝ)/(2*L*(folded a:ℝ)) ≤ (H:ℝ)/(folded a) := by
      rw [hqr]; apply (div_le_div_iff₀ (by positivity) m).mpr
      nlinarith [mul_pos (mul_pos hp lp) m]
    have b := bb.trans (min_le_min_left 1 cmp)
    have aBound : spec a ≤ M (folded a) := spectrum_folded s p M B ha
    calc
      raw a ≤ 1/(4*(folded a:ℝ))*M (folded a)*min 1 ((H:ℝ)/folded a) :=
        mul_le_mul (mul_le_mul (normalized_dft_bound ha) aBound (norm_nonneg _) (by positivity))
          b (norm_nonneg _) (mul_nonneg (by positivity) (Mpos _))
      _ = _ := by dsimp [f,frequencyWeight]; ring
  have spec0 : spec 0 = s.card := by simp [spec]
  have zeroRaw : raw 0 = s.card/(2*(Q:ℝ)) := by
    have boxOne : boxCoeff L (ZMod.stdAddChar (0:ZMod Q)) = 1 := by
      simp [boxCoeff,(show (L:ℂ) ≠ 0 by exact_mod_cast (show L≠0 by omega))]
    dsimp only [raw]
    rw [boxOne,dft_gridSaw_zero,spec0]
    norm_num <;> ring
  have hCut : H ≤ Q := hQ ▸ Nat.le_mul_of_pos_right H hL
  have foldedBudget := sum_folded (Q:=Q) f fpos
  have total : (∑ a : ZMod Q, raw a) ≤
      s.card/(2*(Q:ℝ)) + (E*((1/k+1/(1-k))*(H:ℝ)^k)+2*F)/2 := by
    rw [← add_sum_erase _ _ (mem_univ (0:ZMod Q)),zeroRaw]
    apply add_le_add le_rfl
    calc
      _ ≤ ∑ a ∈ (univ : Finset (ZMod Q)).erase 0, f (folded a)/4 :=
        sum_le_sum (fun a ha => bound a (mem_erase.mp ha).1)
      _ = (∑ a ∈ (univ : Finset (ZMod Q)).erase 0, f (folded a))/4 := by rw [sum_div]
      _ ≤ _ := by
        have moment := frequency_budget H Q hH hCut E F k hE hF hk hk1
        change (∑ j ∈ Icc 1 Q, f j) ≤ _ at moment
        change (∑ a ∈ (univ : Finset (ZMod Q)).erase 0, f (folded a)) ≤ _ at foldedBudget
        linarith
  have start := ReciprocalSmoothing.normalized_discrepancy s p (L:=L) hL
  rw [f_eq] at start
  change _ ≤ _ + ∑ a : ZMod Q, raw a at start
  have rounding : (s.card:ℝ)*((L:ℝ)-1)/(2*Q)+s.card/(2*(Q:ℝ))=s.card/(2*(H:ℝ)) := by
    rw [hqr]; field_simp; ring
  linarith

/-- For a list of positive moduli a, denote its jth reciprocal exponential
sum by S(j). A bound E*j^k+F/j for S(j) bounds the actual sieve remainder. -/
theorem reciprocal_transfer (u v : ℝ) (x t H : ℕ) (hH : 1 ≤ H)
    (E F k : ℝ) (hE : 0 ≤ E) (hF : 0 ≤ F) (hk : 0 < k) (hk1 : k < 1)
    (B : ∀ j : ℕ, 0 < j →
      ‖∑ m ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter (t ∣ ·),
        Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*x/m)‖ ≤ E*(j:ℝ)^k+F/j) :
    |FactorialSieve.remainder u v x t| ≤
      ((Ioc ⌊u⌋₊ ⌊v⌋₊).filter (t ∣ ·)).card/(2*(H:ℝ)) +
        (E*((1/k+1/(1-k))*(H:ℝ)^k)+2*F)/2 := by
  obtain ⟨L,lp,divs⟩ := exists_grid v H
  let Q := H*L
  have l : 1 ≤ L := by omega
  let _ : NeZero Q := ⟨(Nat.mul_pos hH l).ne'⟩
  let S := (Ioc ⌊u⌋₊ ⌊v⌋₊).filter (t ∣ ·)
  have C (j : ℕ) (jp : 0<j) :
      ‖∑ m ∈ S, ZMod.stdAddChar ((j:ZMod Q)*residue Q x m)‖ ≤ E*(j:ℝ)^k+F/j := by
    refine le_of_eq_of_le (congrArg _ (sum_congr rfl ?_)) (B j jp)
    intro m hm
    obtain ⟨hl,hu⟩ := mem_Ioc.mp (mem_filter.mp hm).1
    have mp : 0 < m := by omega
    exact residue_character mp (divs m mp hu) x j
  rw [remainder_grid (Q:=Q) u v x t divs]
  exact grid_transfer S (residue Q x) hH l rfl E F k hE hF hk hk1 C

end FactorialFourier
#print axioms FactorialFourier.reciprocal_transfer

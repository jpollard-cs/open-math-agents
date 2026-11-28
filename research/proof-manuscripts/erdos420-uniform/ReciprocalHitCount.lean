import FactorialSelbergBlock

/-! Counting the project’s prime hits by the prime and the corresponding
multiple. The source set may already have been restricted to a wider band. -/
open Finset
namespace FactorialFourier

theorem hit_card_le (n h : ℕ) (u v : ℝ) (hu : 0 ≤ u)
    (S : Finset ((i : ℕ) × ℕ))
    (hits : ∀ z ∈ S, z.1 < h ∧ z.2.Prime ∧ z.2 ∣ n+z.1+1 ∧ u < (z.2:ℝ) ∧ (z.2:ℝ) ≤ v) :
    (S.card : ℝ) ≤ ∑ p ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime, (FactorialSieve.multiplicity n h p:ℝ) := by
  classical
  let P := (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime
  let f (z : (i : ℕ) × ℕ) : (p : ℕ) × ℕ := ⟨z.2,(n+z.1+1)/z.2⟩
  have inj := card_le_card_of_injOn (s:=S) (t:=P.sigma (fun p => Ioc (n/p) ((n+h)/p))) f (by
    intro z hz
    obtain ⟨hi,prime,hd,lo,up⟩ := hits z hz
    have recover :=  Nat.div_mul_cancel hd
    apply mem_sigma.mpr
    refine ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨(Nat.floor_lt hu).mpr lo,(Nat.le_floor up)⟩,prime⟩,?_⟩
    exact mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul prime.pos).mpr (by rw [recover]; omega),
      Nat.div_le_div_right (by omega)⟩) (by
    rintro ⟨i,p⟩ hi ⟨j,q⟩ hj eq
    have pq : p=q := congrArg Sigma.fst eq
    subst q
    have hq : (n+i+1)/p=(n+j+1)/p := congrArg (fun y : (k:ℕ) × ℕ => y.2) eq
    have l := Nat.div_mul_cancel (hits _ hi).2.2.1
    have r := Nat.div_mul_cancel (hits _ hj).2.2.1
    change (n+i+1)/p*p=n+i+1 at l
    change (n+j+1)/p*p=n+j+1 at r
    rw [hq] at l
    have e : i=j := by omega
    subst j; rfl)
  simp only [card_sigma,Nat.card_Ioc] at inj
  dsimp [P] at inj
  change (S.card:ℝ) ≤ ∑ p ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime, (((n+h)/p-n/p:ℕ):ℝ)
  exact_mod_cast inj

end FactorialFourier
#print axioms FactorialFourier.hit_card_le

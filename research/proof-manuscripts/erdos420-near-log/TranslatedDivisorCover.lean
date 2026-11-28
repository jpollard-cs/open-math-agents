import Init

/-!
# Divisor certificates on a translated arithmetic progression

This finite lemma assembles the two kinds of divisor certificate used in
the factorial-window argument. The first hypothesis on root families is
the interface of the simultaneous-residue theorem. The second is the
interface of the linear-root lemma applied separately to each modulus.
No primality assumption is necessary for the assembly step itself.

The root supplied by the linear-root lemma corresponds to the point
`b + M * (t + 1)`. The progression can therefore start one step before
the first candidate. All interval offsets are ordinary natural numbers.
-/

namespace TranslatedDivisorCover

/-- If every exceptional offset has a simultaneous modular hit and all
remaining offsets have a suitable divisor of both the initial translate
and the progression modulus, a single progression point has a divisor
certificate at every offset. -/
theorem of_simultaneous_roots
    {A : Type} {k H b M T W U : Nat}
    (P : A → Nat) (s : Fin k → Nat)
    (hsim : ∀ root : (p : A) → Fin k → Fin (P p),
      (∀ p i j, root p i = root p j → i = j) →
      ∃ t < T, ∀ i, ∃ p : A, t % P p = (root p i).val)
    (hlinear : ∀ p : A, ∃ root : Fin k → Fin (P p),
      (∀ i j, root i = root j → i = j) ∧
      ∀ t i, t % P p = (root i).val → P p ∣ b + M * (t + 1) + s i)
    (hbound : ∀ p : A, W < P p ∧ P p < U)
    (hgood : ∀ i, 1 ≤ i → i ≤ H →
      (∀ j, s j ≠ i) → ∃ d, W < d ∧ d < U ∧ d ∣ b + i ∧ d ∣ M) :
    ∃ t < T, ∀ i, 1 ≤ i → i ≤ H →
      ∃ d, W < d ∧ d < U ∧ d ∣ b + M * (t + 1) + i := by
  classical
  let root (p : A) := Classical.choose (hlinear p)
  have hr (p : A) := Classical.choose_spec (hlinear p)
  obtain ⟨t, ht, hhit⟩ := hsim root (fun p => (hr p).1)
  refine ⟨t, ht, ?_⟩
  intro i hi hiH
  by_cases he : ∃ j, s j = i
  · obtain ⟨j, rfl⟩ := he
    obtain ⟨p, hp⟩ := hhit j
    exact ⟨P p, (hbound p).1, (hbound p).2, (hr p).2 t j hp⟩
  · have hne (j) : s j ≠ i := fun hj => he ⟨j, hj⟩
    obtain ⟨d, hdW, hdU, hd, hdM⟩ := hgood i hi hiH hne
    refine ⟨d, hdW, hdU, ?_⟩
    have h : d ∣ (b + i) + M * (t + 1) :=
      Nat.dvd_add hd (Nat.dvd_mul_right_of_dvd hdM _)
    simpa only [Nat.add_right_comm b i] using h

/-- If a divisor of `p * s` lies strictly between `W` and its square
root, the cofactor `s` must exceed `W` whenever `p` is prime. We use
only the characterization of primality by divisors, so the proof remains
independent of any number-theory library. -/
theorem cofactor_gt_of_divisor
    {W d p s : Nat} (hWd : W < d) (hsq : d * d < p * s)
    (hd : d ∣ p * s) (hprime : ∀ k, k ∣ p → k = 1 ∨ k = p) :
    W < s := by
  by_cases hs : d ≤ s
  · exact Nat.lt_of_lt_of_le hWd hs
  have hp : d < p := by
    apply Nat.lt_of_not_ge
    intro hpd
    have hsd : s ≤ d := Nat.le_of_not_le hs
    exact (Nat.not_le_of_gt hsq) (Nat.mul_le_mul hpd hsd)
  have hcop : d.Coprime p := by
    change d.gcd p = 1
    rcases hprime _ (Nat.gcd_dvd_right d p) with h | h
    · exact h
    · have hle := Nat.gcd_le_left p (Nat.lt_of_le_of_lt (Nat.zero_le W) hWd)
      rw [h] at hle
      exact False.elim ((Nat.not_le_of_gt hp) hle)
  have hspos : 0 < s := by
    cases s with
    | zero => simp at hsq
    | succ s => exact Nat.zero_lt_succ s
  exact Nat.lt_of_lt_of_le hWd (Nat.le_of_dvd hspos (hcop.dvd_of_dvd_mul_left hd))

end TranslatedDivisorCover

import Std

namespace AxisSurvival
variable {V : Type} {A : V → Type}
abbrev Point (A : V → Type) := (i : V) → A i

def avoids (guard : (i : V) → A i → V → Prop) (z x : Point A) : Prop :=
  ∀ i a, a ≠ z i → ¬ (x i = a ∧ ∀ j, guard i a j → x j = z j)

theorem support_test (guard : (i : V) → A i → V → Prop) (z : Point A)
    (allowed : (i : V) → A i → Prop) :
    (∃ x : Point A, (∃ i, x i ≠ z i) ∧ (∀ i, allowed i (x i)) ∧ avoids guard z x) ↔
    ∃ U : V → Prop, (∃ i, U i) ∧ (∀ i, ¬ allowed i (z i) → U i) ∧
      ∀ i, U i → ∃ a, a ≠ z i ∧ allowed i a ∧ ∃ j, guard i a j ∧ U j := by
  classical
  constructor
  · rintro ⟨x, hx, ha, hr⟩
    refine ⟨fun i => x i ≠ z i, hx, ?_, ?_⟩
    · intro i nz eq
      exact nz (eq ▸ ha i)
    · intro i hi
      refine ⟨x i, hi, ha i, ?_⟩
      apply Classical.byContradiction
      intro hn
      apply hr i (x i) hi
      refine ⟨rfl, ?_⟩
      intro j hj
      apply Classical.byContradiction
      exact fun hne => hn ⟨j, hj, hne⟩
  · rintro ⟨U, hu, hf, step⟩
    let x : Point A := fun i => if h : U i then (step i h).choose else z i
    have atU (i : V) (hi : U i) :
        x i ≠ z i ∧ allowed i (x i) ∧ ∃ j, guard i (x i) j ∧ U j := by
      simpa [x, hi] using (step i hi).choose_spec
    obtain ⟨i, hi⟩ := hu
    refine ⟨x, ⟨i, (atU i hi).1⟩, ?_, ?_⟩
    · intro j
      by_cases hj : U j
      · exact (atU j hj).2.1
      · have haz : allowed j (z j) := Classical.byContradiction (fun hn => hj (hf j hn))
        simpa [x, hj] using haz
    · rintro j a hn ⟨same, quiet⟩
      by_cases hj : U j
      · obtain ⟨l, edge, hl⟩ := (atU j hj).2.2
        exact (atU l hl).1 (quiet l (same ▸ edge))
      · exact hn (by simpa [x, hj] using same.symm)

#print axioms support_test
end AxisSurvival

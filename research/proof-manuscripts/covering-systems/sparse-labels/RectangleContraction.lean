import Std

/-! A local cover in a product of two coordinates. The internal residue
assignment may be arbitrary. For an irreducible list, each full internal
assignment has a private point for each of its indexed rows. -/
namespace CoveringRectangle
variable {X Y I : Type} (low : X → Prop) (outer : I → X → Prop)
  (inner : I → Y → Prop)

theorem contraction
    (privatePoint : (∀ y, ∃ i, inner i y) →
      ∀ i, ∃ y, ∀ j, inner j y → j = i) :
    (∀ x y, low x ∨ ∃ i, outer i x ∧ inner i y) ↔
    (∀ x, low x) ∨ ((∀ y, ∃ i, inner i y) ∧
      ∀ x, low x ∨ ∀ i, outer i x) := by
  classical
  constructor
  · intro cover
    by_cases hl : ∀ x, low x
    · exact Or.inl hl
    · obtain ⟨a, ha⟩ := Classical.not_forall.mp hl
      have hi : ∀ y, ∃ i, inner i y := by
        intro y
        obtain ⟨i, _, hy⟩ := (cover a y).resolve_left ha
        exact ⟨i, hy⟩
      refine Or.inr ⟨hi, ?_⟩
      intro x
      by_cases h : low x
      · exact Or.inl h
      · apply Or.inr
        intro i
        obtain ⟨y, only⟩ := privatePoint hi i
        obtain ⟨j, hj, hy⟩ := (cover x y).resolve_left h
        exact only j hy ▸ hj
  · rintro (hl | ⟨hi, hx⟩) x y
    · exact Or.inl (hl x)
    · rcases hx x with hl | h
      · exact Or.inl hl
      · obtain ⟨i, hy⟩ := hi y
        exact Or.inr ⟨i, h i, hy⟩

theorem deletion (i : I) (miss : ∃ y, ∀ j, j ≠ i → ¬ inner j y)
    (cover : ∀ x y, low x ∨ ∃ j, j ≠ i ∧ outer j x ∧ inner j y) :
    ∀ x, low x := by
  obtain ⟨y, hy⟩ := miss
  intro x
  rcases cover x y with h | ⟨j, hji, _, hj⟩
  · exact h
  · exact False.elim (hy j hji hj)

#print axioms contraction
#print axioms deletion
end CoveringRectangle

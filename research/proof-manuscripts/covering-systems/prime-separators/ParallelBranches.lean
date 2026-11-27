import Std

/-! Cover contraction for independent branches with possibly shared exterior
coordinates. Every predicate selecting rows and every assignment is arbitrary. -/
namespace PrimeBranches

theorem fibre {G : Type} {Y : G → Type} {T : (g : G) → Y g → Prop} :
    (∀ y : (g : G) → Y g, ∃ g, T g (y g)) ↔ ∃ g, ∀ v, T g v := by
  classical
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    have miss (g : G) : ∃ v, ¬ T g v := by
      apply Classical.not_forall.mp
      intro hg
      exact hn ⟨g,hg⟩
    obtain ⟨g,hit⟩ := h (fun g => Classical.choose (miss g))
    exact Classical.choose_spec (miss g) hit
  · rintro ⟨g,hg⟩ y
    exact ⟨g,hg (y g)⟩

theorem contract {G X : Type} {Y I : G → Type}
    (low : X → Prop) (keep : (g : G) → I g → Prop)
    (outer : (g : G) → I g → X → Prop)
    (inner : (g : G) → I g → Y g → Prop)
    (essential : ∀ g (use : I g → Prop),
      (∀ v, ∃ i, use i ∧ inner g i v) → ∀ i, use i)
    (full : ∀ g v, ∃ i, inner g i v) :
    (∀ x (y : (g : G) → Y g), low x ∨
      ∃ g i, keep g i ∧ outer g i x ∧ inner g i (y g)) ↔
    (∀ x, low x ∨ ∃ g, ∀ i, keep g i ∧ outer g i x) := by
  classical
  constructor
  · intro covered x
    by_cases hx : low x
    · exact Or.inl hx
    · apply Or.inr
      have h (y : (g : G) → Y g) :
          ∃ g i, (keep g i ∧ outer g i x) ∧ inner g i (y g) := by
        obtain ⟨g,i,k,o,v⟩ := (covered x y).resolve_left hx
        exact ⟨g,i,⟨k,o⟩,v⟩
      obtain ⟨g,hg⟩ := (fibre (G:=G) (Y:=Y) (T:=fun g v => ∃ i, (keep g i ∧ outer g i x) ∧ inner g i v)).mp h
      exact ⟨g,essential g _ hg⟩
  · intro h x y
    rcases h x with v | ⟨g,hg⟩
    · exact Or.inl v
    · obtain ⟨i,hi⟩ := full g (y g)
      exact Or.inr ⟨g,i,(hg i).1,(hg i).2,hi⟩

-- Across a set of base holes, a group need only cover the points at
-- which it is active. No disjointness of the exterior periods is assumed.
#print axioms fibre
#print axioms contract
end PrimeBranches

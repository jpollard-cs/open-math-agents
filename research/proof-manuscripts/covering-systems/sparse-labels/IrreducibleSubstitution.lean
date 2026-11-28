import Std

/-! Independent assignments on the two factors, with an exterior intersection
that can be replaced by a single old row. The criterion quantifies over all
assignments and arbitrary subfamilies. -/
namespace CoveringSubstitution
variable {X Y I A O B V : Type}

def Expanded (low : A → X → Prop) (outer : O → I → X → Prop)
    (inner : B → I → Y → Prop) (keep : I → Prop) : Prop :=
  ∃ a o b, ∀ x y, low a x ∨ ∃ i, keep i ∧ outer o i x ∧ inner b i y

theorem criterion [Nonempty O]
    (low : A → X → Prop) (outer : O → I → X → Prop)
    (inner : B → I → Y → Prop) (one : V → X → Prop) (keep : I → Prop)
    (innerFull : ∃ b, ∀ y, ∃ i, inner b i y)
    (essential : ∀ b (use : I → Prop),
      (∀ y, ∃ i, use i ∧ inner b i y) → ∀ i, use i)
    (contract : ∀ o, ∃ v, ∀ x, (∀ i, outer o i x) → one v x)
    (lift : ∀ v, ∃ o, ∀ x, one v x → ∀ i, outer o i x) :
    Expanded low outer inner keep ↔
      (∃ a, ∀ x, low a x) ∨
      ((∃ a v, ∀ x, low a x ∨ one v x) ∧ ∀ i, keep i) := by
  classical
  constructor
  · rintro ⟨a,o,b,h⟩
    by_cases allLow : ∀ x, low a x
    · exact Or.inl ⟨a,allLow⟩
    · obtain ⟨u, hu⟩ := Classical.not_forall.mp allLow
      have each (x : X) (hx : ¬ low a x) : ∀ i, keep i ∧ outer o i x := by
        apply essential b (fun i => keep i ∧ outer o i x)
        intro y
        obtain ⟨i,hk,ho,hi⟩ := (h x y).resolve_left hx
        exact ⟨i,⟨hk,ho⟩,hi⟩
      obtain ⟨v,hv⟩ := contract o
      refine Or.inr ⟨⟨a,v,?_⟩,fun i => (each u hu i).1⟩
      intro x
      by_cases hx : low a x
      · exact Or.inl hx
      · exact Or.inr (hv x (fun i => (each x hx i).2))
  · rintro (⟨a,ha⟩ | ⟨⟨a,v,ha⟩,hk⟩)
    · obtain ⟨o⟩ := ‹Nonempty O›
      obtain ⟨b,_⟩ := innerFull
      exact ⟨a,o,b,fun x _ => Or.inl (ha x)⟩
    · obtain ⟨o,ho⟩ := lift v
      obtain ⟨b,hb⟩ := innerFull
      refine ⟨a,o,b,?_⟩
      intro x y
      rcases ha x with h | h
      · exact Or.inl h
      · obtain ⟨i,hi⟩ := hb y
        exact Or.inr ⟨i,hk i,ho x h i,hi⟩

theorem irreducible [Nonempty O] {K : Type}
    (old : A → K → X → Prop) (outer : O → I → X → Prop)
    (inner : B → I → Y → Prop) (one : V → X → Prop)
    (innerFull : ∃ b, ∀ y, ∃ i, inner b i y)
    (essential : ∀ b (use : I → Prop),
      (∀ y, ∃ i, use i ∧ inner b i y) → ∀ i, use i)
    (contract : ∀ o, ∃ v, ∀ x, (∀ i, outer o i x) → one v x)
    (lift : ∀ v, ∃ o, ∀ x, one v x → ∀ i, outer o i x)
    (oldFull : ∃ a v, ∀ x, (∃ j, old a j x) ∨ one v x)
    (oldNeedsOne : ¬ ∃ a, ∀ x, ∃ j, old a j x)
    (oldNeedsOthers : ∀ (use : K → Prop) a v,
      (∀ x, (∃ j, use j ∧ old a j x) ∨ one v x) → ∀ j, use j)
    (keepOld : K → Prop) (keepNew : I → Prop) :
    Expanded (fun a x => ∃ j, keepOld j ∧ old a j x) outer inner keepNew ↔
      (∀ j, keepOld j) ∧ (∀ i, keepNew i) := by
  rw [criterion _ outer inner one keepNew innerFull essential contract lift]
  constructor
  · rintro (⟨a,ha⟩ | ⟨⟨a,v,ha⟩,hn⟩)
    · apply False.elim
      apply oldNeedsOne
      refine ⟨a,?_⟩
      intro x
      obtain ⟨j,_,hj⟩ := ha x
      exact ⟨j,hj⟩
    · exact ⟨oldNeedsOthers keepOld a v ha,hn⟩
  · rintro ⟨ho,hn⟩
    obtain ⟨a,v,ha⟩ := oldFull
    refine Or.inr ⟨⟨a,v,?_⟩,hn⟩
    intro x
    rcases ha x with ⟨j,hj⟩ | h
    · exact Or.inl ⟨j,ho j,hj⟩
    · exact Or.inr h

#print axioms criterion
#print axioms irreducible
end CoveringSubstitution

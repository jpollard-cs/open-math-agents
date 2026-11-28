/- Codex (OpenAI). An autarky for product covers from a cycle of exclusive projections. -/
namespace PrimeOwnerCycle
universe u v w
variable {P : Type u} {R : Type v} {V : P → Type w}
abbrev Assignment (V : P → Type w) := (p : P) → V p
def Hits (accepts : R → (p : P) → V p → Prop) (r : R) (x : Assignment V) :=
  ∀ p, accepts r p (x p)

/-- A chosen value at each marked site permits at most its owner among
the tested rows. If every chosen owner is blocked at another marked site,
all rows touching the marked sites can be removed from a cover. -/
theorem removable (uses : R → P → Prop) (accepts : R → (p : P) → V p → Prop)
    (free : ∀ r p, ¬ uses r p → ∀ z, accepts r p z)
    (cover : ∀ x : Assignment V, ∃ r, Hits accepts r x)
    (marked : P → Prop) [DecidablePred marked]
    (label : Assignment V) (owner : P → R)
    (exclusive : ∀ p, marked p → ∀ r, uses r p → accepts r p (label p) → r = owner p)
    (killed : ∀ p, marked p → ∃ q, marked q ∧ uses (owner p) q ∧ owner p ≠ owner q) :
    ∀ x : Assignment V, ∃ r, (∀ p, marked p → ¬ uses r p) ∧ Hits accepts r x := by
  intro x
  let y : Assignment V := fun p => if marked p then label p else x p
  obtain ⟨r, hr⟩ := cover y
  have avoids : ∀ p, marked p → ¬ uses r p := by
    intro p hp huse
    have heq := exclusive p hp r huse (by simpa [y, hp] using hr p)
    obtain ⟨q, hq, hquse, hne⟩ := killed p hp
    have heq' := exclusive q hq r (heq ▸ hquse) (by simpa [y, hq] using hr q)
    exact hne (heq.symm.trans heq')
  refine ⟨r, avoids, ?_⟩
  intro p
  by_cases hp : marked p
  · exact free r p (avoids p hp) _
  · simpa [y, hp] using hr p

#print axioms removable
end PrimeOwnerCycle

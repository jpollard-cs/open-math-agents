import Std
namespace IndexedDecisions
instance (P : Empty → Prop) : Decidable (∀ j,P j) := isTrue (fun j => Empty.elim j)

instance {I} (P : Option I → Prop) [Decidable (P none)] [Decidable (∀ i,P (some i))] :
    Decidable (∀ i,P i) :=
  decidable_of_iff (P none ∧ ∀ i,P (some i)) ⟨fun h => fun | none => h.1 | some i => h.2 i,
    fun h => ⟨h none, fun i => h (some i)⟩⟩

instance {I} (P : Option I → Prop) [Decidable (P none)] [Decidable (∃ i,P (some i))] :
    Decidable (∃ i,P i) :=
  decidable_of_iff (P none ∨ ∃ i,P (some i)) ⟨fun h => by
    rcases h with h | ⟨i,hi⟩
    · exact ⟨none,h⟩
    · exact ⟨some i,hi⟩, fun ⟨i,h⟩ => by
    cases i with
    | none => exact Or.inl h
    | some j => exact Or.inr ⟨j,h⟩⟩

instance {I J} (P : Sum I J → Prop)
    [Decidable (∀ i,P (Sum.inl i))] [Decidable (∀ j,P (Sum.inr j))] :
    Decidable (∀ t,P t) :=
  decidable_of_iff ((∀ i,P (.inl i)) ∧ (∀ j,P (.inr j)))
    ⟨fun h => fun | .inl i => h.1 i | .inr j => h.2 j,
      fun h => ⟨fun i => h (.inl i),fun j => h (.inr j)⟩⟩
end IndexedDecisions

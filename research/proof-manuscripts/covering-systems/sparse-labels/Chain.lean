import IntegerSubstitution
namespace CoveringChain
open IntegerSubstitution CoveringResidues

theorem seed (ko : Empty → Prop) (u : Prop) :
    Old (fun _ : Empty => (1:Int)) 1 ko u ↔ (∀ j,ko j) ∧ u := by
  constructor
  · rintro ⟨_,_,h⟩
    rcases h 0 with ⟨j,_⟩ | ⟨hu,_⟩
    · exact nomatch j
    · exact ⟨(fun j => Empty.elim j),hu⟩
  · rintro ⟨_,hu⟩
    exact ⟨Empty.elim,0,fun x => Or.inr ⟨hu,Int.one_dvd _⟩⟩

theorem stage {K J : Type} (m : K → Int) (e b : Option J → Int)
    (base : ∀ ko kn, New m e b ko kn ↔ (∀ j, ko j) ∧ (∀ i, kn i))
    (h : Sum K J → Prop) (u : Prop) :
    Old (Sum.elim m (fun j => e (some j)*b (some j))) (e none*b none) h u
    ↔ (∀ j,h j) ∧ u := by
  let ko := fun j => h (Sum.inl j)
  let kn := fun i : Option J => i.elim u (fun j => h (Sum.inr j))
  constructor
  · rintro ⟨a,v,hx⟩
    have hc : New m e b ko kn := by
      refine ⟨fun j => a (.inl j),fun i => i.elim v (fun j => a (.inr j)),?_⟩
      intro z
      rcases hx z with ⟨j,hj,ht⟩ | ⟨hu,ht⟩
      · cases j with
        | inl q => exact Or.inl ⟨q,hj,ht⟩
        | inr q => exact Or.inr ⟨some q,hj,ht⟩
      · exact Or.inr ⟨none,hu,ht⟩
    obtain ⟨ho,hn⟩ := (base ko kn).mp hc
    exact ⟨fun | .inl j => ho j | .inr j => hn (some j), hn none⟩
  · rintro ⟨hall,hu⟩
    have hn : ∀ i, kn i := fun | none => hu | some j => hall (.inr j)
    obtain ⟨a,r,hr⟩ := (base ko kn).mpr ⟨fun j => hall (.inl j),hn⟩
    refine ⟨Sum.elim a (fun j => r (some j)),r none,?_⟩
    intro z
    rcases hr z with ⟨j,hj,ht⟩ | ⟨i,hi,ht⟩
    · exact Or.inl ⟨.inl j,hj,ht⟩
    · cases i with
      | none => exact Or.inr ⟨hi,ht⟩
      | some j => exact Or.inl ⟨.inr j,hi,ht⟩

theorem lcmOfLast {J : Type} (d : Int) (e : Option J → Int)
    (last : e none=d) (all : ∀ j, e j ∣ d) (z : Int) :
    (∀ i, e i ∣ z) ↔ d ∣ z := by
  constructor
  · intro h; simpa [last] using h none
  · intro h i; exact Int.dvd_trans (all i) h

end CoveringChain

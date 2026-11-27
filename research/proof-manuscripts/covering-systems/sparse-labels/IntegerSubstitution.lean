import IrreducibleSubstitution
import ResidueContraction

/-! Irreducibility of an actual integer congruence substitution under fresh
choices of all residues. Indices distinguish rows even during a construction
with repeated moduli. Endpoints are stated on all integers. -/
namespace IntegerSubstitution
open CoveringResidues
variable {I K : Type}

def Covers (m : I → Int) (keep : I → Prop) : Prop :=
  ∃ r : I → Int, ∀ z : Int, ∃ i, keep i ∧ Same (m i) z (r i)

def Old (m : K → Int) (d : Int) (keep : K → Prop) (useOne : Prop) : Prop :=
  ∃ a : K → Int, ∃ v : Int, ∀ z : Int,
    (∃ j, keep j ∧ Same (m j) z (a j)) ∨ (useOne ∧ Same d z v)

def New (m : K → Int) (e b : I → Int) (ko : K → Prop) (kn : I → Prop) : Prop :=
  ∃ a : K → Int, ∃ r : I → Int, ∀ z : Int,
    (∃ j, ko j ∧ Same (m j) z (a j)) ∨ ∃ i, kn i ∧ Same (e i*b i) z (r i)

private theorem weaken {d l x y : Int} (h : d ∣ l) (v : Same l x y) : Same d x y :=
  Int.dvd_trans h v

private theorem change {d x y r : Int} (a : Same d x y) (b : Same d x r) : Same d y r := by
  obtain ⟨u,hu⟩ := a
  obtain ⟨v,hv⟩ := b
  refine ⟨v-u,?_⟩
  rw [Int.mul_sub]
  omega

private theorem symm {d x y : Int} (a : Same d x y) : Same d y x := by
  obtain ⟨u,hu⟩ := a
  exact ⟨-u,by grind⟩

theorem irreducible (m : K → Int) (d : Int) (e b : I → Int)
    (L N s t : Int) (bezout : L*s+N*t=1)
    (hm : ∀ j, m j ∣ L) (he : ∀ i, e i ∣ L) (hb : ∀ i, b i ∣ N)
    (lcmSpec : ∀ z, (∀ i, e i ∣ z) ↔ d ∣ z)
    (oldMinimal : ∀ ko u, Old m d ko u ↔ (∀ j, ko j) ∧ u)
    (innerMinimal : ∀ kn, Covers b kn ↔ ∀ i, kn i)
    (ko : K → Prop) (kn : I → Prop) :
    New m e b ko kn ↔ (∀ j, ko j) ∧ (∀ i, kn i) := by
  classical
  let lo := fun (a : K → Int) (j : K) x => Same (m j) x (a j)
  let out := fun (o : I → Int) (i : I) x => Same (e i) x (o i)
  let inn := fun (r : I → Int) (i : I) x => Same (b i) x (r i)
  let low := fun a x => ∃ j, ko j ∧ lo a j x
  have prodEq (i : I) (z : Int) : e i*b i ∣ z ↔ e i ∣ z ∧ b i ∣ z := by
    obtain ⟨h,hh⟩ := he i
    obtain ⟨g,hg⟩ := hb i
    apply coprimeProduct (e i) (b i) (h*s) (g*t)
    grind
  have equiv : New m e b ko kn ↔ CoveringSubstitution.Expanded low out inn kn := by
    constructor
    · rintro ⟨a,r,hr⟩
      refine ⟨a,r,r,?_⟩
      intro x y
      obtain ⟨z,hx,hy⟩ := interpolate L N s t bezout x y
      rcases hr z with ⟨j,hj,hit⟩ | ⟨i,hi,hit⟩
      · exact Or.inl ⟨j,hj,change (weaken (hm j) hx) hit⟩
      · obtain ⟨u,v⟩ := (prodEq i _).mp hit
        exact Or.inr ⟨i,hi,change (weaken (he i) hx) u,change (weaken (hb i) hy) v⟩
    · rintro ⟨a,o,r,hr⟩
      have supply (i : I) := interpolate L N s t bezout (o i) (r i)
      let f := fun i => Classical.choose (supply i)
      have congr (i : I) : Same L (f i) (o i) ∧ Same N (f i) (r i) :=
        Classical.choose_spec (supply i)
      refine ⟨a,f,?_⟩
      intro z
      rcases hr z z with h | ⟨i,hi,ho,hn⟩
      · exact Or.inl h
      · have u := change (symm ho) (symm (weaken (he i) (congr i).1))
        have v := change (symm hn) (symm (weaken (hb i) (congr i).2))
        exact Or.inr ⟨i,hi,(prodEq i _).mpr ⟨u,v⟩⟩
  rw [equiv]
  apply CoveringSubstitution.irreducible lo out inn (fun v x => Same d x v)
  · obtain ⟨r,hr⟩ := (innerMinimal (fun _ => True)).mpr (fun _ => True.intro)
    exact ⟨r,fun x => by obtain ⟨i,_,hi⟩ := hr x; exact ⟨i,hi⟩⟩
  · intro r use h
    exact (innerMinimal use).mp ⟨r,h⟩
  · exact contraction e d lcmSpec
  · exact lift e d lcmSpec
  · obtain ⟨a,v,h⟩ := (oldMinimal (fun _ => True) True).mpr ⟨fun _ => True.intro,True.intro⟩
    refine ⟨a,v,?_⟩
    intro x
    rcases h x with ⟨j,_,hj⟩ | ⟨_,hv⟩
    · exact Or.inl ⟨j,hj⟩
    · exact Or.inr hv
  · rintro ⟨a,h⟩
    apply ((oldMinimal (fun _ => True) False).mp ?_).2
    refine ⟨a,0,?_⟩
    intro x
    obtain ⟨j,hj⟩ := h x
    exact Or.inl ⟨j,True.intro,hj⟩
  · intro use a v h
    apply ((oldMinimal use True).mp ?_).1
    refine ⟨a,v,?_⟩
    intro x
    exact (h x).imp_right (fun hv => ⟨True.intro,hv⟩)

#print axioms irreducible
end IntegerSubstitution

import PacketEssential

namespace SaturatedBox

/-- A packet row fixes one left coordinate and one of the remaining right values. -/
def Kills {U V : Type} {r : Nat} (coord : Fin r → U) (left : Fin r → V)
    (right : Fin r → Fin r) (active : Fin r → Prop) (x : U → V) : Prop :=
  ∀ j, ∃ i, active i ∧ x (coord i) = left i ∧ right i = j

theorem all_constraints {U V : Type} {r : Nat} {coord : Fin r → U}
    {left : Fin r → V} {right : Fin r → Fin r} {active : Fin r → Prop} {x : U → V}
    (hx : Kills coord left right active x) :
    ∀ i, active i ∧ x (coord i) = left i := by
  let H (i j : Fin r) := active i ∧ x (coord i)=left i ∧ right i=j
  intro i
  obtain ⟨_,a,h,_⟩ := PacketEssential.all_used H hx
    (fun _ _ _ h h' => h.2.2.symm.trans h'.2.2) i
  exact ⟨a,h⟩

theorem at_most_one {U V : Type} {r : Nat} {coord : Fin r → U}
    (hcoord : ∀ u, ∃ i, coord i=u) {left : Fin r → V} {right : Fin r → Fin r}
    {active : Fin r → Prop} {x y : U → V}
    (hx : Kills coord left right active x) (hy : Kills coord left right active y) :
    x=y := by
  funext u
  obtain ⟨i,rfl⟩ := hcoord u
  exact (all_constraints hx i).2.trans (all_constraints hy i).2.symm

/-- Any collection of saturated stars excluding every left assignment must contain
at least as many right vertices as left assignments. -/
theorem count {a b : Nat} (kills : Fin b → Fin a → Prop)
    (cover : ∀ x, ∃ w, kills w x)
    (one : ∀ w x y, kills w x → kills w y → x=y) : a≤b := by
  classical
  let f := fun x => Classical.choose (cover x)
  have hf (x) : kills (f x) x := Classical.choose_spec (cover x)
  have nd : ((List.finRange a).map f).Nodup :=
    (List.nodup_finRange a).map f (fun x y hn eq => hn (one _ x y (hf x) (eq ▸ hf y)))
  have bound := nd.length_le_of_subset (l₂ := List.finRange b)
    (fun {w} _ => List.mem_finRange w)
  simpa using bound

#print axioms at_most_one
#print axioms count
end SaturatedBox

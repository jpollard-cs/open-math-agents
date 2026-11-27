import Std

namespace OverfilledFibre

/-- Each active row can hit only one of the a surviving right values. -/
theorem active_count {D a : Nat} (active : Fin D → Bool) (right : Fin D → Nat)
    (cover : ∀ j : Fin a, ∃ r, active r = true ∧ right r = j.val) :
    a ≤ (List.finRange D).countP active := by
  classical
  let f := fun j => Classical.choose (cover j)
  have hf (j) := Classical.choose_spec (cover j)
  have nd : ((List.finRange a).map f).Nodup := (List.nodup_finRange a).map f (by
    intro i j hne heq
    apply hne
    apply Fin.ext
    exact (hf i).2.symm.trans ((congrArg right heq).trans (hf j).2))
  have sub : (List.finRange a).map f ⊆ (List.finRange D).filter active := by
    intro r hr
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hr
    exact List.mem_filter.mpr ⟨List.mem_finRange _,(hf j).1⟩
  simpa [List.countP_eq_length_filter] using nd.length_le_of_subset sub

private theorem incidence {α : Type} (x y diff : α → Bool)
    (ex : ∀ r, diff r = true → x r = true → y r = false) (l : List α) :
    l.countP x + l.countP y + l.countP diff ≤ 2*l.length := by
  induction l with
  | nil => simp
  | cons r rs ih =>
    have h := ex r
    cases hx : x r <;> cases hy : y r <;> cases hd : diff r <;>
      simp_all <;> omega

/-- The weighted number of rows whose left requirements differ at two excluded
vectors is at most twice the slack. The theorem permits inactive rows. -/
theorem two_point {D a : Nat} {U V : Type} [DecidableEq V]
    (coord : Fin D → U) (value : Fin D → V) (right : Fin D → Nat)
    (enabled : Fin D → Bool) (x y : U → V)
    (hx : ∀ j : Fin a, ∃ r, (enabled r && decide (x (coord r) = value r)) = true ∧ right r = j.val)
    (hy : ∀ j : Fin a, ∃ r, (enabled r && decide (y (coord r) = value r)) = true ∧ right r = j.val) :
    (List.finRange D).countP (fun r => decide (x (coord r) ≠ y (coord r))) ≤ 2*(D-a) := by
  have cx := active_count _ right hx
  have cy := active_count _ right hy
  have hc := incidence (fun r => enabled r && decide (x (coord r) = value r))
    (fun r => enabled r && decide (y (coord r) = value r))
    (fun r => decide (x (coord r) ≠ y (coord r))) (by
      intro r hd ha
      have hd' : x (coord r) ≠ y (coord r) := of_decide_eq_true hd
      have hval : x (coord r) = value r := of_decide_eq_true (Bool.and_eq_true_iff.mp ha).2
      have hn : y (coord r) ≠ value r := fun he => hd' (hval.trans he.symm)
      simp [hn]) (List.finRange D)
  rw [List.length_finRange] at hc
  omega

/-- Adding a point outside a coordinate line forces distance at least two to
one of two points on it. This pure implication uses no finite enumeration. -/
theorem common_line {U V : Type} {x y z : U → V} {i : U}
    (diff : x i ≠ y i) (line : ∀ j, j ≠ i → x j = y j)
    (nearX : ∀ j l, x j ≠ z j → x l ≠ z l → j=l)
    (nearY : ∀ j l, y j ≠ z j → y l ≠ z l → j=l) :
    ∀ j, j ≠ i → z j = x j := by
  classical
  intro j hji
  apply Classical.byContradiction
  intro hz
  have hxj : x j ≠ z j := Ne.symm hz
  have hyj : y j ≠ z j := (line j hji) ▸ hxj
  by_cases he : x i = z i
  · exact hji (nearY j i hyj (fun h => diff (he.trans h.symm)))
  · exact hji (nearX j i hxj he)

private theorem add_row {R X : Type} (rows : List R) (sites : List X)
    (act : X → R → Bool) (r : R) :
    (sites.map (fun x => (r::rows).countP (act x))).sum =
      (sites.map (fun x => rows.countP (act x))).sum + sites.countP (fun x => act x r) := by
  induction sites with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    simp only [List.countP_cons]
    omega

private theorem count_exclusive {R X : Type} (rows : List R) (sites : List X)
    (nd : sites.Nodup) (act : X → R → Bool)
    (unique : ∀ r x y, act x r = true → act y r = true → x=y) :
    (sites.map (fun x => rows.countP (act x))).sum ≤ rows.length := by
  classical
  induction rows with
  | nil => induction sites with
           | nil => simp
           | cons x xs ih => simp_all
  | cons r rows ih =>
    have one : sites.countP (fun x => act x r) ≤ 1 := by
      rw [List.countP_eq_length_filter]
      by_cases h : ∃ z, act z r = true
      · obtain ⟨z,hz⟩ := h
        have sub : sites.filter (fun x => act x r) ⊆ [z] := by
          intro x hx
          simp [unique r x z (List.mem_filter.mp hx).2 hz]
        simpa using (List.filter_sublist.nodup nd).length_le_of_subset sub
      · have hempty : sites.filter (fun x => act x r) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro x _ hh
          exact h ⟨x,hh⟩
        simp [hempty]
    rw [add_row, List.length_cons]
    omega

private theorem sum_lower {X : Type} (sites : List X) (f : X → Nat) (u : Nat)
    (lb : ∀ x, u ≤ f x) : sites.length*u ≤ (sites.map f).sum := by
  induction sites with
  | nil => simp
  | cons x xs ih =>
    have hx := lb x
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul, List.map_cons, List.sum_cons]
    omega

/-- On a line each of b excluded digits needs u varying-coordinate rows. A
varying-coordinate row is active at only one digit. This proves b*u ≤ t,
including the strict capacity loss caused by deleting one of those rows. -/
theorem line_capacity {t b u : Nat} (act : Fin b → Fin t → Bool)
    (unique : ∀ r x y, act x r = true → act y r = true → x=y)
    (need : ∀ x, u ≤ (List.finRange t).countP (act x)) : b*u ≤ t := by
  have lower := sum_lower (List.finRange b) _ u need
  have upper := count_exclusive (List.finRange t) (List.finRange b) (List.nodup_finRange b) act unique
  simpa using Nat.le_trans lower upper

#print axioms two_point
#print axioms common_line
#print axioms line_capacity
end OverfilledFibre

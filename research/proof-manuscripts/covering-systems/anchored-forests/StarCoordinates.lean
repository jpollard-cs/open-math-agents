import ForestFibre

namespace StarCoordinates
open ForestFibre

private def leaf (p a b : Nat) (u : List Nat) (h : u.length≤b) (ha : 0<a) (eq : a+b=p) :
    NodeData := ⟨p,a,ha,u,b,h,[],by simpa using eq⟩

private def makeLeg (c : NodeData) (rs : List Pair) (hr : rs.length+1 ≤ 2*c.a) : Leg :=
  ⟨next c,1,by decide,rs,by simpa [next] using hr⟩

private theorem good_leg {c : NodeData} {e : Leg} {x} (mem : x∈(next c).digits)
    (edge : e∈c.legs) : rem e x ≠ [] := by
  have hh := (List.mem_filter.mp mem)
  have ok : x ∉ banned c := by simpa using hh.2
  intro empty
  apply ok
  apply List.mem_append.mpr
  apply Or.inr
  exact List.mem_flatMap.mpr ⟨e,edge,List.mem_filter.mpr ⟨hh.1,by simp [empty]⟩⟩

private theorem singleton_of {α : Type} {xs : List α} {t : α} (nd : xs.Nodup) (u : xs ≠ [])
    (single : ∀ x ∈ xs, x=t) : xs=[t] := by
  cases xs with
  | nil => contradiction
  | cons x l =>
    have he := single x (by simp)
    subst x
    cases l with
    | nil => rfl
    | cons y rest =>
      have hy := single y (by simp)
      subst y
      simp at nd

private theorem leafmem {p a b} {u : List Nat} {bound ha eq} {rs : List Pair} {hfit}
    {x y : Nat} (hy : y∈rem (makeLeg (leaf p a b u bound ha eq) rs hfit) x) :
    y<p ∧ y∉u ∧ (x,y)∉rs := by
  have hm := List.mem_filter.mp hy
  have hl := List.mem_filter.mp hm.1
  have out : y ∉ hits (makeLeg (leaf p a b u bound ha eq) rs hfit) x := by simpa using hm.2
  refine ⟨List.mem_range.mp hl.1,by simpa [banned,leaf] using hl.2,?_⟩
  intro he
  apply out
  exact List.mem_map.mpr ⟨(x,y),List.mem_filter.mpr ⟨he,by simp⟩,rfl⟩

/-- All arbitrary labels and all deletions: covering the surviving triples with
one marked triple forces all unary and pair row slots at both children to be full. -/
theorem compulsory (u5 u7 : List Nat) (e5 e7 : List Pair)
    (h5 : u5.length≤3) (h7 : u7.length≤5) (f5 : e5.length≤3) (f7 : e7.length≤3)
    (mark : Prop) (i0 j0 k0 : Nat)
    (cover : ∀ i<3, ∀ j<5, ∀ k<7, j∉u5 → k∉u7 → (i,j)∉e5 → (i,k)∉e7 →
      mark ∧ i=i0 ∧ j=j0 ∧ k=k0) :
    mark ∧ u5.length=3 ∧ u7.length=5 ∧ e5.length=3 ∧ e7.length=3 := by
  let c5 := leaf 5 2 3 u5 h5 (by decide) (by decide)
  let c7 := leaf 7 2 5 u7 h7 (by decide) (by decide)
  let l5 := makeLeg c5 e5 (by change e5.length+1≤4; omega)
  let l7 := makeLeg c7 e7 (by change e7.length+1≤4; omega)
  let n : NodeData := ⟨3,1,by decide,[],0,by decide,[l5,l7],by simp [l5,l7,makeLeg]⟩
  have hp5 : Valid l5.child := joinValid c5 (by simp [c5,leaf])
  have hp7 : Valid l7.child := joinValid c7 (by simp [c7,leaf])
  have hlegs : ∀ e ∈ n.legs, Valid e.child := by
    intro e he
    change e ∈ [l5,l7] at he
    rcases (by simpa using he : e=l5 ∨ e=l7) with rfl|rfl
    · exact hp5
    · exact hp7
  have non : (next n).digits ≠ [] := by
    have hl := (joinValid n hlegs).1
    change 1 ≤ (next n).digits.length at hl
    intro h
    simp [h] at hl
  have details {x} (hx : x∈(next n).digits) :
      mark ∧ x=i0 ∧ rem l5 x=[j0] ∧ rem l7 x=[k0] := by
    have a := good_leg hx (show l5∈n.legs by simp [n])
    have b := good_leg hx (show l7∈n.legs by simp [n])
    obtain ⟨y,hy⟩ := List.exists_mem_of_ne_nil _ a
    obtain ⟨z,hz⟩ := List.exists_mem_of_ne_nil _ b
    have cx : x<3 := List.mem_range.mp (List.mem_filter.mp hx).1
    have any {j k} (hj : j∈rem l5 x) (hk : k∈rem l7 x) := by
      have ⟨jlt,ju,je⟩ := leafmem hj
      have ⟨klt,ku,ke⟩ := leafmem hk
      exact cover x cx j jlt k klt ju ku je ke
    have v := any hy hz
    exact ⟨v.1,v.2.1,singleton_of (List.filter_sublist.nodup l5.child.nodup) a
      (fun j hj => (any hj hz).2.2.1),singleton_of (List.filter_sublist.nodup l7.child.nodup) b
      (fun k hk => (any hy hk).2.2.2)⟩
  obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil _ non
  have d := details hx
  have one := singleton_of (next n).nodup non (fun y hy => (details hy).2.1)
  have unique : (next n).uniqueAt x := by
    intro e he
    change e ∈ [l5,l7] at he
    rcases (by simpa using he : e=l5 ∨ e=l7) with rfl|rfl
    · exact ⟨j0,d.2.2.1,by simp [l5,makeLeg,c5,leaf,next]⟩
    · exact ⟨k0,d.2.2.2,by simp [l7,makeLeg,c7,leaf,next]⟩
  have used := root_compulsory n rfl hlegs (d.2.1 ▸ one) unique
  obtain ⟨ue5,uc5⟩ := used.2 l5 (by simp [n])
  obtain ⟨ue7,uc7⟩ := used.2 l7 (by simp [n])
  change e5.length+1=4 at ue5
  change e7.length+1=4 at ue7
  exact ⟨d.1,uc5.1,uc7.1,by omega,by omega⟩

#print axioms compulsory
end StarCoordinates

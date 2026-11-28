import PacketEssential

namespace PacketAssignment
open PacketEssential PacketCoverage

def classes (d : Nat) : List (List Nat) → List (Nat × Int)
  | [] => [(d,0)]
  | [] :: _ => []
  | (c::ns)::rest => List.ofFn (fun i : Fin ns.length =>
      (ns[i.val], (d : Int)*(i.val+1 : Int))) ++ classes c rest

theorem handles {d : Nat} {stages : List (List Nat)} :
    (classes d stages).map Prod.fst = Flat d stages := by
  induction stages generalizing d with
  | nil => rfl
  | cons rows rest ih =>
    cases rows with
    | nil => rfl
    | cons c ns =>
      simp [classes,Flat,List.map_ofFn,Function.comp_def,List.ofFn_getElem,ih]

theorem from_hit {d : Nat} {stages : List (List Nat)} {x : Int} (h : Hit d stages x) :
    ∃ e ∈ classes d stages, (e.1 : Int) ∣ x-e.2 := by
  induction stages generalizing d with
  | nil => exact ⟨(d,0),by simp [classes],by simpa [Hit] using h⟩
  | cons rows rest ih =>
    cases rows with
    | nil => contradiction
    | cons c ns =>
      rcases h with ⟨j,hj,hit⟩|hit
      · exact ⟨_,List.mem_append.mpr (Or.inl (List.mem_ofFn.mpr ⟨⟨j,hj⟩,rfl⟩)),hit⟩
      · obtain ⟨e,he,ht⟩ := ih hit
        exact ⟨e,List.mem_append.mpr (Or.inr he),ht⟩

def residue : List (Nat × Int) → Nat → Int
  | [], _ => 0
  | (m,r)::rs,n => if m=n then r else residue rs n

theorem agree {cs : List (Nat × Int)} (unique : (cs.map Prod.fst).Nodup) {e} (he : e ∈ cs) :
    residue cs e.1 = e.2 := by
  induction cs with
  | nil => contradiction
  | cons c cs ih =>
    obtain ⟨m,r⟩ := c
    rcases List.mem_cons.mp he with rfl|he
    · simp [residue]
    · have hm := (List.nodup_cons.mp unique).1
      have ne : m ≠ e.1 := by
        intro eq
        exact hm (List.mem_map.mpr ⟨e,he,eq.symm⟩)
      simpa [residue,ne] using ih (List.nodup_cons.mp unique).2 he

theorem covers {stages : List (List Nat)} (v : Valid 1 stages = true)
    (nd : (Flat 1 stages).Nodup) :
    ∃ a : Nat → Int, ∀ x : Int, ∃ n ∈ Flat 1 stages, (n : Int) ∣ x - a n := by
  refine ⟨residue (classes 1 stages),?_⟩
  intro x
  obtain ⟨e,he,h⟩ := from_hit (coverage v (Int.one_dvd x))
  refine ⟨e.1,?_,?_⟩
  · rw [← handles]; exact List.mem_map.mpr ⟨e,he,rfl⟩
  · rw [agree (by rwa [handles]) he]; exact h

end PacketAssignment

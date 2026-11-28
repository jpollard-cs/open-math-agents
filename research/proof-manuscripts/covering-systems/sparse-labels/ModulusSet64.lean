import Checked64

namespace Checked64
set_option maxRecDepth 200000
set_option maxHeartbeats 0
open IntegerSubstitution CoveringResidues

theorem indexedFamily (keep : Index64 → Prop) : Covers m64 keep ↔ ∀ i, keep i := by
  constructor
  · rintro ⟨a,h⟩
    have hn : New m4 e5 (fun _ => 35) (fun j => keep (.inl j)) (fun i => keep (.inr i)) := by
      refine ⟨fun j => a (.inl j),fun i => a (.inr i),?_⟩
      intro z
      obtain ⟨i,hi,hz⟩ := h z
      cases i with
      | inl j => exact Or.inl ⟨j,hi,hz⟩
      | inr j => exact Or.inr ⟨j,hi,hz⟩
    obtain ⟨u,v⟩ := (everyDeletion _ _).mp hn
    exact fun | .inl j => u j | .inr i => v i
  · intro h
    obtain ⟨a,r,hz⟩ := (everyDeletion (fun j => keep (.inl j)) (fun i => keep (.inr i))).mpr
      ⟨fun j => h (.inl j),fun i => h (.inr i)⟩
    refine ⟨Sum.elim a r,?_⟩
    intro z
    rcases hz z with ⟨j,hj,hit⟩ | ⟨j,hj,hit⟩
    · exact ⟨.inl j,hj,hit⟩
    · exact ⟨.inr j,hj,hit⟩

-- The choice of residues is an arbitrary function of the modulus, including
-- after a deletion. Quantifying over all integers also includes negatives.
theorem modulusSet (keep : Int → Prop) :
    (∃ a : Int → Int, ∀ z : Int, ∃ d ∈ moduli, keep d ∧ z % d = a d % d) ↔
    ∀ d ∈ moduli, keep d := by
  have sumComplete {X Y : Type} {xs : List X} {ys : List Y}
      (hx : ∀ i, i ∈ xs) (hy : ∀ j, j ∈ ys) (u : Sum X Y) :
      u ∈ xs.map Sum.inl ++ ys.map Sum.inr := by
    cases u with
    | inl i => exact List.mem_append_left _ (List.mem_map.mpr ⟨i,hx i,rfl⟩)
    | inr i => exact List.mem_append_right _ (List.mem_map.mpr ⟨i,hy i,rfl⟩)
  have allIndices : ∀ i, i ∈ indices :=
    sumComplete (sumComplete (sumComplete (sumComplete (sumComplete
      (fun (i : Empty) => Empty.elim i) List.mem_finRange)
      List.mem_finRange) List.mem_finRange) List.mem_finRange) List.mem_finRange
  have tab : ∀ i ∈ indices, ∀ j ∈ indices, m64 i=m64 j → i=j := by decide
  have inj (i j : Index64) := tab i (allIndices i) j (allIndices j)
  classical
  constructor
  · rintro ⟨a,ha⟩
    have indexed : Covers m64 (fun i => keep (m64 i)) := by
      refine ⟨fun i => a (m64 i),?_⟩
      intro z
      obtain ⟨d,hd,hk,he⟩ := ha z
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hd
      exact ⟨i,hk,Int.dvd_iff_emod_eq_zero.mpr (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp he)⟩
    have keeps := (indexedFamily _).mp indexed
    intro d hd
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hd
    exact keeps i
  · intro h
    have hi : ∀ i, keep (m64 i) := fun i => h _ (List.mem_map.mpr ⟨i,allIndices i,rfl⟩)
    obtain ⟨a,ha⟩ := (indexedFamily _).mpr hi
    let f (d : Int) := if q : ∃ i, m64 i=d then a (Classical.choose q) else 0
    have fit (i : Index64) : f (m64 i)=a i := by
      have present : ∃ j, m64 j=m64 i := ⟨i,rfl⟩
      simp only [f,dif_pos present]
      rw [inj _ i (Classical.choose_spec present)]
    refine ⟨f,?_⟩
    intro z
    obtain ⟨i,ki,hit⟩ := ha z
    exact ⟨m64 i,List.mem_map.mpr ⟨i,allIndices i,rfl⟩,ki,by
      rw [fit]
      exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.dvd_iff_emod_eq_zero.mp hit)⟩

theorem validModuli : ∀ d ∈ moduli, 1 < d := by decide
#print axioms modulusSet
#print axioms validModuli
end Checked64

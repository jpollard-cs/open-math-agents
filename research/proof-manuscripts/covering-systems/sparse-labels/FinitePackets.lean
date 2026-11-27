import IntegerSubstitution

namespace FinitePackets
open IntegerSubstitution CoveringResidues

variable {I : Type} [DecidableEq I]

def survivors (all : List I) (j : I) := all.filter (fun i => i != j)

theorem deletionCost {P : Nat} (allRows : List I) (complete : ∀ i, i ∈ allRows) (m : I → Nat)
    (positive : ∀ i, 0 < m i) (period : ∀ i, m i ∣ P)
    (j : I) (r : I → Int)
    (h : ∀ z : Int, ∃ i, i ≠ j ∧ Same (m i) z (r i)) :
    P ≤ ((survivors allRows j).map (fun i => P/m i)).sum := by
  let hits (i : I) := (List.range (P/m i)).map
    (fun q => ((r i) % (m i : Int)).toNat + m i*q)
  have subset : List.range P ⊆ (survivors allRows j).flatMap hits := by
    intro x hx
    have lt := List.mem_range.mp hx
    obtain ⟨i,hij,hit⟩ := h x
    apply List.mem_flatMap.mpr
    refine ⟨i,?_,?_⟩
    · exact List.mem_filter.mpr ⟨complete i, by simpa using hij⟩
    · apply List.mem_map.mpr
      refine ⟨x / m i, List.mem_range.mpr ?_, ?_⟩
      · apply (Nat.div_lt_iff_lt_mul (positive i)).mpr
        simpa [Nat.div_mul_cancel (period i)] using lt
      · have hh := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.dvd_iff_emod_eq_zero.mp hit)
        rw [← Int.natCast_emod] at hh
        have eq : ((r i) % (m i : Int)).toNat = x % m i := by rw [← hh]; rfl
        rw [eq]
        exact Nat.mod_add_div _ _
  have bound := List.Nodup.length_le_of_subset List.nodup_range subset
  simpa [List.length_flatMap,hits] using bound

theorem minimal {P : Nat} (allRows : List I) (complete : ∀ i, i ∈ allRows) (hP : 0<P) (m : I → Nat) (r : I → Int)
    (positive : ∀ i, 0 < m i) (period : ∀ i, m i ∣ P)
    (finiteCover : ∀ x : Fin P, ∃ i, Same (m i) x.val (r i))
    (cost : ∀ j, ((survivors allRows j).map (fun i => P/m i)).sum < P)
    (keep : I → Prop) : Covers (fun i => (m i : Int)) keep ↔ ∀ i, keep i := by
  constructor
  · rintro ⟨a,ha⟩ j
    apply Classical.byContradiction
    intro notkept
    have bad := deletionCost allRows complete m positive period j a (fun x => by
      obtain ⟨i,hi,hit⟩ := ha x
      exact ⟨i,(fun eq => notkept (eq ▸ hi)),hit⟩)
    exact (Nat.not_le.mpr (cost j)) bad
  · intro all
    refine ⟨r,?_⟩
    intro z
    have hn := Int.emod_nonneg z (by omega : (P : Int)≠0)
    let x : Fin P := ⟨(z % P).toNat,(Int.toNat_lt hn).mpr (Int.emod_lt_of_pos _ (by omega))⟩
    obtain ⟨i,u⟩ := finiteCover x
    have hcast : (x.val : Int) = z % P := Int.toNat_of_nonneg hn
    unfold Same at u
    rw [hcast] at u
    have dv := Int.dvd_trans (Int.ofNat_dvd.mpr (period i)) (Int.dvd_self_sub_emod (x:=z) (m:=(P:Int)))
    obtain ⟨a,ha⟩ := dv
    obtain ⟨b,hb⟩ := u
    refine ⟨i,all i,a+b,?_⟩
    change z-r i=(m i : Int)*(a+b)
    rw [Int.mul_add]
    omega
end FinitePackets

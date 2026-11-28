import Std

/-! Coverage over all integers for successive refinements of a single congruence.
The first modulus of a packet is its zero-residue continuation. At the last
stage it contributes the final zero-residue class. No primality is required.
-/
namespace PacketCoverage

def Valid (d : Nat) : List (List Nat) → Bool
  | [] => true
  | [] :: _ => false
  | (c :: ns) :: rest =>
    (c :: ns).all (fun n => n > 0 && d * (ns.length + 1) % n == 0) && Valid c rest

def Hit (d : Nat) : List (List Nat) → Int → Prop
  | [], x => (d : Int) ∣ x
  | [] :: _, _ => False
  | (c :: ns) :: rest, x =>
    (∃ j : Nat, ∃ hj : j < ns.length,
      (ns[j] : Int) ∣ x - (d : Int) * ((j : Int) + 1)) ∨ Hit c rest x

theorem coverage {stages : List (List Nat)} {d : Nat}
    (hv : Valid d stages = true) {x : Int} (hx : (d : Int) ∣ x) :
    Hit d stages x := by
  induction stages generalizing d with
  | nil => exact hx
  | cons rows rest ih =>
    cases rows with
    | nil => simp [Valid] at hv
    | cons c ns =>
      simp only [Valid, Bool.and_eq_true, List.all_eq_true] at hv
      have member (n : Nat) (hn : n ∈ c :: ns) :
          (n : Int) ∣ (d : Int) * (ns.length + 1 : Nat) := by
        have hm := hv.1 n hn
        simp only [beq_iff_eq, decide_eq_true_eq] at hm
        rw [← Int.natCast_mul]
        exact Int.ofNat_dvd.mpr (Nat.dvd_of_mod_eq_zero hm.2)
      obtain ⟨t, ht⟩ := hx
      let r : Nat := ns.length + 1
      have pos : (0 : Int) < r := by dsimp [r]; omega
      let i := (t % r).toNat
      have hn : 0 ≤ t % r := Int.emod_nonneg _ (by omega)
      have hi : i < r := (Int.toNat_lt hn).mpr (Int.emod_lt_of_pos _ pos)
      have hcast : (i : Int) = t % r := Int.toNat_of_nonneg hn
      have delta : t - (i : Int) = (r : Int) * (t / r) := by
        rw [hcast]
        have := Int.emod_add_mul_ediv t (r : Int)
        omega
      have mult : (d : Int) * (r : Int) ∣ x - (d : Int) * (i : Int) := by
        refine ⟨t / r, ?_⟩
        rw [ht, ← Int.mul_sub, delta, Int.mul_assoc]
      cases e : i with
      | zero =>
        right
        apply ih hv.2
        have h := Int.dvd_trans (member c (by simp)) mult
        simpa [e] using h
      | succ j =>
        left
        have hj : j < ns.length := by dsimp [r] at hi; omega
        refine ⟨j,hj,?_⟩
        have h := Int.dvd_trans (member ns[j] (by simp [List.getElem_mem hj])) mult
        simpa [e] using h

#print axioms coverage
end PacketCoverage

namespace PacketCoverage
def unused (seen : Nat) : List Nat → Bool
  | [] => true
  | n :: ns => !(seen.testBit n) && unused (seen ||| (2^n)) ns

theorem unused_sound {seen : Nat} {xs : List Nat} (h : unused seen xs = true) :
    xs.Nodup ∧ ∀ n ∈ xs, seen.testBit n = false := by
  induction xs generalizing seen with
  | nil => simp
  | cons n ns ih =>
    simp only [unused, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hn, hm⟩ := ih h.2
    constructor
    · apply List.nodup_cons.mpr
      refine ⟨?_,hn⟩
      intro a
      have H := hm n a
      simpa using H
    · intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact h.1
      · have H := hm k hk
        rw [Nat.testBit_or, Bool.or_eq_false_iff] at H
        exact H.1
end PacketCoverage

import BinarySeparator

/- Codex (OpenAI). The minimum number of common feasible cells under column bijections.
   Pairing constructs the multiset of paired columns one column at a time. -/
namespace BinarySeparator.MinimumOverlap
open BinarySeparator

inductive Mask | empty | top | bottom | both deriving DecidableEq, Repr
open Mask

def zero : Counts := ⟨0,0,0,0⟩
def add : Mask → Counts → Counts
  | .empty, a => {a with empty := a.empty+1}
  | .top, a => {a with top := a.top+1}
  | .bottom, a => {a with bottom := a.bottom+1}
  | .both, a => {a with both := a.both+1}

def sub : Mask → Counts → Counts
  | .empty, a => {a with empty := a.empty-1}
  | .top, a => {a with top := a.top-1}
  | .bottom, a => {a with bottom := a.bottom-1}
  | .both, a => {a with both := a.both-1}

def size : Mask → Counts → Nat
  | .empty, a => a.empty
  | .top, a => a.top
  | .bottom, a => a.bottom
  | .both, a => a.both

def cost : Mask → Mask → Nat
  | .empty, _ | _, .empty | .top, .bottom | .bottom, .top => 0
  | .both, .both => 2
  | _, _ => 1

inductive Pairing : Counts → Counts → Nat → Prop
  | nil : Pairing zero zero 0
  | append (u v) {a b n} : Pairing a b n → Pairing (add u a) (add v b) (n+cost u v)

/-- Five nontrivial linear inequalities (the sixth bound, nonnegativity, is automatic).
    The last inequality adds the two coordinate demands before taking positive parts. -/
def Budget (a b : Counts) (n : Nat) : Prop :=
  a.both ≤ b.empty+n ∧ b.both ≤ a.empty+n ∧
  a.top+a.both + b.top+b.both ≤ a.total+n ∧
  a.bottom+a.both + b.bottom+b.both ≤ a.total+n ∧
  a.top+a.bottom+2*a.both + b.top+b.bottom+2*b.both ≤ 2*a.total+n

private def Fit (u v : Mask) (a b : Counts) (n : Nat) : Prop :=
  0 < size v b ∧ cost u v ≤ n ∧ Budget a (sub v b) (n-cost u v)

set_option maxHeartbeats 2000000 in
private theorem step (u : Mask) (a b : Counts) (n : Nat)
    (eqs : (add u a).total = b.total) (h : Budget (add u a) b n) :
    Fit u empty a b n ∨ Fit u top a b n ∨ Fit u bottom a b n ∨ Fit u both a b n := by
  cases u <;> simp [Fit, Budget, Counts.total, size, sub, add, cost] at * <;> omega

private theorem restore (v : Mask) (b : Counts) (hp : 0 < size v b) :
    add v (sub v b) = b := by
  cases b with
  | mk e t d f =>
    cases v <;> simp [size] at hp <;> simp [add, sub] <;> omega

private theorem total_add (v : Mask) (a : Counts) : (add v a).total = a.total+1 := by
  cases v <;> simp [add, Counts.total] <;> omega

private theorem pick (a : Counts) (hp : 0 < a.total) : ∃ u a', a = add u a' := by
  rcases a with ⟨e,t,d,f⟩
  cases e with
  | succ e => exact ⟨empty, ⟨e,t,d,f⟩, rfl⟩
  | zero =>
    cases t with
    | succ t => exact ⟨top, ⟨0,t,d,f⟩, rfl⟩
    | zero =>
      cases d with
      | succ d => exact ⟨bottom, ⟨0,0,d,f⟩, rfl⟩
      | zero =>
        cases f with
        | succ f => exact ⟨both, ⟨0,0,0,f⟩, rfl⟩
        | zero => simp [Counts.total] at hp

private theorem is_zero (a : Counts) (h : a.total = 0) : a = zero := by
  rcases a with ⟨e,t,d,f⟩
  simp [Counts.total] at h
  obtain ⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩ := h
  rfl

theorem budget_suffices (a b : Counts) (n : Nat) (balanced : a.total = b.total)
    (h : Budget a b n) : ∃ m ≤ n, Pairing a b m := by
  induction ht : a.total generalizing a b n with
  | zero =>
    have hb : b.total = 0 := by omega
    rw [is_zero a ht, is_zero b hb]
    exact ⟨0, Nat.zero_le _, Pairing.nil⟩
  | succ t ih =>
    obtain ⟨u,a',rfl⟩ := pick a (by omega)
    have ht' := total_add u a'
    have hf := step u a' b n balanced h
    have useFit : ∀ v, Fit u v a' b n → ∃ m ≤ n, Pairing (add u a') b m := by
      intro v hv
      obtain ⟨hp,hc,hbound⟩ := hv
      have hb := restore v b hp
      have ht'' := total_add v (sub v b)
      rw [hb] at ht''
      obtain ⟨m, hm, hpair⟩ := ih a' (sub v b) (n-cost u v) (by omega) hbound (by omega)
      exact ⟨m+cost u v, by omega, hb ▸ Pairing.append u v hpair⟩
    rcases hf with he|htop|hbottom|hboth
    · exact useFit empty he
    · exact useFit top htop
    · exact useFit bottom hbottom
    · exact useFit both hboth

theorem budget_needed {a b m} (h : Pairing a b m) : Budget a b m := by
  induction h with
  | nil => simp [Budget, zero, Counts.total]
  | append u v h ih =>
    cases u <;> cases v <;> simp [Budget, Counts.total, add, cost] at * <;> omega

theorem minimum_overlap_iff (a b : Counts) (n : Nat) (balanced : a.total = b.total) :
    (∃ m ≤ n, Pairing a b m) ↔ Budget a b n := by
  constructor
  · rintro ⟨m,hm,hp⟩
    have hb := budget_needed hp
    unfold Budget at *
    omega
  · exact budget_suffices a b n balanced

#print axioms minimum_overlap_iff
end BinarySeparator.MinimumOverlap

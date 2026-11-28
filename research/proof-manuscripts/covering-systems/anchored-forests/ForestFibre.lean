import Std

/-! Bottom-up arithmetic for rooted congruence trees. A profile lists the digits
with a possible continuation, plus the predicate for a unique continuation.
Rows that were deleted are absent. Arbitrary row labels and repeated labels
are allowed. No primality assumption is needed for this coordinate lemma. -/
namespace ForestFibre
abbrev Pair := Nat × Nat

structure Profile where
  digits : List Nat
  nodup : digits.Nodup
  uniqueAt : Nat → Prop
  target : Nat
  target_pos : 0 < target
  allUsed : Prop

def Valid (c : Profile) : Prop :=
  c.target ≤ c.digits.length ∧
  (c.digits.length = c.target → ∀ x ∈ c.digits, c.uniqueAt x → c.allUsed)

structure Leg where
  child : Profile
  v : Nat
  vp : 0 < v
  rows : List Pair
  budget : rows.length + 1 ≤ (v+1)*child.target

def hits (e : Leg) (x : Nat) : List Nat :=
  (e.rows.filter (fun r => r.1 == x)).map Prod.snd
def rem (e : Leg) (x : Nat) : List Nat :=
  e.child.digits.filter (fun y => !((hits e x).contains y))
def blocked (p : Nat) (e : Leg) : List Nat :=
  (List.range p).filter (fun x => (rem e x).isEmpty)

theorem pointCost (e : Leg) (x : Nat) :
    e.child.digits.length ≤ (rem e x).length + (hits e x).length := by
  have sub : e.child.digits ⊆ rem e x ++ hits e x := by
    intro y hy
    by_cases h : y ∈ hits e x
    · exact List.mem_append.mpr (Or.inr h)
    · exact List.mem_append.mpr (Or.inl (List.mem_filter.mpr ⟨hy,by simpa using h⟩))
  simpa using e.child.nodup.length_le_of_subset sub

private theorem addRow (xs : List Nat) (r : Pair) (rs : List Pair) :
    (xs.map (fun x => ((r::rs).filter (fun t => t.1 == x)).length)).sum =
    (xs.map (fun x => (rs.filter (fun t => t.1 == x)).length)).sum +
      xs.countP (fun x => r.1 == x) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    by_cases h : r.1 = x <;> simp [h] <;> omega

private theorem sumHits (xs : List Nat) (nd : xs.Nodup) (e : Leg) :
    (xs.map (hits e · |>.length)).sum ≤ e.rows.length := by
  have aux (rs : List Pair) :
      (xs.map (fun x => (rs.filter (fun t => t.1 == x)).length)).sum ≤ rs.length := by
    induction rs with
    | nil =>
      suffices h : (xs.map (fun _ => 0)).sum = (0:Nat) by simpa using h
      induction xs with
      | nil => simp
      | cons x xs ih => simp_all
    | cons r rs ih =>
      have one : xs.countP (fun x => r.1 == x) ≤ 1 := by
        rw [List.countP_eq_length_filter]
        have sub : xs.filter (fun x => r.1 == x) ⊆ [r.1] := by
          intro x hx
          have h := (List.mem_filter.mp hx).2
          simpa using (beq_iff_eq.mp h).symm
        simpa using (List.filter_sublist.nodup nd).length_le_of_subset sub
      rw [addRow, List.length_cons]
      omega
  simpa [hits] using aux e.rows

private theorem sumLower (xs : List Nat) (e : Leg) (m : Nat)
    (need : ∀ x ∈ xs, m ≤ (hits e x).length) :
    xs.length*m ≤ (xs.map (hits e · |>.length)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h := need x (by simp)
    have hi := ih (fun y hy => need y (by simp [hy]))
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul, List.map_cons, List.sum_cons]
    omega

private theorem noRem {p x} {e : Leg} (h : x ∈ blocked p e) : rem e x = [] := by
  have hm := (List.mem_filter.mp h).2
  simpa using hm

private theorem costBlocked (p : Nat) (e : Leg) :
    (blocked p e).length*e.child.digits.length ≤
      ((blocked p e).map (hits e · |>.length)).sum := by
  apply sumLower
  intro x hx
  simpa [noRem hx] using pointCost e x

theorem capacity {p : Nat} {e : Leg} (hc : Valid e.child) :
    (blocked p e).length ≤ e.v := by
  have fuel := Nat.le_trans (costBlocked p e) (sumHits _ (List.filter_sublist.nodup List.nodup_range) e)
  have hp := e.budget
  apply Nat.le_of_not_gt
  intro h
  have bad := Nat.mul_le_mul (show e.v+1 ≤ (blocked p e).length by omega) hc.1
  omega

/-- When a child eliminates its full quota and has just one continuation at a
different parent digit, it uses every edge row and its projection is minimal. -/
theorem tightLeg {p x y : Nat} {e : Leg} (hc : Valid e.child)
    (full : (blocked p e).length=e.v) (single : rem e x=[y]) (unique : e.child.uniqueAt y) :
    e.rows.length+1=(e.v+1)*e.child.target ∧ e.child.allUsed := by
  have nx : x ∉ blocked p e := by
    intro h
    have := noRem h
    simp_all
  have nd : (x::blocked p e).Nodup :=
    List.nodup_cons.mpr ⟨nx,List.filter_sublist.nodup List.nodup_range⟩
  have sum := sumHits _ nd e
  simp only [List.map_cons,List.sum_cons] at sum
  have base := costBlocked p e
  rw [full] at base
  have atx := pointCost e x
  rw [single] at atx
  simp only [List.length_cons,List.length_nil] at atx
  have lo : (e.v+1)*e.child.digits.length ≤ e.rows.length+1 := by
    rw [Nat.add_mul,Nat.one_mul]; omega
  have bounds := e.budget
  have middle := Nat.mul_le_mul_left (e.v+1) hc.1
  have eq : (e.v+1)*e.child.digits.length=(e.v+1)*e.child.target := by omega
  have mc := Nat.eq_of_mul_eq_mul_left (show 0<e.v+1 by omega) eq
  have mem : y ∈ e.child.digits := by
    have h : y ∈ rem e x := by simp [single]
    exact (List.mem_filter.mp h).1
  exact ⟨by omega,hc.2 mc y mem unique⟩


structure NodeData where
  p : Nat
  a : Nat
  positive : 0<a
  unary : List Nat
  unaryBudget : Nat
  unaryFit : unary.length ≤ unaryBudget
  legs : List Leg
  split : a+unaryBudget+(legs.map Leg.v).sum=p

def banned (n : NodeData) := n.unary ++ n.legs.flatMap (blocked n.p)
def next (n : NodeData) : Profile where
  digits := (List.range n.p).filter (fun x => !(banned n).contains x)
  nodup := List.filter_sublist.nodup List.nodup_range
  target := n.a
  target_pos := n.positive
  uniqueAt x := ∀ e ∈ n.legs, ∃ y, rem e x = [y] ∧ e.child.uniqueAt y
  allUsed := n.unary.length=n.unaryBudget ∧ ∀ e ∈ n.legs,
      e.rows.length+1=(e.v+1)*e.child.target ∧ e.child.allUsed

private theorem sum_bounds {α : Type} (xs : List α) (f g : α → Nat)
    (bound : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum ∧
      ((xs.map f).sum=(xs.map g).sum → ∀ x ∈ xs, f x=g x) := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    have hy := bound y (by simp)
    obtain ⟨hb,he⟩ := ih (fun x hx => bound x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons]
    refine ⟨by omega,?_⟩
    intro eq x hx
    rcases List.mem_cons.mp hx with rfl|ht
    · omega
    · exact he (by omega) x ht

/-- Compose the already proved subtree invariants on arbitrary finite lists of
children. Repeated applications prove the invariant on any finite rooted tree. -/
theorem joinValid (n : NodeData) (hc : ∀ e ∈ n.legs, Valid e.child) : Valid (next n) := by
  have sub : List.range n.p ⊆ (next n).digits ++ banned n := by
    intro x hx
    by_cases h : x ∈ banned n
    · exact List.mem_append.mpr (Or.inr h)
    · exact List.mem_append.mpr (Or.inl (List.mem_filter.mpr ⟨hx,by simpa using h⟩))
  have cover := List.nodup_range.length_le_of_subset sub
  simp only [List.length_range, List.length_append, banned, List.length_flatMap] at cover
  obtain ⟨cap,each⟩ := sum_bounds n.legs (fun e => (blocked n.p e).length) Leg.v
    (fun e h => capacity (hc e h))
  have quota := n.split
  have un := n.unaryFit
  change n.a ≤ (next n).digits.length ∧ _
  refine ⟨by omega,?_⟩
  intro eq x _ single
  change (next n).digits.length = n.a at eq
  have alls : (n.legs.map (fun e => (blocked n.p e).length)).sum=(n.legs.map Leg.v).sum := by omega
  refine ⟨by omega,?_⟩
  intro e he
  obtain ⟨y,hy,sy⟩ := single e he
  exact tightLeg (hc e he) (each alls e he) hy sy

theorem root_compulsory (n : NodeData) (hroot : n.a=1) (hc : ∀ e ∈ n.legs, Valid e.child)
    (one : (next n).digits=[x]) (unique : (next n).uniqueAt x) : (next n).allUsed := by
  apply (joinValid n hc).2 _ x _ unique
  · change (next n).digits.length=n.a
    rw [one,hroot]
    rfl
  · simp [one]

#print axioms joinValid
#print axioms root_compulsory
end ForestFibre

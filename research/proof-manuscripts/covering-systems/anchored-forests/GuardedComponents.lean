import Std

/-!
Two successive component tests. Every row may be reassigned or omitted.
An outer guard on each later row can have an arbitrary set of active old
points. For the converse, its label must be able to target any given old point.
-/
namespace GuardedComponents

abbrev Placement {I : Type} (V : I → Type) := (i : I) → Option (V i)

def AllUsed {I : Type} {V : I → Type} (f : Placement V) : Prop :=
  ∀ i, f i ≠ none

def Rigid {X : Type} (holes : X → Prop) (used : Prop) : Prop :=
  (∃ x, holes x) ∧ ∀ z, (∀ x, holes x → x = z) → used

def Single {X : Type} (holes : X → Prop) (z : X) : Prop :=
  ∀ x, holes x ↔ x = z

variable {X Y I J : Type} {A : I → Type} {B G : J → Type}
variable (earlier : Placement A → X → Prop) (later : Placement B → Y → Prop)
variable (guard : (j : J) → G j → X → Prop)

noncomputable def active (h : Placement (fun j => G j × B j)) (x : X) : Placement B :=
  fun j => (h j).bind fun a => open Classical in if guard j a.1 x then some a.2 else none

def align (pick : (j : J) → G j) (g : Placement B) : Placement (fun j => G j × B j) :=
  fun j => (g j).map fun b => (pick j, b)

theorem active_align (x : X) (pick : (j : J) → G j) (hp : ∀ j, guard j (pick j) x)
    (g : Placement B) : active guard (align pick g) x = g := by
  classical
  funext j
  cases eq : g j <;> simp [active, align, eq, hp]

theorem used_of_active {h : Placement (fun j => G j × B j)} {x : X}
    (ha : AllUsed (active guard h x)) : AllUsed h := by
  intro j hj
  apply ha j
  simp [active, hj]

theorem used_of_align {pick : (j : J) → G j} {g : Placement B}
    (ha : AllUsed (align pick g)) : AllUsed g := by
  intro j hj
  apply ha j
  simp [align, hj]

def joint (f : Placement A) (h : Placement (fun j => G j × B j)) (z : X × Y) : Prop :=
  earlier f z.1 ∧ later (active guard h z.1) z.2

theorem compose
    (he : ∀ f, Rigid (earlier f) (AllUsed f))
    (hl : ∀ g, Rigid (later g) (AllUsed g))
    (f : Placement A) (h : Placement (fun j => G j × B j)) :
    Rigid (joint earlier later guard f h) (AllUsed f ∧ AllUsed h) := by
  obtain ⟨x, hx⟩ := (he f).1
  obtain ⟨y, hy⟩ := (hl (active guard h x)).1
  refine ⟨⟨(x,y), hx, hy⟩, ?_⟩
  intro z hz
  constructor
  · apply (he f).2 z.1
    intro u hu
    obtain ⟨v, hv⟩ := (hl (active guard h u)).1
    exact congrArg Prod.fst (hz (u,v) ⟨hu,hv⟩)
  · apply used_of_active (guard := guard) (x := x)
    apply (hl (active guard h x)).2 z.2
    intro v hv
    exact congrArg Prod.snd (hz (x,v) ⟨hx,hv⟩)

theorem exact_factorization
    (xe : X) (yl : Y)
    (witnessE : ∃ f, Single (earlier f) xe)
    (witnessL : ∃ g, Single (later g) yl)
    (target : ∀ (x : X) (j : J), ∃ a, guard j a x) :
    (∀ f h, Rigid (joint earlier later guard f h) (AllUsed f ∧ AllUsed h)) ↔
    (∀ f, Rigid (earlier f) (AllUsed f)) ∧ (∀ g, Rigid (later g) (AllUsed g)) := by
  classical
  constructor
  · intro whole
    obtain ⟨f₀, hf₀⟩ := witnessE
    obtain ⟨g₀, hg₀⟩ := witnessL
    let pick (x : X) (j : J) := Classical.choose (target x j)
    have good (x : X) (j : J) : guard j (pick x j) x :=
      Classical.choose_spec (target x j)
    constructor
    · intro f
      obtain ⟨w, hw⟩ := (whole f (align (pick xe) g₀)).1
      refine ⟨⟨w.1, hw.1⟩, ?_⟩
      intro x only
      apply ((whole f (align (pick x) g₀)).2 (x,yl) ?_).1
      rintro ⟨u,v⟩ ⟨hu,hv⟩
      change earlier f u at hu
      have eq := only u hu
      subst u
      change later (active guard (align (pick x) g₀) x) v at hv
      rw [active_align guard x (pick x) (good x)] at hv
      exact Prod.ext rfl ((hg₀ v).mp hv)
    · intro g
      let h := align (pick xe) g
      have pull (u : X) (v : Y) (hw : joint earlier later guard f₀ h (u,v)) :
          u = xe ∧ later g v := by
        obtain ⟨hu,hv⟩ := hw
        have eq := (hf₀ u).mp hu
        subst u
        change later (active guard (align (pick xe) g) xe) v at hv
        rw [active_align guard xe (pick xe) (good xe)] at hv
        exact ⟨rfl,hv⟩
      obtain ⟨⟨u,v⟩,hw⟩ := (whole f₀ h).1
      refine ⟨⟨v,(pull u v hw).2⟩, ?_⟩
      intro y only
      apply used_of_align (pick := pick xe)
      apply ((whole f₀ h).2 (xe,y) ?_).2
      rintro ⟨u',v'⟩ hw'
      obtain ⟨hu,hv⟩ := pull u' v' hw'
      exact Prod.ext hu (only v' hv)
  · rintro ⟨he,hl⟩
    exact compose earlier later guard he hl

#print axioms compose
#print axioms exact_factorization
end GuardedComponents

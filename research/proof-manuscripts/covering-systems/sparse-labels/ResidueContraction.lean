import Std

/-! Arithmetic interface for the contraction of the old-coordinate
congruences. The lcm is specified by its universal divisibility property.
Integer Bezout coefficients give unrestricted interpolation of two residues. -/
namespace CoveringResidues
variable {I : Type}

def Same (m a b : Int) := m ∣ a-b

theorem contraction (e : I → Int) (d : Int)
    (lcmSpec : ∀ z, (∀ i, e i ∣ z) ↔ d ∣ z) (o : I → Int) :
    ∃ v, ∀ x, (∀ i, Same (e i) x (o i)) → Same d x v := by
  classical
  by_cases h : ∃ u, ∀ i, Same (e i) u (o i)
  · obtain ⟨u,hu⟩ := h
    refine ⟨u,?_⟩
    intro x hx
    apply (lcmSpec _).mp
    intro i
    obtain ⟨a,ha⟩ := hx i
    obtain ⟨b,hb⟩ := hu i
    refine ⟨a-b,?_⟩
    rw [Int.mul_sub]
    omega
  · exact ⟨0, fun x hx => False.elim (h ⟨x,hx⟩)⟩

theorem lift (e : I → Int) (d : Int)
    (lcmSpec : ∀ z, (∀ i, e i ∣ z) ↔ d ∣ z) (v : Int) :
    ∃ o : I → Int, ∀ x, Same d x v → ∀ i, Same (e i) x (o i) := by
  exact ⟨fun _ => v, fun x hx => (lcmSpec (x-v)).mpr hx⟩

theorem interpolate (l n s t : Int) (bezout : l*s+n*t=1) (x y : Int) :
    ∃ z, Same l z x ∧ Same n z y := by
  refine ⟨x + l * (s*(y-x)), ⟨s*(y-x),by omega⟩, ⟨t*(x-y),?_⟩⟩
  have h := congrArg (fun w : Int => w*(y-x)) bezout
  grind

theorem coprimeProduct (e b s t : Int) (bezout : e*s+b*t=1) (z : Int) :
    e*b ∣ z ↔ e ∣ z ∧ b ∣ z := by
  constructor
  · rintro ⟨w,hw⟩
    exact ⟨⟨b*w,by grind⟩,⟨e*w,by grind⟩⟩
  · rintro ⟨⟨i,hi⟩,⟨j,hj⟩⟩
    refine ⟨s*j+t*i,?_⟩
    have h := congrArg (fun w : Int => w*z) bezout
    grind

#print axioms contraction
#print axioms lift
#print axioms interpolate
#print axioms coprimeProduct
end CoveringResidues

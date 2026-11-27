import IndexedDecisions
import Chain
import FinitePackets
namespace Checked21
open IntegerSubstitution CoveringResidues CoveringChain
set_option maxHeartbeats 0
set_option maxRecDepth 200000
local instance (m a b : Int) : Decidable (Same m a b) :=
  inferInstanceAs (Decidable (m ∣ a-b))

private theorem completeOption {n : Nat} (i : Option (Fin n)) :
    i ∈ none :: (List.finRange n).map some := by
  cases i with
  | none => simp
  | some j => simp [List.mem_finRange]

def m0 : Empty → Int := fun _ => 1
abbrev K0 := Empty
theorem core0 (ko : Empty → Prop) (u : Prop) : Old m0 1 ko u ↔ (∀ j,ko j) ∧ u := CoveringChain.seed ko u


abbrev J1 := Fin 4
abbrev K1 := Sum K0 J1
def e1 (i : Option J1) : Int := i.elim 1 (fun j => #[1, 1, 1, 1][j.val]!)
def b1 (i : Option J1) : Nat := i.elim 16 (fun j => #[2, 4, 8, 16][j.val]!)
def r1 (i : Option J1) : Int := i.elim 0 (fun j => #[1, 2, 4, 8][j.val]!)
def m1 : K1 → Int := Sum.elim m0 (fun j => e1 (some j)*b1 (some j))
theorem inner1 (use : Option J1 → Prop) : Covers (fun j => (b1 j : Int)) use ↔ ∀ j,use j :=
  FinitePackets.minimal (none :: (List.finRange 4).map some) completeOption (P:=16) (by decide)
    b1 r1 (by decide) (by decide) (by decide) (by decide) use
theorem core1 (ko : K1 → Prop) (u : Prop) :
    Old m1 16 ko u ↔ (∀ j,ko j) ∧ u := by
  apply stage m0 e1 (fun j => (b1 j : Int))
  exact IntegerSubstitution.irreducible m0 1 e1 (fun j => (b1 j : Int)) 1 16 1 (0)
    (by decide) (by decide) (by decide) (by decide)
    (lcmOfLast 1 e1 rfl (by decide)) core0 inner1


abbrev J2 := Fin 2
abbrev K2 := Sum K1 J2
def e2 (i : Option J2) : Int := i.elim 16 (fun j => #[1, 2][j.val]!)
def b2 (i : Option J2) : Nat := i.elim 3 (fun j => #[3, 3][j.val]!)
def r2 (i : Option J2) : Int := i.elim 0 (fun j => #[1, 2][j.val]!)
def m2 : K2 → Int := Sum.elim m1 (fun j => e2 (some j)*b2 (some j))
theorem inner2 (use : Option J2 → Prop) : Covers (fun j => (b2 j : Int)) use ↔ ∀ j,use j :=
  FinitePackets.minimal (none :: (List.finRange 2).map some) completeOption (P:=3) (by decide)
    b2 r2 (by decide) (by decide) (by decide) (by decide) use
theorem core2 (ko : K2 → Prop) (u : Prop) :
    Old m2 48 ko u ↔ (∀ j,ko j) ∧ u := by
  apply stage m1 e2 (fun j => (b2 j : Int))
  exact IntegerSubstitution.irreducible m1 16 e2 (fun j => (b2 j : Int)) 16 3 1 (-5)
    (by decide) (by decide) (by decide) (by decide)
    (lcmOfLast 16 e2 rfl (by decide)) core1 inner2


abbrev J3 := Fin 4
abbrev K3 := Sum K2 J3
def e3 (i : Option J3) : Int := i.elim 48 (fun j => #[1, 2, 3, 4][j.val]!)
def b3 (i : Option J3) : Nat := i.elim 5 (fun j => #[5, 5, 5, 5][j.val]!)
def r3 (i : Option J3) : Int := i.elim 0 (fun j => #[1, 2, 3, 4][j.val]!)
def m3 : K3 → Int := Sum.elim m2 (fun j => e3 (some j)*b3 (some j))
theorem inner3 (use : Option J3 → Prop) : Covers (fun j => (b3 j : Int)) use ↔ ∀ j,use j :=
  FinitePackets.minimal (none :: (List.finRange 4).map some) completeOption (P:=5) (by decide)
    b3 r3 (by decide) (by decide) (by decide) (by decide) use
theorem core3 (ko : K3 → Prop) (u : Prop) :
    Old m3 240 ko u ↔ (∀ j,ko j) ∧ u := by
  apply stage m2 e3 (fun j => (b3 j : Int))
  exact IntegerSubstitution.irreducible m2 48 e3 (fun j => (b3 j : Int)) 48 5 2 (-19)
    (by decide) (by decide) (by decide) (by decide)
    (lcmOfLast 48 e3 rfl (by decide)) core2 inner3


def term (i : Fin 11) : Int := #[16, 3, 5, 1, 2, 4, 6, 8, 10, 12, 15][i.val]!
theorem lastLcm (z : Int) : (∀ i, term i ∣ z) ↔ 240 ∣ z := by
  constructor
  · intro h
    have h16 : (16:Int) ∣ z := h ⟨0,by decide⟩
    have h3 : (3:Int) ∣ z := h ⟨1,by decide⟩
    have h5 : (5:Int) ∣ z := h ⟨2,by decide⟩
    omega
  · intro h i
    have all : ∀ i, term i ∣ 240 := by decide
    exact Int.dvd_trans (all i) h
theorem finalPacket (use : Fin 11 → Prop) :
    Covers (fun _ : Fin 11 => 11) use ↔ ∀ j,use j :=
  FinitePackets.minimal (List.finRange 11) List.mem_finRange (P:=11) (by decide)
    (fun _ => 11) (fun i => (i.val:Int)) (by decide) (by decide) (by decide) (by decide) use
theorem everyDeletion (ko : K3 → Prop) (kn : Fin 11 → Prop) :
    New m3 term (fun _ => 11) ko kn ↔ (∀ j,ko j) ∧ (∀ i,kn i) :=
  IntegerSubstitution.irreducible m3 240 term (fun _ => 11) 240 11 5 (-109) (by decide)
    (by decide) (by decide) (by decide) lastLcm core3 finalPacket ko kn
abbrev Index21 := Sum K3 (Fin 11)
def m21 : Index21 → Int := Sum.elim m3 (fun j => term j*11)
def all0 : List K0 := []

def all1 : List K1 := all0.map Sum.inl ++ (List.finRange _).map Sum.inr
def all2 : List K2 := all1.map Sum.inl ++ (List.finRange _).map Sum.inr
def all3 : List K3 := all2.map Sum.inl ++ (List.finRange _).map Sum.inr
def indices : List Index21 := all3.map Sum.inl ++ (List.finRange _).map Sum.inr
def moduli : List Int := indices.map m21
theorem sizeAndMax : moduli.length=21 ∧ moduli.Nodup ∧ moduli.max? = some 176 := by decide
#print axioms everyDeletion
#print axioms sizeAndMax
end Checked21

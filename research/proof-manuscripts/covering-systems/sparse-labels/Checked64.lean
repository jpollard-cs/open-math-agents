import IndexedDecisions
import Chain
import FinitePackets
namespace Checked64
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


abbrev J1 := Fin 3
abbrev K1 := Sum K0 J1
def e1 (i : Option J1) : Int := i.elim 1 (fun j => #[1, 1, 1][j.val]!)
def b1 (i : Option J1) : Nat := i.elim 8 (fun j => #[2, 4, 8][j.val]!)
def r1 (i : Option J1) : Int := i.elim 0 (fun j => #[1, 2, 4][j.val]!)
def m1 : K1 → Int := Sum.elim m0 (fun j => e1 (some j)*b1 (some j))
theorem inner1 (use : Option J1 → Prop) : Covers (fun j => (b1 j : Int)) use ↔ ∀ j,use j :=
  FinitePackets.minimal (none :: (List.finRange 3).map some) completeOption (P:=8) (by decide)
    b1 r1 (by decide) (by decide) (by decide) (by decide) use
theorem core1 (ko : K1 → Prop) (u : Prop) :
    Old m1 8 ko u ↔ (∀ j,ko j) ∧ u := by
  apply stage m0 e1 (fun j => (b1 j : Int))
  exact IntegerSubstitution.irreducible m0 1 e1 (fun j => (b1 j : Int)) 1 8 1 (0)
    (by decide) (by decide) (by decide) (by decide)
    (lcmOfLast 1 e1 rfl (by decide)) core0 inner1


abbrev J2 := Fin 4
abbrev K2 := Sum K1 J2
def e2 (i : Option J2) : Int := i.elim 8 (fun j => #[1, 2, 1, 2][j.val]!)
def b2 (i : Option J2) : Nat := i.elim 9 (fun j => #[3, 3, 9, 9][j.val]!)
def r2 (i : Option J2) : Int := i.elim 0 (fun j => #[1, 2, 3, 6][j.val]!)
def m2 : K2 → Int := Sum.elim m1 (fun j => e2 (some j)*b2 (some j))
theorem inner2 (use : Option J2 → Prop) : Covers (fun j => (b2 j : Int)) use ↔ ∀ j,use j :=
  FinitePackets.minimal (none :: (List.finRange 4).map some) completeOption (P:=9) (by decide)
    b2 r2 (by decide) (by decide) (by decide) (by decide) use
theorem core2 (ko : K2 → Prop) (u : Prop) :
    Old m2 72 ko u ↔ (∀ j,ko j) ∧ u := by
  apply stage m1 e2 (fun j => (b2 j : Int))
  exact IntegerSubstitution.irreducible m1 8 e2 (fun j => (b2 j : Int)) 8 9 8 (-7)
    (by decide) (by decide) (by decide) (by decide)
    (lcmOfLast 8 e2 rfl (by decide)) core1 inner2


abbrev J3 := Fin 10
abbrev K3 := Sum K2 J3
def e3 (i : Option J3) : Int := i.elim 72 (fun j => #[1, 2, 3, 4, 6, 8, 9, 12, 18, 24][j.val]!)
def b3 (i : Option J3) : Nat := i.elim 11 (fun j => #[11, 11, 11, 11, 11, 11, 11, 11, 11, 11][j.val]!)
def r3 (i : Option J3) : Int := i.elim 0 (fun j => #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10][j.val]!)
def m3 : K3 → Int := Sum.elim m2 (fun j => e3 (some j)*b3 (some j))
theorem inner3 (use : Option J3 → Prop) : Covers (fun j => (b3 j : Int)) use ↔ ∀ j,use j :=
  FinitePackets.minimal (none :: (List.finRange 10).map some) completeOption (P:=11) (by decide)
    b3 r3 (by decide) (by decide) (by decide) (by decide) use
theorem core3 (ko : K3 → Prop) (u : Prop) :
    Old m3 792 ko u ↔ (∀ j,ko j) ∧ u := by
  apply stage m2 e3 (fun j => (b3 j : Int))
  exact IntegerSubstitution.irreducible m2 72 e3 (fun j => (b3 j : Int)) 72 11 2 (-13)
    (by decide) (by decide) (by decide) (by decide)
    (lcmOfLast 72 e3 rfl (by decide)) core2 inner3


abbrev J4 := Fin 12
abbrev K4 := Sum K3 J4
def e4 (i : Option J4) : Int := i.elim 792 (fun j => #[1, 2, 3, 4, 6, 8, 9, 11, 12, 18, 22, 24][j.val]!)
def b4 (i : Option J4) : Nat := i.elim 13 (fun j => #[13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13][j.val]!)
def r4 (i : Option J4) : Int := i.elim 0 (fun j => #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12][j.val]!)
def m4 : K4 → Int := Sum.elim m3 (fun j => e4 (some j)*b4 (some j))
theorem inner4 (use : Option J4 → Prop) : Covers (fun j => (b4 j : Int)) use ↔ ∀ j,use j :=
  FinitePackets.minimal (none :: (List.finRange 12).map some) completeOption (P:=13) (by decide)
    b4 r4 (by decide) (by decide) (by decide) (by decide) use
theorem core4 (ko : K4 → Prop) (u : Prop) :
    Old m4 10296 ko u ↔ (∀ j,ko j) ∧ u := by
  apply stage m3 e4 (fun j => (b4 j : Int))
  exact IntegerSubstitution.irreducible m3 792 e4 (fun j => (b4 j : Int)) 792 13 12 (-731)
    (by decide) (by decide) (by decide) (by decide)
    (lcmOfLast 792 e4 rfl (by decide)) core3 inner4


def e5 (i : Fin 35) : Int := #[1, 2, 3, 4, 6, 8, 9, 11, 12, 13, 18, 22, 24, 26, 33, 36, 39, 44, 52, 66, 72, 78, 88, 99, 104, 117, 132, 143, 156, 198, 234, 264, 286, 312, 396][i.val]!
theorem lastLcm (z : Int) : (∀ i, e5 i ∣ z) ↔ 10296 ∣ z := by
  constructor
  · intro h
    have h8 : (8:Int) ∣ z := h ⟨5,by decide⟩
    have h9 : (9:Int) ∣ z := h ⟨6,by decide⟩
    have h11 : (11:Int) ∣ z := h ⟨7,by decide⟩
    have h13 : (13:Int) ∣ z := h ⟨9,by decide⟩
    omega
  · intro h i
    have all : ∀ i, e5 i ∣ 10296 := by decide
    exact Int.dvd_trans (all i) h
theorem finalPacket (use : Fin 35 → Prop) :
    Covers (fun _ : Fin 35 => 35) use ↔ ∀ j,use j :=
  FinitePackets.minimal (List.finRange 35) List.mem_finRange (P:=35) (by decide)
    (fun _ => 35) (fun i => (i.val:Int)) (by decide) (by decide) (by decide) (by decide) use
theorem everyDeletion (ko : K4 → Prop) (kn : Fin 35 → Prop) :
    New m4 e5 (fun _ => 35) ko kn ↔ (∀ j,ko j) ∧ (∀ i,kn i) :=
  IntegerSubstitution.irreducible m4 10296 e5 (fun _ => 35) 10296 35 6 (-1765) (by decide)
    (by decide) (by decide) (by decide) lastLcm core4 finalPacket ko kn
abbrev Index64 := Sum K4 (Fin 35)
def m64 : Index64 → Int := Sum.elim m4 (fun j => e5 j*35)
def all0 : List K0 := []

def all1 : List K1 := all0.map Sum.inl ++ (List.finRange _).map Sum.inr
def all2 : List K2 := all1.map Sum.inl ++ (List.finRange _).map Sum.inr
def all3 : List K3 := all2.map Sum.inl ++ (List.finRange _).map Sum.inr
def all4 : List K4 := all3.map Sum.inl ++ (List.finRange _).map Sum.inr
def indices : List Index64 := all4.map Sum.inl ++ (List.finRange _).map Sum.inr
def moduli : List Int := indices.map m64
theorem sizeAndMax : moduli.length=64 ∧ moduli.Nodup ∧ moduli.max? = some 13860 := by decide
#print axioms everyDeletion
#print axioms sizeAndMax
end Checked64

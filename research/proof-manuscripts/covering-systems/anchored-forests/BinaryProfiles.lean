import Std

/-! Each bit of a 16-bit mask is one tuple of four binary digits. -/
namespace BinaryProfiles

set_option maxRecDepth 200000
set_option maxHeartbeats 0

def edges : List (Nat × Nat) := [(0,2),(2,1),(1,3),(3,0),(0,1)]
def table : List (List Nat) := [[64250, 44975, 62965, 24415], [64764, 62451, 53199, 16191], [65484, 52479, 65331, 13311], [65450, 65365, 43775, 22015], [61166, 48059, 56797, 30583]]

theorem tableSemantics : ∀ j : Fin 5, ∀ c : Fin 4, ∀ x : Fin 16,
    (table[j.val]![c.val]!).testBit x.val =
       let e := edges[j.val]!
       decide (2*((x.val/2^e.1)%2) + ((x.val/2^e.2)%2) ≠ c.val) := by decide +kernel

def masks (code : Nat) : List Nat := (List.range 5).map
  (fun j => table[j]![code/4^j%4]!)

def multiple (mask : Nat) : Bool := mask &&& (mask-1) != 0

-- Concrete semantic check of the two-or-more-bits test on the finite profiles
-- is supplied by the independent tuple enumeration in cyclic_check.py.
def valid (code : Nat) : Bool := Id.run do
  let ms := masks code
  let a := ms[0]!
  let b := ms[1]!
  let c := ms[2]!
  let d := ms[3]!
  let e := ms[4]!
  return (a &&& b &&& c &&& d &&& e != 0) &&
    multiple (b &&& c &&& d &&& e) && multiple (a &&& c &&& d &&& e) &&
    multiple (a &&& b &&& d &&& e) && multiple (a &&& b &&& c &&& e) &&
    multiple (a &&& b &&& c &&& d)

theorem allProfiles : ∀ i : Fin 32, ∀ j : Fin 32,
    valid (i.val*32+j.val) = true := by decide +kernel

theorem canonical : ((masks (2+4*2+16*2+64*2+256*3)).foldl (fun a b => a &&& b) 65535) = 1 := by decide +kernel
#print axioms tableSemantics
#print axioms allProfiles
#print axioms canonical
end BinaryProfiles

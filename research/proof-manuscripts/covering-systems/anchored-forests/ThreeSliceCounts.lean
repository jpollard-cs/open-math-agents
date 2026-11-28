/-! AI-authored finite arithmetic certificate for the three-slice rectangle formula.
The simultaneous coordinate-compression argument is in all-divisor-minimum.md. -/
namespace ThreeSliceCounts

structure Widths where
  a : Nat
  b : Nat
  c : Nat
deriving Repr

def triples (bound total : Nat) (sorted : Bool) : List Widths :=
  (List.range (bound+1)).flatMap fun a =>
    (List.range (bound+1)).filterMap fun b =>
      let c := total-a-b
      if a+b+c == total && c ≤ bound && (!sorted || (a ≤ b && b ≤ c)) then
        some ⟨a,b,c⟩
      else none

def uncovered (x y : Widths) (budget : Nat) : Nat :=
  let area := x.a*y.a+x.b*y.b+x.c*y.c
  let allThree := x.a*min y.a (min y.b y.c)
  let pairSum := x.a*min y.a y.b + x.a*min y.a y.c + x.b*min y.b y.c
  let atLeastTwo := pairSum - 2*allThree
  let unionSize := area-atLeastTwo-allThree
  area-min budget unionSize-min budget atLeastTwo-min budget allThree

def optimum (q r pq pr qr : Nat) : Nat :=
  let costs := (triples q (3*q-pq) true).flatMap fun x =>
    (triples r (3*r-pr) false).map fun y => uncovered x y qr
  costs.foldl min (3*q*r)

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem profile : [optimum 5 9 8 8 8, optimum 5 9 8 8 7, optimum 5 9 8 8 6,
    optimum 5 9 7 8 8, optimum 5 9 8 7 8, optimum 5 10 8 8 8,
    optimum 6 9 8 8 8] = [6,8,10,15,10,12,24] := by decide

#print axioms profile
end ThreeSliceCounts

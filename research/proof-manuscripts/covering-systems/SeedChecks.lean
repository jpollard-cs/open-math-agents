import Std

namespace SeedChecks

def s3 : List (Nat × Nat) :=
  [(2,0),(3,0),(8,1),(9,1),(12,11),(16,5),(18,7),(24,5),(36,31),(48,13)]
def s5 : List (Nat × Nat) :=
  [(2,0),(3,0),(5,0),(8,1),(10,1),(12,7),(15,2),(20,3),(24,13),(30,29),(40,13)]

def coversPeriod (n : Nat) (s : List (Nat × Nat)) : Bool :=
  (List.range n).all fun x => s.any fun mr => x % mr.1 == mr.2

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
theorem s3_covers : coversPeriod 144 s3 = true := by decide
theorem s5_covers : coversPeriod 120 s5 = true := by decide

/-- Each job is (odd modulus, binary capacity, number of normalized offsets). -/
def jobs (h period : Nat) : List Nat → List (Nat × Nat × Nat)
  | [] => []
  | m :: ms =>
    let b := Nat.gcd m h
    let t := m / b
    (t, h / b, Nat.gcd t period) :: jobs h (Nat.lcm period t) ms

def failsOnSomeRow (h : Nat) (loads : List Nat) :
    List (Nat × Nat × Nat) → Bool
  | [] => loads.any (· < h)
  | (t, w, num) :: rest =>
    (List.range num).all fun r =>
      let updated := loads.enum.map fun v =>
        if v.1 % t == r then v.2 + w else v.2
      failsOnSomeRow h updated rest

def deletionCheck (h q : Nat) (s : List (Nat × Nat)) : Bool :=
  let ms := s.map Prod.fst
  ms.all fun m => failsOnSomeRow h (List.replicate q 0) (jobs h 1 (ms.erase m))

-- Compiled decision procedures for the two larger, fully specified finite calculations.
theorem s3_deletions : deletionCheck 16 9 s3 = true := by native_decide
theorem s5_deletions : deletionCheck 8 15 s5 = true := by native_decide


/-- Maximum number of outstanding binary slots this job can pay for in one offset. -/
def potential (needs : List Nat) (t w : Nat) : Nat :=
  ((List.range t).map fun r =>
    (needs.enum.map fun v => if v.1 % t == r then min v.2 w else 0).foldl Nat.add 0).foldl max 0

/-- A branch can be discarded if the sum of individual best possible gains
    is below the total deficit. Future allocations only reduce the deficits. -/
def pruned (needs : List Nat) : List (Nat × Nat × Nat) → Bool
  | [] => needs.any (0 < ·)
  | (t,w,num) :: rest =>
    let upper := potential needs t w + (rest.map fun z => potential needs z.1 z.2.1).foldl Nat.add 0
    if upper < needs.foldl Nat.add 0 then true
    else (List.range num).all fun r =>
      let updated := needs.enum.map fun v => if v.1 % t == r then v.2 - w else v.2
      pruned updated rest

def prunedChecks (h q : Nat) (s : List (Nat × Nat)) : Bool :=
  let ms := s.map Prod.fst
  ms.all fun m => pruned (List.replicate q h) (jobs h 1 (ms.erase m))

theorem s3_kernel_deletions : prunedChecks 16 9 s3 = true := by decide
theorem s5_kernel_deletions : prunedChecks 8 15 s5 = true := by decide
#print axioms s3_kernel_deletions
#print axioms s5_kernel_deletions

#print axioms s3_covers
#print axioms s5_covers
#print axioms s3_deletions
#print axioms s5_deletions

end SeedChecks

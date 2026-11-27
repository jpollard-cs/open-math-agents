import Std
namespace DiamondWeights
def vertexMass (p : Nat) (cof : List Nat) : Rat :=
  (cof.map (fun d => (1:Rat)/(p*d : Nat))).sum
def old (p : Nat) : Rat := vertexMass p ((List.range (p-1)).map (·+1))
def takeSmall (p : Nat) : Rat :=
  let ds := ((List.range 50).map (·+1)).filter (fun n =>
    n % 37 != 0 && n % 41 != 0 && n % 43 != 0 && n % 47 != 0)
  vertexMass p (ds.take (p-2))
def gain : Rat :=
  ([37,41,43,47].map takeSmall).sum - ([37,41,43,47].map old).sum +
    (([(37,43),(43,41),(41,47),(47,37),(37,41)] : List (Nat × Nat)).map
      (fun e => (1:Rat)/(e.1*e.2 : Nat))).sum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem exactGain : gain = (931319:Rat)/5803891632 := by decide +kernel
#print axioms exactGain
end DiamondWeights

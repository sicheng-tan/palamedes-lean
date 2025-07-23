import Palamedes.Synthesizer

open Gen CorrectGen

namespace RBTFold

inductive Color where
  | red
  | black
deriving BEq

@[simp]
def rrFold (t : Tree (Color × α)) : Bool :=
  Tree.fold
    (fun bl (c, _) br isRedChild =>
      if c == .red then !isRedChild && bl true && br true else bl false && br false)
    (fun _ => true)
    t
    false

@[simp]
def bhFold (t : Tree (Color × α)) (height : Nat) : Bool :=
  Tree.fold
    (fun bl (c, _) br h =>
      if c == .red then bl h && br h else h > 0 && bl (h - 1) && br (h - 1))
    (fun _ => true)
    t
    height

@[simp]
def isBSTFold (lo hi : Nat) (t : Tree Nat) : Bool :=
  Tree.fold
        (fun bl x br s =>
          match s with
          | (sl, sr) => (decide (sl ≤ x) && decide (x ≤ sr)) && bl (sl, x - 1) && br (x + 1, sr))
        (fun _ => true) t (lo, hi)

@[simp]
def isRBTFold (lo hi height : Nat) (t : Tree (Color × Nat)) : Bool :=
  rrFold t && bhFold t height
  --isBSTFold lo hi t

set_option maxHeartbeats 5000000

def genRBTFold (lo hi height : Nat) : Gen (Tree Nat) := by
  generator_search (fun t => isBSTFold lo hi t = true)

end RBTFold

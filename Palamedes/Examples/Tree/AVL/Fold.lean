import Palamedes.Synthesizer
import Palamedes.Examples.Tree.BST.BST

open Gen CorrectGen

namespace AVLFold

set_option maxHeartbeats 1000000

def genAVL (height lo hi : Nat) : Gen (Tree Nat) := by
  generator_search (fun (t : Tree Nat)=>
    Tree.fold
      (fun bl x br bounds =>
        match bounds with
        | (sl, sr) => decide (sl ≤ x) && decide (x ≤ sr)
          && bl (sl, x - 1) && br (x + 1, sr))
      (fun x => true) t (lo, hi) = true
    ∧
    Tree.fold
      (fun bl x br h => decide (h > 0) && bl (h - 1) && br (h - 1))
      (fun h => decide (h ≤ 1)) t height = true
    ) allow_partial

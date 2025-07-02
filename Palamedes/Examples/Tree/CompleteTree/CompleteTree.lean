import Palamedes.Synthesizer

open Gen CorrectGen

namespace CompleteTree

@[simp]
def isCompleteTree : Tree α → Nat → Bool := fun t n =>
  match t with
  | .leaf => n == 0
  | .node l _ r =>
    n > 0 &&
    isCompleteTree l (n - 1) &&
    isCompleteTree r (n - 1)

def genCompleteTree (n : Nat) : Gen (Tree Nat) := by
  generator_search (fun t => isCompleteTree t n = true)

end CompleteTree

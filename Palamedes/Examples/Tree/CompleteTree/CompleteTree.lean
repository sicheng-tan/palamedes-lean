import Palamedes.Synthesizer

open Gen CorrectGen

namespace Complete

@[simp]
def isComplete : Tree α → Nat → Bool := fun t n =>
  match t with
  | .leaf => n == 0
  | .node l _ r =>
    n > 0 &&
    isComplete l (n - 1) &&
    isComplete r (n - 1)

def genComplete (n : Nat) : Gen (Tree Nat) := by
  generator_search (fun t => isComplete t n = true)

end Complete

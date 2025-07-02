import Palamedes.Synthesizer

open Gen CorrectGen

namespace CompleteTreeFold

@[simp]
def isCompleteTreeFold (n : Nat) (t : Tree Nat) : Bool :=
  Tree.fold (fun bl _ br s => decide (s > 0) && bl (s - 1) && br (s - 1)) (fun s => s == 0) t n

def genCompleteTreeFold (n : Nat) : Gen (Tree Nat) := by
  generator_search (fun t => isCompleteTreeFold n t = true)

end CompleteTreeFold

import Palamedes.Synthesizer

open Gen CorrectGen

namespace IncreasingByOneTreeFold

@[simp]
def increasingByOneTreeFold (t : Tree Nat) : Bool :=
  Tree.fold (fun bl x br prev => x == prev + 1 && bl x && br x) (fun _ => true) t 0

def genIncreasingByOneFold : Gen (Tree Nat) := by
  generator_search (fun t => increasingByOneTreeFold t = true)

end IncreasingByOneTreeFold

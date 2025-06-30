import Palamedes.Synthesizer

open Gen CorrectGen

namespace IncreasingByOneTree

def genIncreasingByOneFold : Gen (Tree Nat) := by
  generator_search (fun t => Tree.fold (fun bl x br prev => x == prev + 1 && bl x && br x) (fun x => true) t 0 = true)

end IncreasingByOneTree

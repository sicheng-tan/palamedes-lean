import Palamedes.Synthesizer

open Gen CorrectGen

namespace AllTwosTreeFold

@[simp]
def allTwosTreeFold (t : Tree Nat) : Bool :=
  Tree.fold (fun bl x br => x == 2 && bl && br) true t

def genAllTwosFold : Gen (Tree Nat) := by
  generator_search (fun t => allTwosTreeFold t = true)

end AllTwosTreeFold

import Palamedes.Synthesizer

open Gen CorrectGen

namespace AllTwosTree

def genAllTwosFold : Gen (Tree Nat) := by
  generator_search (fun t => Tree.fold (fun bl x br => x == 2 && bl && br) true t = true)

end AllTwosTree

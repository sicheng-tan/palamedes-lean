import Palamedes.Synthesizer

open Gen CorrectGen

namespace AllTwosTree

@[simp]
def allTwosTree : Tree Nat → Bool
  | .leaf => true
  | .node l x r => x = 2 && allTwosTree l && allTwosTree r

def genAllTwos : Gen (Tree Nat) := by
  generator_search (fun t => allTwosTree t)

end AllTwosTree

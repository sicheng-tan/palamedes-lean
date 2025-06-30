import Palamedes.Synthesizer

open Gen CorrectGen

namespace AllTwosTree

@[simp]
def allTwos : Tree Nat → Bool
  | .leaf => true
  | .node l x r => x = 2 && allTwos l && allTwos r

def genAllTwos : Gen (Tree Nat) := by
  generator_search (fun t => allTwos t)

end AllTwosTree

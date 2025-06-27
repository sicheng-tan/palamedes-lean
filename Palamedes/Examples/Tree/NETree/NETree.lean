import Palamedes.Synthesizer

open Gen CorrectGen

@[simp]
def recNETree : Tree α → Bool
  | .leaf => false
  | .node l _ r => true && recNETree l && recNETree r

def genNETree : Gen (Tree Nat) := by
  generator_search (fun t => recNETree t = true)

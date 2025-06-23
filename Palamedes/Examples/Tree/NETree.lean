import Palamedes.Synthesizer

open Gen CorrectGen

@[simp]
def size : Tree α → Nat
  | .leaf => 0
  | .node l _ r => 1 + size l + size r

@[simp]
def isNETree (t : Tree α) : Bool :=
  size t == 0

def genNETree : Gen (Tree Nat) := by
  -- generator_search isNETree
  sorry

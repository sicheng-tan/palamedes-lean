import Palamedes.Synthesizer

open Gen CorrectGen

-- @[simp]
-- def recNETree : Tree α → Bool
--   | .leaf => false
--   | .node l _ r => true && recNETree l && recNETree r

-- def genNETreeRec : Gen (Tree Nat) := by
--   generator_search (fun t => recNETree t = true)

@[simp]
def size : Tree α → Nat
  | .leaf => 0
  | .node l _ r => 1 + size l + size r

@[simp]
def isNETree (t : Tree α) : Bool :=
  size t == 0

-- set_option palamedes.debug true

-- def genNETree : Gen (Tree Nat) := by
--   generator_search (fun t => isNETree t)

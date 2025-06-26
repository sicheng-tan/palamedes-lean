import Palamedes.Synthesizer

open Gen CorrectGen

def genNETreeFold : Gen (Tree Nat) := by
  generator_search (fun t => Tree.fold (fun _ _ _ => true) false t)

def recNETree : Tree α → Bool
  | .leaf => false
  | .node l _ r => true && recNETree l && recNETree r

set_option palamedes.debug true

-- def genNETreeRec : Gen (Tree Nat) := by
--   -- generator_search (fun t => recNETree t = true)
--   let cg : CorrectGen (fun t => recNETree t = true) := by
--     apply convert (by
--       funext
--       simp [guard, *]
--       rw [← Tree.fold_accu_Option_basic]
--       ) (Tree.s_unfold _)
--     cgenerator_search
--   let g : Gen (Tree Nat) := by
--     optimize_gen cg.val
--   let _ : support cg.val = support g := by
--     optimality
--   let _ : Gen.total g := by
--     totality
--   exact g

-- @[simp]
-- def size : Tree α → Nat
--   | .leaf => 0
--   | .node l _ r => 1 + size l + size r

-- @[simp]
-- def isNETree (t : Tree α) : Bool :=
--   size t == 0

-- def genNETree : Gen (Tree Nat) := by
--   generator_search isNETree

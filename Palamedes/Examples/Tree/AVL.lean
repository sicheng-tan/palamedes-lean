import Palamedes.Synthesizer
import Palamedes.Examples.Tree.BST.BST

open Gen CorrectGen

def isBalanced : Tree Nat → Nat → Bool := λ t height =>
  match t with
  | .leaf => height <= 1
  | .node l _ r =>
    height > 0 &&
    isBalanced l (height - 1) &&
    isBalanced r (height - 1)


def genAVL (height lo hi : Nat) : Gen (Tree Nat) := by
  --  generator_search (λ t => isBalanced t height ∧ isBST t (lo, hi))
  sorry

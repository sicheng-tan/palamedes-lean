import Palamedes.Synthesizer
import Palamedes.Examples.Tree.BST.BST

open Gen CorrectGen

def isBalanced : Tree Nat → Nat → Bool := fun t height =>
  match t with
  | .leaf => height <= 1
  | .node l _ r =>
    height > 0 &&
    isBalanced l (height - 1) &&
    isBalanced r (height - 1)

set_option palamedes.debug true

def genAVL (height lo hi : Nat) : Gen (Tree Nat) := by
  -- generator_search (fun t => isBalanced t height = true ∧ isBST t (lo, hi) = true)
  let cg : CorrectGen (fun t => isBalanced t height = true ∧ isBST t (lo, hi) = true) := by
    apply convert (by
      funext
      simp [guard, *]
      rw [← Tree.merge_accuM]
      apply and_congr
      . simp_tree_predicate
      . simp_tree_predicate
    ) (Tree.s_unfold _)
    sorry
  let g : Gen (Tree Nat) := by
    optimize_gen cg.val
  -- let _ : support cg.val = support g := by
  --   optimality
  -- let _ : Gen.total g := by
  --   totality
  exact g

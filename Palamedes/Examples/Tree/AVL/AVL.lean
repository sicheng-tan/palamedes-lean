import Palamedes.Synthesizer

open Gen CorrectGen

namespace AVL

@[simp]
def isBST : Tree Nat → (Nat × Nat) → Bool := λ t ⟨lo, hi⟩ =>
  match t with
  | .leaf => true
  | .node l x r =>
    (lo <= x && x <= hi) &&
    isBST l ⟨lo, x - 1⟩ &&
    isBST r ⟨x + 1, hi⟩

@[simp]
def isBalanced : Tree Nat → Nat → Bool := fun t height =>
  match t with
  | .leaf => height <= 1
  | .node l _ r =>
    height > 0 &&
    isBalanced l (height - 1) &&
    isBalanced r (height - 1)

set_option maxHeartbeats 1000000

def genAVL (height lo hi : Nat) : Gen (Tree Nat) := by
  generator_search (fun t => isBST t (lo, hi) = true ∧ isBalanced t height = true) allow_partial

end AVL

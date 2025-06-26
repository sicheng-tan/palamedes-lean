import Palamedes.Synthesizer

open Gen CorrectGen

inductive Color where
  | red
  | black

abbrev RBT α := Tree (Color × α)

def rr_aux : RBT α → Bool → Bool := λ t isRedChild =>
 match t with
 | .leaf => true
 | .node l (.red, _) r => (not isRedChild) && rr_aux l true && rr_aux r true
 | .node l (.black, _) r => rr_aux l false && rr_aux r false

@[simp]
def rr : RBT α → Bool := λ t => rr_aux t false

def bh : RBT α → Nat → Bool := λ t height =>
 match t with
 | .leaf => height == 1
 | .node l (.red, _) r => bh l height && bh r height
 | .node l (.black, _) r =>
    height > 0 &&
    bh l (height - 1) &&
    bh r (height - 1)

def RBT.isBST : Tree (α × Nat) → (Nat × Nat) → Bool := λ t ⟨lo, hi⟩ =>
  match t with
  | .leaf => true
  | .node l (_, x) r =>
    (lo <= x && x <= hi) &&
    RBT.isBST l ⟨lo, x - 1⟩ &&
    RBT.isBST r ⟨x + 1, hi⟩

def genRBT (height lo hi : Nat) : Gen (RBT Nat) := by
  -- generator_search (λ t => rr t ∧ bh t height ∧ RBT.isBST t (lo, hi))
  sorry

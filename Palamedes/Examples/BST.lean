import Palamedes.Synth
import Palamedes.Sample
import Palamedes.Data.Tree
import Mathlib.Tactic.Convert

#set_up_palamedes_simp

def isBST : Tree Nat → (Nat × Nat) → Bool := λ t ⟨lo, hi⟩ =>
  match t with
  | .leaf => true
  | .node l x r =>
    (lo <= x && x <= hi) &&
    isBST l ⟨lo, x - 1⟩ &&
    isBST r ⟨x + 1, hi⟩

def genBST (lo hi : Nat) : CGen (λ v => isBST v ⟨lo, hi⟩) := by
  palamedes

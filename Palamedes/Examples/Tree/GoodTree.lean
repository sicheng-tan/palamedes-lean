import Palamedes.Synthesizer

open Gen CorrectGen

def isGoodTree : Tree α → Nat → Nat → Bool := λ t n1 n2 =>
  match t with
  | .leaf => n1 == n2
  | .node _ _ _ => false

def genGoodTree (n1 n2 : Nat) : Gen (Tree Nat) := by
  -- generator_search (λ (v : Tree Nat) => isGoodTree v n1 n2) allow_partial
  sorry

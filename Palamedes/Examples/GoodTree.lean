import Palamedes.Synth
-- import Palamedes.Sample
import Palamedes.Data.Tree

namespace GoodTree

#set_up_palamedes_simp

@[aesop simp (rule_sets := [palamedes])]
def isGoodTree : Tree α → Nat → Nat → Bool := λ t n1 n2 =>
  match t with
  | .leaf => n1 == n2
  | .node _ _ _ => false

def genCompleteTree (n1 n2 : Nat) [Arbitrary α] : CGen (λ (v : Tree α) => isGoodTree v n1 n2) := by
  -- palamedes
  -- TODO: this will fundamentally be partial.
  sorry

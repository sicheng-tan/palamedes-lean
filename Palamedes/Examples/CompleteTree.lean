import Palamedes.Synth
-- import Palamedes.Sample
import Palamedes.Data.Tree

namespace CompleteTree

#set_up_palamedes_simp

@[aesop simp (rule_sets := [palamedes])]
def isCompleteTree : Tree α → Nat → Bool := λ t n =>
  match t with
  | .leaf => n == 0
  | .node l _ r =>
    n > 0 &&
    isCompleteTree l (n - 1) &&
    isCompleteTree r (n - 1)

def genCompleteTree (n : Nat) [Arbitrary α] : CGen (λ (v : Tree α) => isCompleteTree v n) := by
  palamedes

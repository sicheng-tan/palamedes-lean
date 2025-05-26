import Palamedes.Synth
-- import Palamedes.Sample
import Palamedes.Data.Stack

namespace GoodStack

#set_up_palamedes_simp

def isGoodInt : Int → Bool
  | 0 => true
  | 1 => true
  | _ => false

def isGoodAtom : Atom → Bool
  | .atm z _ => isGoodInt z

@[aesop simp (rule_sets := [palamedes])]
def isGoodStack : Stack → Nat → Bool := λ s n =>
  match s, n with
  | .mty, 0 => true
  | .cons x s, n' + 1 => isGoodAtom x && isGoodStack s n'
  | .ret_cons pc s, n' + 1 => isGoodAtom pc && isGoodStack s n'
  | _, _ => false

def genGoodStack (n : Nat) : CGen (λ (v : Stack) => isGoodStack v n) := by
  -- conv => arg 1; intro v; lhs; apply Stack.coerce_to_fold (by aesop) (by aesop)
  -- palamedes
  sorry

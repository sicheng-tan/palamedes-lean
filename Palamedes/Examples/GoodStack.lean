import Palamedes.Synth
-- import Palamedes.Sample
import Palamedes.Data.Stack

namespace GoodStack

#set_up_palamedes_simp

def isGoodInt : Int -> Bool
  | 0 => true
  | 1 => true
  | _ => false

def isGoodAtom : Atom -> Bool
  | .Atm z _ => isGoodInt z

@[aesop simp (rule_sets := [palamedes])]
def isGoodStack : Nat -> Stack -> Bool
  | 0, .Mty => true
  | n + 1, .Cons x s => isGoodAtom x && isGoodStack n s
  | n + 1, .RetCons pc s => isGoodAtom pc && isGoodStack n s
  | _, _ => false

def genGoodStack (n : Nat) : CGen (λ (v : Stack) => isGoodStack n v) := by
  -- palamedes
  sorry

import Palamedes.Synthesizer

open Gen CorrectGen

def isGoodInt : Int → Bool
  | 0 => true
  | 1 => true
  | _ => false

def isGoodAtom : Atom → Bool
  | .atm z _ => isGoodInt z

def isGoodStack : Stack → Nat → Bool := λ s n =>
  match s, n with
  | .mty, 0 => true
  | .cons x s, n' + 1 => isGoodAtom x && isGoodStack s n'
  | .ret_cons pc s, n' + 1 => isGoodAtom pc && isGoodStack s n'
  | _, _ => false

def genGoodStack (n : Nat) : Gen Stack := by
  -- generator_search (fun s => isGoodStack s n)
  sorry

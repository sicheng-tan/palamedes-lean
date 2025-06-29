import Palamedes.Synthesizer

open Gen CorrectGen

namespace GoodStackFold

@[simp]
def isGoodNat (n : Nat) : Bool :=
  n == 0 || n == 1

@[simp]
def isGoodAtom : Atom → Bool
  | .atm n _ => isGoodNat n

def genGoodStackFold (n : Nat) : Gen Stack := by
  generator_search (λ s => Stack.fold (λ s => s == 0) (λ x acc s => isGoodAtom x && acc (s - 1)) (λ pc acc s => isGoodAtom pc && acc (s - 1)) s n = true)

end GoodStackFold

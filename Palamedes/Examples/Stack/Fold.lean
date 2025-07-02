import Palamedes.Synthesizer

open Gen CorrectGen

namespace GoodStackFold

@[simp]
def isGoodNat (n : Nat) : Bool :=
  n == 0 || n == 1

@[simp]
def isGoodAtom : Atom → Bool
  | .atm n _ => isGoodNat n

def isGoodStackFold (s : Stack) (n : Nat) : Bool :=
  Stack.fold (fun s => s == 0) (fun x acc s => isGoodAtom x && acc (s - 1)) (fun pc acc s => isGoodAtom pc && acc (s - 1)) s n

def genGoodStackFold (n : Nat) : Gen Stack := by
  generator_search (fun s => isGoodStackFold s n = true)

end GoodStackFold

import Palamedes.Synthesizer
import Palamedes.Synthesizer.Util

open Gen CorrectGen

namespace LengthKAllTwosFold

@[simp]
def lengthKAllTwosFold (k : Nat) (xs : List Nat) :=
  List.fold (fun _ b => b + 1) 0 xs = k ∧ List.fold (fun x b => x == 2 && b) true xs

def genLengthKAllTwosFold (k : Nat) : Gen (List Nat) := by
  generator_search (fun xs => lengthKAllTwosFold k xs = true)

end LengthKAllTwosFold

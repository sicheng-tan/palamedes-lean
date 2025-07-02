import Palamedes.Synthesizer

open Gen CorrectGen

namespace AllTwosFold

@[simp]
def allTwosFold (xs : List Nat) : Bool :=
  List.fold (fun x b => x == 2 && b) true xs

def genAllTwosFold : Gen (List Nat) := by
  generator_search (fun xs => allTwosFold xs = true)

end AllTwosFold

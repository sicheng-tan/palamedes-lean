import Palamedes.Synthesizer

open Gen CorrectGen

namespace AllTwosEvenLenFold

@[simp]
def allTwosEvenLenFold (xs : List Nat) : Bool :=
  List.fold (fun x b => x == 2 && b) true xs = true ∧ List.fold (fun _ b => !b) true xs

def genAllTwosEvenLenFold : Gen (List Nat) := by
  generator_search (fun xs => allTwosEvenLenFold xs = true)

end AllTwosEvenLenFold

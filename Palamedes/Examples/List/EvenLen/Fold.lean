import Palamedes.Synthesizer

open Gen CorrectGen

namespace EvenLenFold

def evenLenFold (xs : List α) : Bool :=
  List.fold (fun _ b => !b) true xs

def genEvenLenFold : Gen (List Nat) := by
  generator_search (fun xs => evenLenFold xs = true)

end EvenLenFold

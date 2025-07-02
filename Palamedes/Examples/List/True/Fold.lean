import Palamedes.Synthesizer

open Gen CorrectGen

namespace TrueFold

@[simp]
def trueFold (xs : List Nat) : Bool :=
  List.fold (fun _ b => b) true xs

def genTrueFold : Gen (List Nat) := by
  generator_search (fun xs => trueFold xs = true)

end TrueFold

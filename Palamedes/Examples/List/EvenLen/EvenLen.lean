import Palamedes.Synthesizer

open Gen CorrectGen

namespace EvenLen

@[simp]
def evenLen : List α → Bool
  | [] => true
  | _ :: xs => !(evenLen xs)

def genEvenLen : Gen (List Nat) := by
  generator_search (fun xs => evenLen xs = true)

end EvenLen

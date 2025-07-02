import Palamedes.Synthesizer

open Gen CorrectGen

namespace AllTwosEvenLen

@[simp]
def allTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && allTwos xs

@[simp]
def evenLen : List α → Bool
  | [] => true
  | _ :: xs => !(evenLen xs)

def genAllTwosEvenLen : Gen (List Nat) := by
  generator_search (fun xs => allTwos xs && evenLen xs = true)

end AllTwosEvenLen

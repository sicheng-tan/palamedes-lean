import Palamedes.Synthesizer

open Gen CorrectGen

namespace AllTwos

@[simp]
def allTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && allTwos xs

def genAllTwos : Gen (List Nat) := by
  generator_search (fun xs => allTwos xs)

end AllTwos

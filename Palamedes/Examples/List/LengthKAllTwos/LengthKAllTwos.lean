import Palamedes.Synthesizer

open Gen CorrectGen

namespace LengthKAllTwos

@[simp]
def allTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && allTwos xs

def genLengthKAllTwos (k : Nat): Gen (List Nat) := by
  generator_search (fun xs => (decide (xs.length = k) && allTwos xs) = true)

end LengthKAllTwos

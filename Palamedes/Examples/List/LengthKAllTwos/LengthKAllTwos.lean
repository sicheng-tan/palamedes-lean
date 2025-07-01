import Palamedes.Synthesizer

open Gen CorrectGen

namespace LengthKAllTwos

@[simp]
def recAllTwos : List Nat → Bool
  | [] => true
  | x :: xs => x = 2 && recAllTwos xs

def genLengthKAllTwos (k : Nat): Gen (List Nat) := by
  generator_search (fun xs => (decide (xs.length = k) && recAllTwos xs) = true)

end LengthKAllTwos

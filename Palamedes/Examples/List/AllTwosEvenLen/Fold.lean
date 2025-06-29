import Palamedes.Synthesizer

open Gen CorrectGen

def genAllTwosEvenLenFold : Gen (List Nat) := by
  generator_search (fun xs => List.fold (fun x b => x == 2 && b) true xs = true ∧ List.fold (fun x b => !b) true xs = true)

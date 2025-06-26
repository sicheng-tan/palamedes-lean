import Palamedes.Synthesizer

open Gen CorrectGen

def genEvenLenFold : Gen (List Nat) := by
  generator_search (fun xs => List.fold (fun x b => !b) true xs = true)

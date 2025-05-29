import Palamedes.V2.Synthesizer

open Gen CorrectGen

def genAllTwosFold : Gen (List Nat) := by
  generator_search (fun xs => List.fold (fun x b => x == 2 && b) true xs = true)

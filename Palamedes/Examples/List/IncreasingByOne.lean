import Palamedes.Synthesizer

open Gen CorrectGen

def genIncreasingByOneFold : Gen (List Nat) := by
  generator_search (fun xs => List.fold (fun x b prev => x == prev + 1 && b x) (fun x => true) xs 0 = true)
